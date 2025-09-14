
#include <minix/com.h>
#include <minix/callnr.h>
#include <minix/type.h>
#include <minix/config.h>
#include <minix/const.h>
#include <minix/sysutil.h>
#include <minix/syslib.h>
#include <minix/debug.h>
#include <minix/bitmap.h>
#include <minix/hash.h>
#include <machine/multiboot.h>

#include <sys/mman.h>

#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>
#include <sys/param.h>

#include "vm.h"
#include "proto.h"
#include "util.h"
#include "glo.h"
#include "region.h"
#include "sanitycheck.h"
#include "memlist.h"
#include "memtype.h"
#include "regionavl.h"

static struct vir_region *map_copy_region(struct vmproc *vmp, struct
	vir_region *vr);

void map_region_init(void)
{
    return;
}

static void map_printregion(struct vir_region *vr)
{
    unsigned int i;
    struct phys_region *ph;
    
    if (!vr || !vr->def_memtype) {
        printf("map_printmap: invalid region\n");
        return;
    }
    
    printf("map_printmap: map_name: %s\n", vr->def_memtype->name);
    printf("\t%lx (len 0x%lx, %lukB), %s, %s\n",
           vr->vaddr, vr->length, vr->length/1024,
           vr->def_memtype->name,
           (vr->flags & VR_WRITABLE) ? "writable" : "readonly");
    printf("\t\tphysblocks:\n");
    
    if (!vr->physblocks) {
        printf("\t\t(no physblocks)\n");
        return;
    }
    
    unsigned int page_count = vr->length / VM_PAGE_SIZE;
    for (i = 0; i < page_count; i++) {
        ph = vr->physblocks[i];
        if (!ph || !ph->ph) {
            continue;
        }
        
        printf("\t\t@ %lx (refs %d): phys 0x%lx, %s\n",
               (vr->vaddr + ph->offset),
               ph->ph->refcount, ph->ph->phys,
               pt_writable(vr->parent, vr->vaddr + ph->offset) ? "W" : "R");
    }
}

struct phys_region *physblock_get(struct vir_region *region, vir_bytes offset)
{
	struct phys_region *foundregion;
	int i;
	
	if (!region) {
		return NULL;
	}
	
	if (offset % VM_PAGE_SIZE != 0) {
		return NULL;
	}
	
	if (offset >= region->length) {
		return NULL;
	}
	
	i = offset / VM_PAGE_SIZE;
	
	if (i < 0 || !region->physblocks) {
		return NULL;
	}
	
	foundregion = region->physblocks[i];
	
	if (foundregion && foundregion->offset != offset) {
		return NULL;
	}
	
	return foundregion;
}

void physblock_set(struct vir_region *region, vir_bytes offset,
	struct phys_region *newphysr)
{
	int page_index;
	struct vmproc *proc;
	
	if (!region) return;
	
	assert(!(offset % VM_PAGE_SIZE));
	assert(offset < region->length);
	
	page_index = offset / VM_PAGE_SIZE;
	proc = region->parent;
	
	if (!proc) return;
	
	if (newphysr) {
		assert(!region->physblocks[page_index]);
		assert(newphysr->offset == offset);
		proc->vm_total += VM_PAGE_SIZE;
		if (proc->vm_total > proc->vm_total_max)
			proc->vm_total_max = proc->vm_total;
	} else {
		assert(region->physblocks[page_index]);
		proc->vm_total -= VM_PAGE_SIZE;
	}
	
	region->physblocks[page_index] = newphysr;
}

/*===========================================================================*
 *				map_printmap				     *
 *===========================================================================*/
void map_printmap(struct vmproc *vmp)
{
	struct vir_region *vr;
	region_iter iter;

	if (!vmp) {
		return;
	}

	printf("memory regions in process %d:\n", vmp->vm_endpoint);

	region_start_iter_least(&vmp->vm_regions_avl, &iter);
	while ((vr = region_get_iter(&iter)) != NULL) {
		map_printregion(vr);
		region_incr_iter(&iter);
	}
}

static struct vir_region *getnextvr(struct vir_region *vr)
{
	struct vir_region *nextvr;
	region_iter v_iter;
	
	if (!vr) return NULL;
	
	SLABSANE(vr);
	
	region_start_iter(&vr->parent->vm_regions_avl, &v_iter, vr->vaddr, AVL_EQUAL);
	
	if (!region_get_iter(&v_iter)) return NULL;
	if (region_get_iter(&v_iter) != vr) return NULL;
	
	region_incr_iter(&v_iter);
	nextvr = region_get_iter(&v_iter);
	
	if (!nextvr) return NULL;
	
	SLABSANE(nextvr);
	
	if (vr->parent != nextvr->parent) return NULL;
	if (vr->vaddr >= nextvr->vaddr) return NULL;
	if (vr->vaddr + vr->length > nextvr->vaddr) return NULL;
	
	return nextvr;
}

static int pr_writable(struct vir_region *vr, struct phys_region *pr)
{
	if (!vr || !pr || !pr->memtype) {
		return 0;
	}
	
	if (!pr->memtype->writable) {
		return 0;
	}
	
	return ((vr->flags & VR_WRITABLE) && pr->memtype->writable(pr));
}

#if SANITYCHECKS

/*===========================================================================*
 *				map_sanitycheck_pt			     *
 *===========================================================================*/
static int map_sanitycheck_pt(struct vmproc *vmp,
	struct vir_region *vr, struct phys_region *pr)
{
	struct phys_block *pb = pr->ph;
	int rw;
	int r;

	if(pr_writable(vr, pr))
		rw = PTF_WRITE;
	else
		rw = PTF_READ;

	r = pt_writemap(vmp, &vmp->vm_pt, vr->vaddr + pr->offset,
	  pb->phys, VM_PAGE_SIZE, PTF_PRESENT | PTF_USER | rw, WMF_VERIFY);

	if(r != OK) {
		printf("proc %d phys_region 0x%lx sanity check failed\n",
			vmp->vm_endpoint, pr->offset);
		map_printregion(vr);
	}

	return r;
}

/*===========================================================================*
 *				map_sanitycheck			     *
 *===========================================================================*/
void map_sanitycheck(const char *file, int line)
{
	struct vmproc *vmp;

/* Macro for looping over all physical blocks of all regions of
 * all processes.
 */
#define ALLREGIONS(regioncode, physcode)			\
	for(vmp = vmproc; vmp < &vmproc[VMP_NR]; vmp++) {	\
		vir_bytes voffset;				\
		region_iter v_iter;				\
		struct vir_region *vr;				\
		if(!(vmp->vm_flags & VMF_INUSE))		\
			continue;				\
		region_start_iter_least(&vmp->vm_regions_avl, &v_iter);	\
		while((vr = region_get_iter(&v_iter))) {	\
			struct phys_region *pr;			\
			regioncode;				\
			for(voffset = 0; voffset < vr->length; \
				voffset += VM_PAGE_SIZE) {	\
				if(!(pr = physblock_get(vr, voffset))) 	\
					continue;	\
				physcode;			\
			}					\
			region_incr_iter(&v_iter);		\
		}						\
	}

#define MYSLABSANE(s) MYASSERT(slabsane_f(__FILE__, __LINE__, s, sizeof(*(s))))
	/* Basic pointers check. */
	ALLREGIONS(MYSLABSANE(vr),MYSLABSANE(pr); MYSLABSANE(pr->ph);MYSLABSANE(pr->parent));
	ALLREGIONS(/* MYASSERT(vr->parent == vmp) */,MYASSERT(pr->parent == vr););

	/* Do counting for consistency check. */
	ALLREGIONS(;,USE(pr->ph, pr->ph->seencount = 0;););
	ALLREGIONS(;,MYASSERT(pr->offset == voffset););
	ALLREGIONS(;,USE(pr->ph, pr->ph->seencount++;);
		if(pr->ph->seencount == 1) {
			if(pr->memtype->ev_sanitycheck)
				pr->memtype->ev_sanitycheck(pr, file, line);
		}
	);

	/* Do consistency check. */
	ALLREGIONS({ struct vir_region *nextvr = getnextvr(vr);
		if(nextvr) {
			MYASSERT(vr->vaddr < nextvr->vaddr);
			MYASSERT(vr->vaddr + vr->length <= nextvr->vaddr);
		}
		}
		MYASSERT(!(vr->vaddr % VM_PAGE_SIZE));,	
		if(pr->ph->flags & PBF_INCACHE) pr->ph->seencount++;
		if(pr->ph->refcount != pr->ph->seencount) {
			map_printmap(vmp);
			printf("ph in vr %p: 0x%lx  refcount %u "
				"but seencount %u\n", 
				vr, pr->offset,
				pr->ph->refcount, pr->ph->seencount);
		}
		{
			int n_others = 0;
			struct phys_region *others;
			if(pr->ph->refcount > 0) {
				MYASSERT(pr->ph->firstregion);
				if(pr->ph->refcount == 1) {
					MYASSERT(pr->ph->firstregion == pr);
				}
			} else {
				MYASSERT(!pr->ph->firstregion);
			}
			for(others = pr->ph->firstregion; others;
				others = others->next_ph_list) {
				MYSLABSANE(others);
				MYASSERT(others->ph == pr->ph);
				n_others++;
			}
			if(pr->ph->flags & PBF_INCACHE) n_others++;
			MYASSERT(pr->ph->refcount == n_others);
		}
		MYASSERT(pr->ph->refcount == pr->ph->seencount);
		MYASSERT(!(pr->offset % VM_PAGE_SIZE)););
	ALLREGIONS(,MYASSERT(map_sanitycheck_pt(vmp, vr, pr) == OK));
}

#endif

/*=========================================================================*
 *				map_ph_writept				*
 *=========================================================================*/
int map_ph_writept(struct vmproc *vmp, struct vir_region *vr,
	struct phys_region *pr)
{
	int flags = PTF_PRESENT | PTF_USER;
	struct phys_block *pb;
	int write_flags;

	if (!vmp || !vr || !pr) {
		return EINVAL;
	}

	pb = pr->ph;
	if (!pb) {
		return EINVAL;
	}

	if ((vr->vaddr % VM_PAGE_SIZE) != 0 || 
	    (pr->offset % VM_PAGE_SIZE) != 0 || 
	    pb->refcount <= 0) {
		return EINVAL;
	}

	flags |= pr_writable(vr, pr) ? PTF_WRITE : PTF_READ;

	if (vr->def_memtype && vr->def_memtype->pt_flags) {
		flags |= vr->def_memtype->pt_flags(vr);
	}

#if SANITYCHECKS
	write_flags = pr->written ? WMF_OVERWRITE : 0;
#else
	write_flags = WMF_OVERWRITE;
#endif

	if (pt_writemap(vmp, &vmp->vm_pt, vr->vaddr + pr->offset,
			pb->phys, VM_PAGE_SIZE, flags, write_flags) != OK) {
		printf("VM: map_writept: pt_writemap failed\n");
		return ENOMEM;
	}

#if SANITYCHECKS
	pr->written = 1;
#endif

	return OK;
}

#define SLOT_FAIL ((vir_bytes) -1)

/*===========================================================================*
 *				region_find_slot_range			     *
 *===========================================================================*/
static vir_bytes region_find_slot_range(struct vmproc *vmp,
		vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
	struct vir_region *lastregion;
	vir_bytes startv = 0;
	int foundflag = 0;
	region_iter iter;

	SANITYCHECK(SCL_FUNCTIONS);

	if (length == 0) {
		return SLOT_FAIL;
	}

	if (maxv == 0) {
		maxv = minv + length;
		if (maxv <= minv) {
			printf("region_find_slot: minv 0x%lx and bytes 0x%lx\n",
				minv, length);
			return SLOT_FAIL;
		}
	}

	if ((length % VM_PAGE_SIZE) != 0) {
		return SLOT_FAIL;
	}

	if (minv >= maxv) {
		printf("VM: 1 minv: 0x%lx maxv: 0x%lx length: 0x%lx\n",
			minv, maxv, length);
		return SLOT_FAIL;
	}

	if (minv + length > maxv) {
		return SLOT_FAIL;
	}

	region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_GREATER_EQUAL);
	lastregion = region_get_iter(&iter);

	if (!lastregion) {
		vir_bytes range_start, range_end;
		region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_LESS);
		lastregion = region_get_iter(&iter);
		
		range_start = lastregion ? lastregion->vaddr + lastregion->length : 0;
		range_end = VM_DATATOP;
		
		range_start = (range_start > minv) ? range_start : minv;
		range_end = (range_end < maxv) ? range_end : maxv;
		
		if (range_end > range_start && (range_end - range_start) >= length) {
			startv = range_end - length;
			foundflag = 1;
		}
	}

	if (!foundflag) {
		struct vir_region *vr;
		while ((vr = region_get_iter(&iter)) && !foundflag) {
			struct vir_region *nextvr;
			vir_bytes range_start, range_end;
			
			region_decr_iter(&iter);
			nextvr = region_get_iter(&iter);
			
			range_start = nextvr ? nextvr->vaddr + nextvr->length : 0;
			range_end = vr->vaddr;
			
			if (range_start + VM_PAGE_SIZE < range_end - VM_PAGE_SIZE) {
				range_start += VM_PAGE_SIZE;
				range_end -= VM_PAGE_SIZE;
			}
			
			range_start = (range_start > minv) ? range_start : minv;
			range_end = (range_end < maxv) ? range_end : maxv;
			
			if (range_end > range_start && (range_end - range_start) >= length) {
				startv = range_end - length;
				foundflag = 1;
			}
		}
	}

	if (!foundflag) {
		return SLOT_FAIL;
	}

	if (startv < minv || startv >= maxv || startv + length > maxv) {
		return SLOT_FAIL;
	}

	vmp->vm_region_top = startv + length;

	return startv;
}

/*===========================================================================*
 *				region_find_slot			     *
 *===========================================================================*/
static vir_bytes region_find_slot(struct vmproc *vmp,
		vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
	vir_bytes v;
	vir_bytes hint;

	if (!vmp || !length) {
		return SLOT_FAIL;
	}

	hint = vmp->vm_region_top;

	if (maxv != 0 && hint < maxv && hint >= minv) {
		v = region_find_slot_range(vmp, minv, hint, length);
		if (v != SLOT_FAIL) {
			return v;
		}
	}

	return region_find_slot_range(vmp, minv, maxv, length);
}

static unsigned int phys_slot(vir_bytes len)
{
	if (len % VM_PAGE_SIZE != 0) {
		return 0;
	}
	return len / VM_PAGE_SIZE;
}

static struct vir_region *region_new(struct vmproc *vmp, vir_bytes startv, vir_bytes length,
	int flags, mem_type_t *memtype)
{
	struct vir_region *newregion;
	struct phys_region **newphysregions;
	static u32_t id;
	int slots;

	if (vmp == NULL || memtype == NULL || length == 0) {
		return NULL;
	}

	slots = phys_slot(length);
	if (slots <= 0) {
		return NULL;
	}

	if (!(SLABALLOC(newregion))) {
		printf("vm: region_new: could not allocate\n");
		return NULL;
	}

	memset(newregion, 0, sizeof(*newregion));
	newregion->vaddr = startv;
	newregion->length = length;
	newregion->flags = flags;
	newregion->def_memtype = memtype;
	newregion->remaps = 0;
	newregion->id = id++;
	newregion->lower = NULL;
	newregion->higher = NULL;
	newregion->parent = vmp;

	newphysregions = calloc(slots, sizeof(struct phys_region *));
	if (newphysregions == NULL) {
		printf("VM: region_new: allocating phys blocks failed\n");
		SLABFREE(newregion);
		return NULL;
	}

	newregion->physblocks = newphysregions;

	return newregion;
}

/*===========================================================================*
 *				map_page_region				     *
 *===========================================================================*/
struct vir_region *map_page_region(struct vmproc *vmp, vir_bytes minv,
	vir_bytes maxv, vir_bytes length, u32_t flags, int mapflags,
	mem_type_t *memtype)
{
	struct vir_region *newregion;
	vir_bytes startv;

	if (!vmp || !memtype || (length % VM_PAGE_SIZE) != 0) {
		return NULL;
	}

	SANITYCHECK(SCL_FUNCTIONS);

	startv = region_find_slot(vmp, minv, maxv, length);
	if (startv == SLOT_FAIL) {
		return NULL;
	}

	newregion = region_new(vmp, startv, length, flags, memtype);
	if (!newregion) {
		printf("VM: map_page_region: allocating region failed\n");
		return NULL;
	}

	if (newregion->def_memtype && newregion->def_memtype->ev_new) {
		if (newregion->def_memtype->ev_new(newregion) != OK) {
			return NULL;
		}
	}

	if (mapflags & MF_PREALLOC) {
		if (map_handle_memory(vmp, newregion, 0, length, 1, NULL, 0, 0) != OK) {
			printf("VM: map_page_region: prealloc failed\n");
			map_free(newregion);
			return NULL;
		}
	}

	USE(newregion, newregion->flags &= ~VR_UNINITIALIZED;);

	region_insert(&vmp->vm_regions_avl, newregion);

#if SANITYCHECKS
	if (startv != newregion->vaddr) {
		printf("VM: map_page_region: address mismatch\n");
		return NULL;
	}
	{
		struct vir_region *nextvr = getnextvr(newregion);
		if (nextvr && newregion->vaddr >= nextvr->vaddr) {
			printf("VM: map_page_region: region ordering violated\n");
			return NULL;
		}
	}
#endif

	SANITYCHECK(SCL_FUNCTIONS);

	return newregion;
}

/*===========================================================================*
 *				map_subfree				     *
 *===========================================================================*/
static int map_subfree(struct vir_region *region, 
	vir_bytes start, vir_bytes len)
{
	struct phys_region *pr;
	vir_bytes end;
	vir_bytes voffset;

	if (!region || len == 0) {
		return EINVAL;
	}

	if (start > region->length || len > region->length - start) {
		return EINVAL;
	}

	end = start + len;

#if SANITYCHECKS
	SLABSANE(region);
	for(voffset = 0; voffset < phys_slot(region->length);
		voffset += VM_PAGE_SIZE) {
		struct phys_region *others;
		struct phys_block *pb;

		pr = physblock_get(region, voffset);
		if(!pr)
			continue;

		pb = pr->ph;
		if (!pb) {
			continue;
		}

		for(others = pb->firstregion; others;
			others = others->next_ph_list) {
			assert(others->ph == pb);
		}
	}
#endif

	for(voffset = start; voffset < end; voffset += VM_PAGE_SIZE) {
		pr = physblock_get(region, voffset);
		if(!pr)
			continue;
		
		if (pr->offset < start || pr->offset >= end) {
			continue;
		}
		
		pb_unreferenced(region, pr, 1);
		SLABFREE(pr);
	}

	return OK;
}

/*===========================================================================*
 *				map_free				     *
 *===========================================================================*/
int map_free(struct vir_region *region)
{
	int r;

	if (!region) {
		return -1;
	}

	r = map_subfree(region, 0, region->length);
	if (r != OK) {
		return r;
	}

	if (region->def_memtype && region->def_memtype->ev_delete) {
		region->def_memtype->ev_delete(region);
	}

	free(region->physblocks);
	region->physblocks = NULL;
	SLABFREE(region);

	return OK;
}

/*========================================================================*
 *				map_free_proc				  *
 *========================================================================*/
int map_free_proc(struct vmproc *vmp)
{
	struct vir_region *r;

	if (!vmp) {
		return -1;
	}

	while ((r = region_search_root(&vmp->vm_regions_avl)) != NULL) {
		SANITYCHECK(SCL_DETAIL);
#if SANITYCHECKS
		nocheck++;
#endif
		if (region_remove(&vmp->vm_regions_avl, r->vaddr) != OK) {
#if SANITYCHECKS
			nocheck--;
#endif
			return -1;
		}
		
		if (map_free(r) != OK) {
#if SANITYCHECKS
			nocheck--;
#endif
			return -1;
		}
#if SANITYCHECKS
		nocheck--;
#endif
		SANITYCHECK(SCL_DETAIL);
	}

	region_init(&vmp->vm_regions_avl);

	SANITYCHECK(SCL_FUNCTIONS);

	return OK;
}

/*===========================================================================*
 *				map_lookup				     *
 *===========================================================================*/
struct vir_region *map_lookup(struct vmproc *vmp,
	vir_bytes offset, struct phys_region **physr)
{
	struct vir_region *r;

	if (!vmp) {
		return NULL;
	}

	SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
	if(!region_search_root(&vmp->vm_regions_avl))
		panic("process has no regions: %d", vmp->vm_endpoint);
#endif

	r = region_search(&vmp->vm_regions_avl, offset, AVL_LESS_EQUAL);
	if (!r) {
		SANITYCHECK(SCL_FUNCTIONS);
		return NULL;
	}

	if (offset < r->vaddr || offset >= r->vaddr + r->length) {
		SANITYCHECK(SCL_FUNCTIONS);
		return NULL;
	}

	if (physr) {
		vir_bytes ph = offset - r->vaddr;
		*physr = physblock_get(r, ph);
		if (*physr && (*physr)->offset != ph) {
			assert(0);
		}
	}

	SANITYCHECK(SCL_FUNCTIONS);
	return r;
}

u32_t vrallocflags(u32_t flags)
{
	u32_t allocflags = 0;

	if (flags & VR_PHYS64K)
		allocflags |= PAF_ALIGN64K;
	if (flags & VR_LOWER16MB)
		allocflags |= PAF_LOWER16MB;
	if (flags & VR_LOWER1MB)
		allocflags |= PAF_LOWER1MB;
	if (!(flags & VR_UNINITIALIZED))
		allocflags |= PAF_CLEAR;

	return allocflags;
}

/*===========================================================================*
 *				map_pf			     *
 *===========================================================================*/
int map_pf(struct vmproc *vmp,
	struct vir_region *region,
	vir_bytes offset,
	int write,
	vfs_callback_t pf_callback,
	void *state,
	int len,
	int *io)
{
	struct phys_region *ph;
	int r;

	if (!vmp || !region || !io) {
		return EINVAL;
	}

	offset -= offset % VM_PAGE_SIZE;

	if (offset >= region->length) {
		return EINVAL;
	}

	if ((region->vaddr % VM_PAGE_SIZE) != 0) {
		return EINVAL;
	}

	if (write && !(region->flags & VR_WRITABLE)) {
		return EACCES;
	}

	SANITYCHECK(SCL_FUNCTIONS);

	ph = physblock_get(region, offset);
	if (!ph) {
		r = create_new_phys_region(region, offset, &ph);
		if (r != OK) {
			return r;
		}
	}

	if (!ph || !ph->ph || !ph->memtype) {
		return EINVAL;
	}

	if (!ph->memtype->writable) {
		return EINVAL;
	}

	if (write && ph->memtype->writable(ph)) {
		return handle_page_fault(vmp, region, ph, write, pf_callback, state, len, io);
	}

	if (ph->ph->phys == MAP_NONE) {
		return EINVAL;
	}

	r = map_ph_writept(vmp, region, ph);
	if (r != OK) {
		printf("map_pf: writept failed\n");
		return r;
	}

	SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
	if (pt_checkrange(&vmp->vm_pt, region->vaddr + offset, VM_PAGE_SIZE, write) != OK) {
		panic("map_pf: pt_checkrange failed: %d", r);
	}
#endif

	return OK;
}

static int create_new_phys_region(struct vir_region *region, vir_bytes offset, struct phys_region **ph_out)
{
	struct phys_block *pb;
	struct phys_region *ph;

	if (!region || !ph_out) {
		return EINVAL;
	}

	pb = pb_new(MAP_NONE);
	if (!pb) {
		printf("map_pf: pb_new failed\n");
		return ENOMEM;
	}

	ph = pb_reference(pb, offset, region, region->def_memtype);
	if (!ph) {
		printf("map_pf: pb_reference failed\n");
		pb_free(pb);
		return ENOMEM;
	}

	*ph_out = ph;
	return OK;
}

static int handle_page_fault(struct vmproc *vmp, struct vir_region *region, struct phys_region *ph, 
	int write, vfs_callback_t pf_callback, void *state, int len, int *io)
{
	int r;

	if (!ph->memtype->ev_pagefault) {
		return EINVAL;
	}

	r = ph->memtype->ev_pagefault(vmp, region, ph, write, pf_callback, state, len, io);
	if (r == SUSPEND) {
		return SUSPEND;
	}

	if (r != OK) {
		if (ph) {
			pb_unreferenced(region, ph, 1);
		}
		return r;
	}

	if (!ph || !ph->ph || ph->ph->phys == MAP_NONE) {
		return EINVAL;
	}

	return OK;
}

int map_handle_memory(struct vmproc *vmp,
	struct vir_region *region, vir_bytes start_offset, vir_bytes length,
	int write, vfs_callback_t cb, void *state, int statelen)
{
	vir_bytes offset, lim;
	int r;
	int io = 0;

	if (!vmp || !region || length == 0) {
		return EINVAL;
	}

	if (start_offset > VADDR_MAX - length) {
		return EINVAL;
	}

	lim = start_offset + length;

	for (offset = start_offset; offset < lim; offset += VM_PAGE_SIZE) {
		r = map_pf(vmp, region, offset, write, cb, state, statelen, &io);
		if (r != OK) {
			return r;
		}
	}

	return OK;
}

/*===========================================================================*
 *				map_pin_memory      			     *
 *===========================================================================*/
int map_pin_memory(struct vmproc *vmp)
{
    struct vir_region *vr;
    int r;
    region_iter iter;
    
    if (!vmp) {
        return EINVAL;
    }
    
    pt_assert(&vmp->vm_pt);
    region_start_iter_least(&vmp->vm_regions_avl, &iter);
    
    while ((vr = region_get_iter(&iter))) {
        r = map_handle_memory(vmp, vr, 0, vr->length, 1, NULL, 0, 0);
        if (r != OK) {
            panic("map_pin_memory: map_handle_memory failed: %d", r);
        }
        region_incr_iter(&iter);
    }
    
    pt_assert(&vmp->vm_pt);
    return OK;
}

/*===========================================================================*
 *				map_copy_region			     	*
 *===========================================================================*/
struct vir_region *map_copy_region(struct vmproc *vmp, struct vir_region *vr)
{
    struct vir_region *newvr;
    struct phys_region *ph;
    int r;
    vir_bytes p;

    if (!vmp || !vr) {
        return NULL;
    }

    newvr = region_new(vr->parent, vr->vaddr, vr->length, vr->flags, vr->def_memtype);
    if (!newvr) {
        return NULL;
    }

    USE(newvr, newvr->parent = vmp;);

    if (vr->def_memtype->ev_copy) {
        r = vr->def_memtype->ev_copy(vr, newvr);
        if (r != OK) {
            map_free(newvr);
            printf("VM: memtype-specific copy failed (%d)\n", r);
            return NULL;
        }
    }

    for (p = 0; p < phys_slot(vr->length); p++) {
        struct phys_region *newph;

        ph = physblock_get(vr, p * VM_PAGE_SIZE);
        if (!ph) {
            continue;
        }

        newph = pb_reference(ph->ph, ph->offset, newvr, vr->def_memtype);
        if (!newph) {
            map_free(newvr);
            return NULL;
        }

        if (ph->memtype->ev_reference) {
            ph->memtype->ev_reference(ph, newph);
        }

#if SANITYCHECKS
        USE(newph, newph->written = 0;);
#endif
    }

    return newvr;
}

/*===========================================================================*
 *				copy_abs2region			     	*
 *===========================================================================*/
int copy_abs2region(phys_bytes absaddr, struct vir_region *destregion,
	phys_bytes offset, phys_bytes len)
{
	if (!destregion || !destregion->physblocks) {
		printf("VM: copy_abs2region: invalid destination region.\n");
		return EFAULT;
	}

	while (len > 0) {
		struct phys_region *ph = physblock_get(destregion, offset);
		if (!ph) {
			printf("VM: copy_abs2region: no phys region found.\n");
			return EFAULT;
		}

		if (ph->offset > offset || ph->offset + VM_PAGE_SIZE <= offset) {
			printf("VM: copy_abs2region: invalid phys region bounds.\n");
			return EFAULT;
		}

		if (ph->ph->refcount != 1) {
			printf("VM: copy_abs2region: refcount not 1.\n");
			return EFAULT;
		}

		phys_bytes suboffset = offset - ph->offset;
		phys_bytes sublen = len;
		phys_bytes remaining_page = VM_PAGE_SIZE - suboffset;
		
		if (sublen > remaining_page) {
			sublen = remaining_page;
		}

		if (sys_abscopy(absaddr, ph->ph->phys + suboffset, sublen) != OK) {
			printf("VM: copy_abs2region: abscopy failed.\n");
			return EFAULT;
		}

		absaddr += sublen;
		offset += sublen;
		len -= sublen;
	}

	return OK;
}

/*=========================================================================*
 *				map_writept				*
 *=========================================================================*/
int map_writept(struct vmproc *vmp)
{
	struct vir_region *vr;
	struct phys_region *ph;
	int r;
	region_iter v_iter;
	vir_bytes p;

	if (!vmp) {
		return EINVAL;
	}

	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while ((vr = region_get_iter(&v_iter))) {
		for (p = 0; p < vr->length; p += VM_PAGE_SIZE) {
			ph = physblock_get(vr, p);
			if (!ph) {
				continue;
			}

			r = map_ph_writept(vmp, vr, ph);
			if (r != OK) {
				printf("VM: map_writept: failed\n");
				return r;
			}
		}
		region_incr_iter(&v_iter);
	}

	return OK;
}

/*========================================================================*
 *			       map_proc_copy			     	  *
 *========================================================================*/
int map_proc_copy(struct vmproc *dst, struct vmproc *src)
{
    if (!dst || !src) {
        return -1;
    }
    
    region_init(&dst->vm_regions_avl);
    return map_proc_copy_range(dst, src, NULL, NULL);
}

/*========================================================================*
 *			     map_proc_copy_range			     	  *
 *========================================================================*/
int map_proc_copy_range(struct vmproc *dst, struct vmproc *src,
    struct vir_region *start_src_vr, struct vir_region *end_src_vr)
{
    struct vir_region *vr;
    region_iter v_iter;

    if (!dst || !src) {
        return EINVAL;
    }

    if (!start_src_vr) {
        start_src_vr = region_search_least(&src->vm_regions_avl);
    }
    if (!end_src_vr) {
        end_src_vr = region_search_greatest(&src->vm_regions_avl);
    }

    if (!start_src_vr || !end_src_vr) {
        return EINVAL;
    }

    if (start_src_vr->parent != src) {
        return EINVAL;
    }

    region_start_iter(&src->vm_regions_avl, &v_iter, start_src_vr->vaddr, AVL_EQUAL);
    
    if (region_get_iter(&v_iter) != start_src_vr) {
        return EINVAL;
    }

    while ((vr = region_get_iter(&v_iter))) {
        struct vir_region *newvr = map_copy_region(dst, vr);
        if (!newvr) {
            map_free_proc(dst);
            return ENOMEM;
        }
        region_insert(&dst->vm_regions_avl, newvr);

        if (vr == end_src_vr) {
            break;
        }
        region_incr_iter(&v_iter);
    }

    map_writept(src);
    map_writept(dst);

    return OK;
}

int map_region_extend_upto_v(struct vmproc *vmp, vir_bytes v)
{
    vir_bytes offset, limit, extralen;
    struct vir_region *vr, *nextvr;
    struct phys_region **newpr;
    int newslots, prevslots, addedslots, r;

    if (!vmp) {
        return ENOMEM;
    }

    offset = roundup(v, VM_PAGE_SIZE);

    vr = region_search(&vmp->vm_regions_avl, offset, AVL_LESS);
    if (!vr) {
        printf("VM: nothing to extend\n");
        return ENOMEM;
    }

    if (vr->vaddr + vr->length >= v) {
        return OK;
    }

    limit = vr->vaddr + vr->length;
    
    if (vr->vaddr > offset) {
        return ENOMEM;
    }

    newslots = phys_slot(offset - vr->vaddr);
    prevslots = phys_slot(vr->length);
    
    if (newslots < prevslots) {
        return ENOMEM;
    }

    addedslots = newslots - prevslots;
    extralen = offset - limit;
    
    if (extralen == 0) {
        return OK;
    }

    nextvr = getnextvr(vr);
    if (nextvr) {
        if (offset > nextvr->vaddr || nextvr->vaddr < offset) {
            printf("VM: can't grow into next region\n");
            return ENOMEM;
        }
    }

    if (!vr->def_memtype || !vr->def_memtype->ev_resize) {
        if (!map_page_region(vmp, limit, 0, extralen,
            VR_WRITABLE | VR_ANON,
            0, &mem_type_anon)) {
            printf("resize: couldn't put anon memory there\n");
            return ENOMEM;
        }
        return OK;
    }

    newpr = realloc(vr->physblocks, newslots * sizeof(struct phys_region *));
    if (!newpr) {
        printf("VM: map_region_extend_upto_v: realloc failed\n");
        return ENOMEM;
    }

    vr->physblocks = newpr;
    memset(vr->physblocks + prevslots, 0, addedslots * sizeof(struct phys_region *));

    r = vr->def_memtype->ev_resize(vmp, vr, offset - vr->vaddr);

    return r;
}

/*========================================================================*
 *				map_unmap_region	     	  	*
 *========================================================================*/
int map_unmap_region(struct vmproc *vmp, struct vir_region *r,
	vir_bytes offset, vir_bytes len)
{
	vir_bytes regionstart;
	int freeslots = phys_slot(len);

	SANITYCHECK(SCL_FUNCTIONS);

	if (offset + len > r->length || (len % VM_PAGE_SIZE)) {
		printf("VM: bogus length 0x%lx\n", len);
		return EINVAL;
	}

	regionstart = r->vaddr + offset;
	map_subfree(r, offset, len);

	if (r->length == len) {
		region_remove(&vmp->vm_regions_avl, r->vaddr);
		map_free(r);
	} else if (offset == 0) {
		if (map_unmap_region_shrink_start(vmp, r, len, freeslots) != OK) {
			return EINVAL;
		}
	} else if (offset + len == r->length) {
		r->length -= len;
	}

	SANITYCHECK(SCL_DETAIL);

	if (pt_writemap(vmp, &vmp->vm_pt, regionstart, MAP_NONE, len, 0, WMF_OVERWRITE) != OK) {
		printf("VM: map_unmap_region: pt_writemap failed\n");
		return ENOMEM;
	}

	SANITYCHECK(SCL_FUNCTIONS);
	return OK;
}

static int map_unmap_region_shrink_start(struct vmproc *vmp, struct vir_region *r, 
	vir_bytes len, int freeslots)
{
	struct phys_region *pr;
	vir_bytes voffset;
	int remslots;

	if (!r->def_memtype->ev_lowshrink) {
		printf("VM: low-shrinking not implemented for %s\n", r->def_memtype->name);
		return EINVAL;
	}

	if (r->def_memtype->ev_lowshrink(r, len) != OK) {
		printf("VM: low-shrinking failed for %s\n", r->def_memtype->name);
		return EINVAL;
	}

	region_remove(&vmp->vm_regions_avl, r->vaddr);
	USE(r, r->vaddr += len;);
	remslots = phys_slot(r->length);
	region_insert(&vmp->vm_regions_avl, r);

	for (voffset = len; voffset < r->length; voffset += VM_PAGE_SIZE) {
		pr = physblock_get(r, voffset);
		if (!pr) continue;
		assert(pr->offset >= len);
		USE(pr, pr->offset -= len;);
	}

	if (remslots) {
		memmove(r->physblocks, r->physblocks + freeslots,
			remslots * sizeof(struct phys_region *));
	}

	USE(r, r->length -= len;);
	return OK;
}

static int split_region(struct vmproc *vmp, struct vir_region *vr,
	struct vir_region **vr1, struct vir_region **vr2, vir_bytes split_len)
{
	struct vir_region *r1 = NULL, *r2 = NULL;
	vir_bytes rem_len = vr->length - split_len;
	vir_bytes voffset;
	int result = OK;

	assert(!(split_len % VM_PAGE_SIZE));
	assert(!(rem_len % VM_PAGE_SIZE));
	assert(!(vr->vaddr % VM_PAGE_SIZE));
	assert(!(vr->length % VM_PAGE_SIZE));

	if(!vr->def_memtype->ev_split) {
		printf("VM: split region not implemented for %s\n",
			vr->def_memtype->name);
		sys_diagctl_stacktrace(vmp->vm_endpoint);
		return EINVAL;
	}

	r1 = region_new(vmp, vr->vaddr, split_len, vr->flags, vr->def_memtype);
	if(!r1) {
		result = ENOMEM;
		goto cleanup;
	}

	r2 = region_new(vmp, vr->vaddr + split_len, rem_len, vr->flags, vr->def_memtype);
	if(!r2) {
		result = ENOMEM;
		goto cleanup;
	}

	for(voffset = 0; voffset < r1->length; voffset += VM_PAGE_SIZE) {
		struct phys_region *ph = physblock_get(vr, voffset);
		if(!ph) continue;
		
		struct phys_region *phn = pb_reference(ph->ph, voffset, r1, ph->memtype);
		if(!phn) {
			result = ENOMEM;
			goto cleanup;
		}
	}

	for(voffset = 0; voffset < r2->length; voffset += VM_PAGE_SIZE) {
		struct phys_region *ph = physblock_get(vr, split_len + voffset);
		if(!ph) continue;
		
		struct phys_region *phn = pb_reference(ph->ph, voffset, r2, ph->memtype);
		if(!phn) {
			result = ENOMEM;
			goto cleanup;
		}
	}

	vr->def_memtype->ev_split(vmp, vr, r1, r2);

	region_remove(&vmp->vm_regions_avl, vr->vaddr);
	map_free(vr);
	region_insert(&vmp->vm_regions_avl, r1);
	region_insert(&vmp->vm_regions_avl, r2);

	*vr1 = r1;
	*vr2 = r2;

	return OK;

cleanup:
	if(r1) map_free(r1);
	if(r2) map_free(r2);
	printf("split_region: failed\n");
	return result;
}

int map_unmap_range(struct vmproc *vmp, vir_bytes unmap_start, vir_bytes length)
{
    region_iter v_iter;
    struct vir_region *vr, *nextvr;
    vir_bytes o, unmap_limit;
    int r;

    if (!vmp) {
        return EINVAL;
    }

    o = unmap_start % VM_PAGE_SIZE;
    unmap_start -= o;
    length += o;
    length = roundup(length, VM_PAGE_SIZE);
    unmap_limit = length + unmap_start;

    if (length < VM_PAGE_SIZE || unmap_limit <= unmap_start) {
        return EINVAL;
    }

    vr = find_initial_region(&vmp->vm_regions_avl, &v_iter, unmap_start);
    if (!vr) {
        return OK;
    }

    for (; vr && vr->vaddr < unmap_limit; vr = nextvr) {
        vir_bytes thislimit = vr->vaddr + vr->length;
        vir_bytes this_unmap_start = MAX(unmap_start, vr->vaddr);
        vir_bytes this_unmap_limit = MIN(unmap_limit, thislimit);

        region_incr_iter(&v_iter);
        nextvr = region_get_iter(&v_iter);

        if (this_unmap_start >= this_unmap_limit) {
            continue;
        }

        if (needs_split(vr, this_unmap_start, this_unmap_limit)) {
            r = handle_region_split(vmp, &vr, this_unmap_limit);
            if (r != OK) {
                return r;
            }
            thislimit = vr->vaddr + vr->length;
        }

        r = map_unmap_region(vmp, vr, this_unmap_start - vr->vaddr,
                            this_unmap_limit - this_unmap_start);
        if (r != OK) {
            return r;
        }

        if (nextvr) {
            region_start_iter(&vmp->vm_regions_avl, &v_iter, nextvr->vaddr, AVL_EQUAL);
        }
    }

    return OK;
}

static struct vir_region *find_initial_region(avl_tree_t *regions, region_iter *iter, vir_bytes start)
{
    struct vir_region *vr;

    region_start_iter(regions, iter, start, AVL_LESS_EQUAL);
    vr = region_get_iter(iter);
    
    if (!vr) {
        region_start_iter(regions, iter, start, AVL_GREATER);
        vr = region_get_iter(iter);
    }

    return vr;
}

static int needs_split(struct vir_region *vr, vir_bytes start, vir_bytes limit)
{
    vir_bytes thislimit = vr->vaddr + vr->length;
    return (start > vr->vaddr && limit < thislimit);
}

static int handle_region_split(struct vmproc *vmp, struct vir_region **vr, vir_bytes split_limit)
{
    struct vir_region *vr1, *vr2;
    vir_bytes split_len = split_limit - (*vr)->vaddr;
    int r;

    if (split_len <= 0 || split_len >= (*vr)->length) {
        return EINVAL;
    }

    r = split_region(vmp, *vr, &vr1, &vr2, split_len);
    if (r != OK) {
        return r;
    }

    *vr = vr1;
    return OK;
}

/*========================================================================*
 *			  map_region_lookup_type			  *
 *========================================================================*/
struct vir_region* map_region_lookup_type(struct vmproc *vmp, u32_t type)
{
	struct vir_region *vr;
	region_iter v_iter;
	
	if (!vmp) {
		return NULL;
	}
	
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while((vr = region_get_iter(&v_iter))) {
		region_incr_iter(&v_iter);
		if(vr->flags & type) {
			return vr;
		}
	}

	return NULL;
}

/*========================================================================*
 *				map_get_phys				  *
 *========================================================================*/
int map_get_phys(struct vmproc *vmp, vir_bytes addr, phys_bytes *r)
{
	struct vir_region *vr;

	if (!vmp) {
		return EINVAL;
	}

	vr = map_lookup(vmp, addr, NULL);
	if (!vr) {
		return EINVAL;
	}

	if (vr->vaddr != addr) {
		return EINVAL;
	}

	if (!vr->def_memtype) {
		return EINVAL;
	}

	if (!vr->def_memtype->regionid) {
		return EINVAL;
	}

	if (r) {
		*r = vr->def_memtype->regionid(vr);
	}

	return OK;
}

/*========================================================================*
 *				map_get_ref				  *
 *========================================================================*/
int map_get_ref(struct vmproc *vmp, vir_bytes addr, u8_t *cnt)
{
	struct vir_region *vr;

	if (!vmp || !addr) {
		return EINVAL;
	}

	vr = map_lookup(vmp, addr, NULL);
	if (!vr) {
		return EINVAL;
	}

	if (vr->vaddr != addr) {
		return EINVAL;
	}

	if (!vr->def_memtype || !vr->def_memtype->refcount) {
		return EINVAL;
	}

	if (cnt) {
		*cnt = vr->def_memtype->refcount(vr);
	}

	return OK;
}

void get_usage_info_kernel(struct vm_usage_info *vui)
{
	if (!vui) {
		return;
	}
	
	memset(vui, 0, sizeof(*vui));
	vui->vui_total = kernel_boot_info.kernel_allocated_bytes +
		kernel_boot_info.kernel_allocated_bytes_dynamic;
	vui->vui_virtual = vui->vui_total;
	vui->vui_mvirtual = vui->vui_total;
}

static void get_usage_info_vm(struct vm_usage_info *vui)
{
	if (vui == NULL) {
		return;
	}
	
	memset(vui, 0, sizeof(*vui));
	
	size_t vm_self_bytes = (size_t)get_vm_self_pages() * VM_PAGE_SIZE;
	vui->vui_total = kernel_boot_info.vm_allocated_bytes + vm_self_bytes;
	vui->vui_virtual = vui->vui_total;
	vui->vui_mvirtual = vui->vui_total;
}

/*
 * Return whether the given region is for the associated process's stack.
 * Unfortunately, we do not actually have this information: in most cases, VM
 * is not responsible for actually setting up the stack in the first place.
 * Fortunately, this is only for statistical purposes, so we can get away with
 * guess work.  However, it is certainly not accurate in the light of userspace
 * thread stacks, or if the process is messing with its stack in any way, or if
 * (currently) VFS decides to put the stack elsewhere, etcetera.
 */
static int
is_stack_region(struct vir_region * vr)
{
	if (!vr) {
		return 0;
	}

	return (vr->vaddr == VM_STACKTOP - DEFAULT_STACK_LIMIT &&
	    vr->length == DEFAULT_STACK_LIMIT);
}

/*========================================================================*
 *				get_usage_info				  *
 *========================================================================*/
void get_usage_info(struct vmproc *vmp, struct vm_usage_info *vui)
{
	struct vir_region *vr;
	struct phys_region *ph;
	region_iter v_iter;
	vir_bytes voffset;

	if (!vmp || !vui) {
		return;
	}

	memset(vui, 0, sizeof(*vui));

	if (vmp->vm_endpoint == VM_PROC_NR) {
		get_usage_info_vm(vui);
		return;
	}

	if (vmp->vm_endpoint < 0) {
		get_usage_info_kernel(vui);
		return;
	}

	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while ((vr = region_get_iter(&v_iter))) {
		vui->vui_virtual += vr->length;
		vui->vui_mvirtual += vr->length;
		
		for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
			ph = physblock_get(vr, voffset);
			if (!ph) {
				if (is_stack_region(vr)) {
					vui->vui_mvirtual -= VM_PAGE_SIZE;
				}
				continue;
			}

			vui->vui_total += VM_PAGE_SIZE;

			if (ph->ph->refcount > 1) {
				vui->vui_common += VM_PAGE_SIZE;
				if (vr->flags & VR_SHARED) {
					vui->vui_shared += VM_PAGE_SIZE;
				}
			}
		}
		region_incr_iter(&v_iter);
	}

	vui->vui_maxrss = vmp->vm_total_max / 1024L;
	vui->vui_minflt = vmp->vm_minor_page_fault;
	vui->vui_majflt = vmp->vm_major_page_fault;
}

/*===========================================================================*
 *				get_region_info				     *
 *===========================================================================*/
int get_region_info(struct vmproc *vmp, struct vm_region_info *vri,
	int max, vir_bytes *nextp)
{
	struct vir_region *vr;
	vir_bytes next;
	int count;
	region_iter v_iter;

	if (!vmp || !vri || !nextp || max <= 0) {
		return 0;
	}

	next = *nextp;

	region_start_iter(&vmp->vm_regions_avl, &v_iter, next, AVL_GREATER_EQUAL);
	vr = region_get_iter(&v_iter);
	if (!vr) {
		return 0;
	}

	count = 0;
	while (vr && count < max) {
		struct phys_region *ph1 = NULL, *ph2 = NULL;
		vir_bytes voffset;

		next = vr->vaddr + vr->length;

		for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
			struct phys_region *ph = physblock_get(vr, voffset);
			if (ph) {
				if (!ph1) {
					ph1 = ph;
				}
				ph2 = ph;
			}
		}

		if (ph1 && ph2) {
			vri->vri_addr = vr->vaddr + ph1->offset;
			vri->vri_prot = PROT_READ;
			vri->vri_length = ph2->offset + VM_PAGE_SIZE - ph1->offset;

			if (vr->flags & VR_WRITABLE) {
				vri->vri_prot |= PROT_WRITE;
			}
			count++;
			vri++;
		} else {
			printf("skipping empty region 0x%lx-0x%lx\n",
				vr->vaddr, vr->vaddr + vr->length);
		}

		region_incr_iter(&v_iter);
		vr = region_get_iter(&v_iter);
	}

	*nextp = next;
	return count;
}

/*========================================================================*
 *				regionprintstats			  *
 *========================================================================*/
void printregionstats(struct vmproc *vmp)
{
    struct vir_region *vr;
    struct phys_region *pr;
    vir_bytes used = 0, weighted = 0;
    region_iter v_iter;
    
    if (!vmp) {
        printf("%6lukB  %6lukB\n", 0UL, 0UL);
        return;
    }
    
    region_start_iter_least(&vmp->vm_regions_avl, &v_iter);
    
    while ((vr = region_get_iter(&v_iter))) {
        vir_bytes voffset;
        region_incr_iter(&v_iter);
        
        if (vr->flags & VR_DIRECT) {
            continue;
        }
        
        for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
            pr = physblock_get(vr, voffset);
            if (!pr || !pr->ph || pr->ph->refcount == 0) {
                continue;
            }
            
            used += VM_PAGE_SIZE;
            weighted += VM_PAGE_SIZE / pr->ph->refcount;
        }
    }
    
    printf("%6lukB  %6lukB\n", used / 1024, weighted / 1024);
}

void map_setparent(struct vmproc *vmp)
{
    region_iter iter;
    struct vir_region *vr;
    
    if (!vmp) {
        return;
    }
    
    region_start_iter_least(&vmp->vm_regions_avl, &iter);
    while ((vr = region_get_iter(&iter)) != NULL) {
        USE(vr, vr->parent = vmp;);
        region_incr_iter(&iter);
    }
}

unsigned int physregions(struct vir_region *vr)
{
	if (!vr || vr->length == 0) {
		return 0;
	}
	
	unsigned int n = 0;
	vir_bytes max_offset = vr->length - (vr->length % VM_PAGE_SIZE);
	
	for (vir_bytes voffset = 0; voffset < max_offset; voffset += VM_PAGE_SIZE) {
		if (physblock_get(vr, voffset)) {
			n++;
		}
	}
	
	if (vr->length % VM_PAGE_SIZE != 0 && physblock_get(vr, max_offset)) {
		n++;
	}
	
	return n;
}
