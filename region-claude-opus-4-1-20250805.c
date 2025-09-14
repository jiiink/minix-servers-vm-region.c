
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
}

static void map_printregion(struct vir_region *vr)
{
	unsigned int i;
	struct phys_region *ph;
	
	if (!vr) {
		return;
	}
	
	if (!vr->def_memtype || !vr->def_memtype->name) {
		return;
	}
	
	printf("map_printmap: map_name: %s\n", vr->def_memtype->name);
	printf("\t%lx (len 0x%lx, %lukB), %p, %s\n",
		vr->vaddr, vr->length, vr->length/1024,
		vr->def_memtype->name,
		(vr->flags & VR_WRITABLE) ? "writable" : "readonly");
	printf("\t\tphysblocks:\n");
	
	if (!vr->physblocks) {
		return;
	}
	
	for(i = 0; i < vr->length/VM_PAGE_SIZE; i++) {
		ph = vr->physblocks[i];
		if (!ph) {
			continue;
		}
		
		if (!ph->ph) {
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
	size_t index;
	
	assert(region != NULL);
	assert((offset % VM_PAGE_SIZE) == 0);
	assert(offset < region->length);
	
	index = offset / VM_PAGE_SIZE;
	
	if (index >= region->length / VM_PAGE_SIZE) {
		return NULL;
	}
	
	foundregion = region->physblocks[index];
	
	if (foundregion != NULL) {
		assert(foundregion->offset == offset);
	}
	
	return foundregion;
}

void physblock_set(struct vir_region *region, vir_bytes offset,
	struct phys_region *newphysr)
{
	int i;
	struct vmproc *proc;
	
	assert(region != NULL);
	assert(!(offset % VM_PAGE_SIZE));
	assert(offset < region->length);
	
	i = offset / VM_PAGE_SIZE;
	proc = region->parent;
	assert(proc != NULL);
	
	if (newphysr != NULL) {
		assert(region->physblocks[i] == NULL);
		assert(newphysr->offset == offset);
		
		proc->vm_total += VM_PAGE_SIZE;
		if (proc->vm_total > proc->vm_total_max) {
			proc->vm_total_max = proc->vm_total;
		}
		
		region->physblocks[i] = newphysr;
	} else {
		assert(region->physblocks[i] != NULL);
		
		proc->vm_total -= VM_PAGE_SIZE;
		region->physblocks[i] = NULL;
	}
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
	while ((vr = region_get_iter(&iter))) {
		map_printregion(vr);
		region_incr_iter(&iter);
	}
}

static struct vir_region *getnextvr(struct vir_region *vr)
{
	struct vir_region *nextvr;
	struct vir_region *current;
	region_iter v_iter;
	
	if (!vr) {
		return NULL;
	}
	
	SLABSANE(vr);
	
	if (!vr->parent) {
		return NULL;
	}
	
	region_start_iter(&vr->parent->vm_regions_avl, &v_iter, vr->vaddr, AVL_EQUAL);
	
	current = region_get_iter(&v_iter);
	if (!current) {
		return NULL;
	}
	
	if (current != vr) {
		return NULL;
	}
	
	region_incr_iter(&v_iter);
	nextvr = region_get_iter(&v_iter);
	
	if (!nextvr) {
		return NULL;
	}
	
	SLABSANE(nextvr);
	
	if (vr->parent != nextvr->parent) {
		return NULL;
	}
	
	if (vr->vaddr >= nextvr->vaddr) {
		return NULL;
	}
	
	if (vr->vaddr + vr->length > nextvr->vaddr) {
		return NULL;
	}
	
	return nextvr;
}

static int pr_writable(struct vir_region *vr, struct phys_region *pr)
{
	if (!vr || !pr || !pr->memtype || !pr->memtype->writable) {
		return 0;
	}
	
	if (!(vr->flags & VR_WRITABLE)) {
		return 0;
	}
	
	return pr->memtype->writable(pr);
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
	int flags;
	struct phys_block *pb;
	int write_flags;
	int result;

	if (!vmp || !vr || !pr) {
		return EINVAL;
	}

	pb = pr->ph;
	if (!pb) {
		return EINVAL;
	}

	assert(!(vr->vaddr % VM_PAGE_SIZE));
	assert(!(pr->offset % VM_PAGE_SIZE));
	assert(pb->refcount > 0);

	flags = PTF_PRESENT | PTF_USER;

	if (pr_writable(vr, pr)) {
		flags |= PTF_WRITE;
	} else {
		flags |= PTF_READ;
	}

	if (vr->def_memtype && vr->def_memtype->pt_flags) {
		flags |= vr->def_memtype->pt_flags(vr);
	}

#if SANITYCHECKS
	write_flags = pr->written ? WMF_OVERWRITE : 0;
#else
	write_flags = WMF_OVERWRITE;
#endif

	result = pt_writemap(vmp, &vmp->vm_pt, vr->vaddr + pr->offset,
			pb->phys, VM_PAGE_SIZE, flags, write_flags);
	
	if (result != OK) {
		printf("VM: map_writept: pt_writemap failed\n");
		return ENOMEM;
	}

#if SANITYCHECKS
	USE(pr, pr->written = 1;);
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

	assert(length > 0);

	if(maxv == 0) {
		maxv = minv + length;
		if(maxv <= minv) {
			printf("region_find_slot: minv 0x%lx and bytes 0x%lx\n",
				minv, length);
			return SLOT_FAIL;
		}
	}

	assert(!(length % VM_PAGE_SIZE));
	if(minv >= maxv) {
		printf("VM: 1 minv: 0x%lx maxv: 0x%lx length: 0x%lx\n",
			minv, maxv, length);
	}

	assert(minv < maxv);

	if(minv + length > maxv)
		return SLOT_FAIL;

	region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_GREATER_EQUAL);
	lastregion = region_get_iter(&iter);

	if(!lastregion) {
		region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_LESS);
		lastregion = region_get_iter(&iter);
		vir_bytes range_start = lastregion ? lastregion->vaddr + lastregion->length : 0;
		vir_bytes range_end = VM_DATATOP;
		
		if(!try_free_range(&startv, &foundflag, range_start + VM_PAGE_SIZE, 
				range_end - VM_PAGE_SIZE, minv, maxv, length)) {
			try_free_range(&startv, &foundflag, range_start, range_end, 
					minv, maxv, length);
		}
	}

	if(!foundflag) {
		struct vir_region *vr;
		while((vr = region_get_iter(&iter)) && !foundflag) {
			struct vir_region *nextvr;
			region_decr_iter(&iter);
			nextvr = region_get_iter(&iter);
			vir_bytes range_start = nextvr ? nextvr->vaddr + nextvr->length : 0;
			vir_bytes range_end = vr->vaddr;
			
			if(!try_free_range(&startv, &foundflag, range_start + VM_PAGE_SIZE,
					range_end - VM_PAGE_SIZE, minv, maxv, length)) {
				try_free_range(&startv, &foundflag, range_start, range_end,
						minv, maxv, length);
			}
		}
	}

	if(!foundflag) {
		return SLOT_FAIL;
	}

	assert(startv >= minv);
	assert(startv < maxv);
	assert(startv + length <= maxv);

	vmp->vm_region_top = startv + length;

	return startv;
}

static int try_free_range(vir_bytes *startv, int *foundflag, 
		vir_bytes rangestart, vir_bytes rangeend,
		vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
	vir_bytes frstart = rangestart;
	vir_bytes frend = rangeend;
	
	if(frstart < minv)
		frstart = minv;
	if(frend > maxv)
		frend = maxv;
		
	if(frend > frstart && (frend - frstart) >= length) {
		*startv = frend - length;
		*foundflag = 1;
		return 1;
	}
	return 0;
}

/*===========================================================================*
 *				region_find_slot			     *
 *===========================================================================*/
static vir_bytes region_find_slot(struct vmproc *vmp,
		vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
	vir_bytes hint;
	vir_bytes result;

	if (vmp == NULL) {
		return SLOT_FAIL;
	}

	hint = vmp->vm_region_top;

	if (maxv != 0 && hint < maxv && hint >= minv) {
		result = region_find_slot_range(vmp, minv, hint, length);
		if (result != SLOT_FAIL) {
			return result;
		}
	}

	return region_find_slot_range(vmp, minv, maxv, length);
}

static unsigned int phys_slot(vir_bytes len)
{
	if (len % VM_PAGE_SIZE != 0) {
		assert(0);
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
	int slots = phys_slot(length);

	if(!(SLABALLOC(newregion))) {
		printf("vm: region_new: could not allocate\n");
		return NULL;
	}

	USE(newregion,
		memset(newregion, 0, sizeof(*newregion));
		newregion->vaddr = startv;
		newregion->length = length;
		newregion->flags = flags;
		newregion->def_memtype = memtype;
		newregion->remaps = 0;
		newregion->id = id++;
		newregion->lower = newregion->higher = NULL;
		newregion->parent = vmp;
	);

	if(!(newphysregions = calloc(slots, sizeof(struct phys_region *)))) {
		printf("VM: region_new: allocating phys blocks failed\n");
		SLABFREE(newregion);
		return NULL;
	}

	USE(newregion, 
		newregion->physblocks = newphysregions;
	);

	return newregion;
}

/*===========================================================================*
 *				map_page_region				     *
 *===========================================================================*/
struct vir_region *map_page_region(struct vmproc *vmp, vir_bytes minv,
	vir_bytes maxv, vir_bytes length, u32_t flags, int mapflags,
	mem_type_t *memtype)
{
	struct vir_region *newregion = NULL;
	vir_bytes startv;

	if (!vmp || !memtype) {
		return NULL;
	}

	if (length == 0 || (length % VM_PAGE_SIZE) != 0) {
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

	if ((mapflags & MF_PREALLOC) != 0) {
		if (map_handle_memory(vmp, newregion, 0, length, 1,
			NULL, 0, 0) != OK) {
			printf("VM: map_page_region: prealloc failed\n");
			map_free(newregion);
			return NULL;
		}
	}

	USE(newregion, newregion->flags &= ~VR_UNINITIALIZED;);

	region_insert(&vmp->vm_regions_avl, newregion);

#if SANITYCHECKS
	assert(startv == newregion->vaddr);
	{
		struct vir_region *nextvr = getnextvr(newregion);
		if (nextvr) {
			assert(newregion->vaddr < nextvr->vaddr);
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

	if (start > SIZE_MAX - len) {
		return EOVERFLOW;
	}

	end = start + len;

#if SANITYCHECKS
	SLABSANE(region);
	validate_region_integrity(region);
#endif

	for (voffset = start; voffset < end; voffset += VM_PAGE_SIZE) {
		pr = physblock_get(region, voffset);
		if (!pr) {
			continue;
		}
		assert(pr->offset >= start);
		assert(pr->offset < end);
		pb_unreferenced(region, pr, 1);
		SLABFREE(pr);
	}

	return OK;
}

#if SANITYCHECKS
static void validate_region_integrity(struct vir_region *region)
{
	vir_bytes voffset;
	struct phys_region *pr;
	struct phys_block *pb;
	struct phys_region *others;

	for (voffset = 0; voffset < phys_slot(region->length); voffset += VM_PAGE_SIZE) {
		pr = physblock_get(region, voffset);
		if (!pr) {
			continue;
		}

		pb = pr->ph;
		for (others = pb->firstregion; others; others = others->next_ph_list) {
			assert(others->ph == pb);
		}
	}
}
#endif

/*===========================================================================*
 *				map_free				     *
 *===========================================================================*/
int map_free(struct vir_region *region)
{
	int r;

	if (region == NULL) {
		return EINVAL;
	}

	r = map_subfree(region, 0, region->length);
	if (r != OK) {
		return r;
	}

	if (region->def_memtype != NULL && region->def_memtype->ev_delete != NULL) {
		region->def_memtype->ev_delete(region);
	}

	if (region->physblocks != NULL) {
		free(region->physblocks);
		region->physblocks = NULL;
	}

	SLABFREE(region);

	return OK;
}

/*========================================================================*
 *				map_free_proc				  *
 *========================================================================*/
int map_free_proc(struct vmproc *vmp)
{
	struct vir_region *r;

	if (vmp == NULL) {
		return EINVAL;
	}

	for (;;) {
		SANITYCHECK(SCL_DETAIL);
		
		r = region_search_root(&vmp->vm_regions_avl);
		if (r == NULL) {
			break;
		}

#if SANITYCHECKS
		nocheck++;
#endif
		region_remove(&vmp->vm_regions_avl, r->vaddr);
		map_free(r);
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
	vir_bytes ph;

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

	ph = offset - r->vaddr;
	if (physr) {
		*physr = physblock_get(r, ph);
		if (*physr) {
			assert((*physr)->offset == ph);
		}
	}

	return r;
}

u32_t vrallocflags(u32_t flags)
{
	u32_t allocflags = 0;

	if ((flags & VR_PHYS64K) != 0) {
		allocflags |= PAF_ALIGN64K;
	}
	if ((flags & VR_LOWER16MB) != 0) {
		allocflags |= PAF_LOWER16MB;
	}
	if ((flags & VR_LOWER1MB) != 0) {
		allocflags |= PAF_LOWER1MB;
	}
	if ((flags & VR_UNINITIALIZED) == 0) {
		allocflags |= PAF_CLEAR;
	}

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
	struct phys_block *pb = NULL;
	int r = OK;

	if (!vmp || !region) {
		return EINVAL;
	}

	offset -= offset % VM_PAGE_SIZE;

	if (offset >= region->length) {
		return EINVAL;
	}

	if (region->vaddr % VM_PAGE_SIZE) {
		return EINVAL;
	}

	if (write && !(region->flags & VR_WRITABLE)) {
		return EACCES;
	}

	SANITYCHECK(SCL_FUNCTIONS);

	ph = physblock_get(region, offset);
	if (!ph) {
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
	}

	if (!ph || !ph->ph || !ph->memtype) {
		return EFAULT;
	}

	if (!ph->memtype->writable) {
		return EFAULT;
	}

	if (write && ph->memtype->writable(ph)) {
		goto write_page_table;
	}

	if (!ph->memtype->ev_pagefault) {
		return EFAULT;
	}

	r = ph->memtype->ev_pagefault(vmp, region, ph, write, 
		pf_callback, state, len, io);
	
	if (r == SUSPEND) {
		return SUSPEND;
	}

	if (r != OK) {
		pb_unreferenced(region, ph, 1);
		return r;
	}

	if (!ph->ph || ph->ph->phys == MAP_NONE) {
		return EFAULT;
	}

write_page_table:
	r = map_ph_writept(vmp, region, ph);
	if (r != OK) {
		printf("map_pf: writept failed\n");
		return r;
	}

	SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
	if (pt_checkrange(&vmp->vm_pt, region->vaddr + offset,
		VM_PAGE_SIZE, write) != OK) {
		panic("map_pf: pt_checkrange failed: %d", r);
	}
#endif

	return r;
}

int map_handle_memory(struct vmproc *vmp,
	struct vir_region *region, vir_bytes start_offset, vir_bytes length,
	int write, vfs_callback_t cb, void *state, int statelen)
{
	vir_bytes offset;
	vir_bytes lim;
	int r;
	int io = 0;

	if (vmp == NULL || region == NULL) {
		return EINVAL;
	}

	if (length == 0 || length > (SIZE_MAX - start_offset)) {
		return EINVAL;
	}

	lim = start_offset + length;

	for (offset = start_offset; offset < lim; offset += VM_PAGE_SIZE) {
		if (offset > (SIZE_MAX - VM_PAGE_SIZE)) {
			return EOVERFLOW;
		}
		
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
	
	if (vmp == NULL) {
		return EINVAL;
	}
	
	region_start_iter_least(&vmp->vm_regions_avl, &iter);
	
	pt_assert(&vmp->vm_pt);
	
	while ((vr = region_get_iter(&iter))) {
		r = map_handle_memory(vmp, vr, 0, vr->length, 1, NULL, 0, 0);
		if (r != OK) {
			return r;
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

	if (vr->def_memtype && vr->def_memtype->ev_copy) {
		r = vr->def_memtype->ev_copy(vr, newvr);
		if (r != OK) {
			map_free(newvr);
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

		if (ph->memtype && ph->memtype->ev_reference) {
			ph->memtype->ev_reference(ph, newph);
		}

#if SANITYCHECKS
		USE(newph, newph->written = 0;);
#endif
	}

#if SANITYCHECKS
	assert(physregions(vr) == physregions(newvr));
#endif

	return newvr;
}

/*===========================================================================*
 *				copy_abs2region			     	*
 *===========================================================================*/
int copy_abs2region(phys_bytes absaddr, struct vir_region *destregion,
	phys_bytes offset, phys_bytes len)
{
	if (!destregion || !destregion->physblocks) {
		return EFAULT;
	}

	while (len > 0) {
		struct phys_region *ph = physblock_get(destregion, offset);
		if (!ph) {
			return EFAULT;
		}

		if (ph->offset > offset || ph->offset + VM_PAGE_SIZE <= offset) {
			return EFAULT;
		}

		phys_bytes suboffset = offset - ph->offset;
		if (suboffset >= VM_PAGE_SIZE) {
			return EFAULT;
		}

		phys_bytes sublen = len;
		phys_bytes remaining = VM_PAGE_SIZE - suboffset;
		if (sublen > remaining) {
			sublen = remaining;
		}

		if (!ph->ph || ph->ph->refcount != 1) {
			return EFAULT;
		}

		if (sys_abscopy(absaddr, ph->ph->phys + suboffset, sublen) != OK) {
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
	
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while((vr = region_get_iter(&v_iter))) {
		vir_bytes p;
		
		for(p = 0; p < vr->length; p += VM_PAGE_SIZE) {
			ph = physblock_get(vr, p);
			if(!ph) {
				continue;
			}

			r = map_ph_writept(vmp, vr, ph);
			if(r != OK) {
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
    if (dst == NULL || src == NULL) {
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

	if (!start_src_vr) {
		start_src_vr = region_search_least(&src->vm_regions_avl);
		if (!start_src_vr)
			return EINVAL;
	}
	
	if (!end_src_vr) {
		end_src_vr = region_search_greatest(&src->vm_regions_avl);
		if (!end_src_vr)
			return EINVAL;
	}

	if (start_src_vr->parent != src)
		return EINVAL;

	region_start_iter(&src->vm_regions_avl, &v_iter,
		start_src_vr->vaddr, AVL_EQUAL);
	
	if (region_get_iter(&v_iter) != start_src_vr)
		return EINVAL;

	SANITYCHECK(SCL_FUNCTIONS);

	vr = region_get_iter(&v_iter);
	while (vr) {
		struct vir_region *newvr = map_copy_region(dst, vr);
		if (!newvr) {
			map_free_proc(dst);
			return ENOMEM;
		}
		
		region_insert(&dst->vm_regions_avl, newvr);
		
		if (vr->length != newvr->length) {
			map_free_proc(dst);
			return EINVAL;
		}

#if SANITYCHECKS
		verify_physblocks(vr, newvr);
#endif
		
		if (vr == end_src_vr)
			break;
			
		region_incr_iter(&v_iter);
		vr = region_get_iter(&v_iter);
	}

	map_writept(src);
	map_writept(dst);

	SANITYCHECK(SCL_FUNCTIONS);
	return OK;
}

#if SANITYCHECKS
static void verify_physblocks(struct vir_region *vr, struct vir_region *newvr)
{
	vir_bytes vaddr;
	struct phys_region *orig_ph, *new_ph;
	
	if (vr->physblocks == newvr->physblocks)
		return;
		
	for (vaddr = 0; vaddr < vr->length; vaddr += VM_PAGE_SIZE) {
		orig_ph = physblock_get(vr, vaddr);
		new_ph = physblock_get(newvr, vaddr);
		
		if (!orig_ph) {
			if (new_ph)
				break;
			continue;
		}
		
		if (!new_ph || orig_ph == new_ph || orig_ph->ph != new_ph->ph)
			break;
	}
}
#endif

int map_region_extend_upto_v(struct vmproc *vmp, vir_bytes v)
{
	vir_bytes offset, limit, extralen;
	struct vir_region *vr, *nextvr;
	struct phys_region **newpr;
	int newslots, prevslots, addedslots;

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
	assert(vr->vaddr <= offset);
	
	newslots = phys_slot(offset - vr->vaddr);
	prevslots = phys_slot(vr->length);
	assert(newslots >= prevslots);
	
	addedslots = newslots - prevslots;
	extralen = offset - limit;
	assert(extralen > 0);

	nextvr = getnextvr(vr);
	if (nextvr) {
		assert(offset <= nextvr->vaddr);
		if (nextvr->vaddr < offset) {
			printf("VM: can't grow into next region\n");
			return ENOMEM;
		}
	}

	if (!vr->def_memtype->ev_resize) {
		if (!map_page_region(vmp, limit, 0, extralen,
			VR_WRITABLE | VR_ANON, 0, &mem_type_anon)) {
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

	return vr->def_memtype->ev_resize(vmp, vr, offset - vr->vaddr);
}

/*========================================================================*
 *				map_unmap_region	     	  	*
 *========================================================================*/
int map_unmap_region(struct vmproc *vmp, struct vir_region *r,
	vir_bytes offset, vir_bytes len)
{
	vir_bytes regionstart;
	int freeslots;

	SANITYCHECK(SCL_FUNCTIONS);

	if(vmp == NULL || r == NULL) {
		return EINVAL;
	}

	if(len == 0 || len > r->length || offset > r->length - len || (len % VM_PAGE_SIZE)) {
		printf("VM: bogus length 0x%lx\n", len);
		return EINVAL;
	}

	freeslots = phys_slot(len);
	regionstart = r->vaddr + offset;

	map_subfree(r, offset, len);

	if(r->length == len) {
		region_remove(&vmp->vm_regions_avl, r->vaddr);
		map_free(r);
	} else if(offset == 0) {
		int result = handle_low_shrink(vmp, r, len, freeslots);
		if(result != OK) {
			return result;
		}
	} else if(offset + len == r->length) {
		r->length -= len;
	}

	SANITYCHECK(SCL_DETAIL);

	if(pt_writemap(vmp, &vmp->vm_pt, regionstart,
	  MAP_NONE, len, 0, WMF_OVERWRITE) != OK) {
	    printf("VM: map_unmap_region: pt_writemap failed\n");
	    return ENOMEM;
	}

	SANITYCHECK(SCL_FUNCTIONS);

	return OK;
}

static int handle_low_shrink(struct vmproc *vmp, struct vir_region *r, 
	vir_bytes len, int freeslots)
{
	struct phys_region *pr;
	vir_bytes voffset;
	int remslots;

	if(!r->def_memtype || !r->def_memtype->ev_lowshrink) {
		printf("VM: low-shrinking not implemented for %s\n",
			r->def_memtype ? r->def_memtype->name : "unknown");
		return EINVAL;
	}

	if(r->def_memtype->ev_lowshrink(r, len) != OK) {
		printf("VM: low-shrinking failed for %s\n",
			r->def_memtype->name);
		return EINVAL;
	}

	region_remove(&vmp->vm_regions_avl, r->vaddr);

	USE(r, r->vaddr += len;);

	remslots = phys_slot(r->length);

	region_insert(&vmp->vm_regions_avl, r);

	for(voffset = len; voffset < r->length; voffset += VM_PAGE_SIZE) {
		pr = physblock_get(r, voffset);
		if(pr == NULL) {
			continue;
		}
		if(pr->offset < len) {
			return EINVAL;
		}
		USE(pr, pr->offset -= len;);
	}

	if(remslots > 0 && r->physblocks != NULL) {
		memmove(r->physblocks, r->physblocks + freeslots,
			remslots * sizeof(struct phys_region *));
	}

	USE(r, r->length -= len;);

	return OK;
}

static int split_region(struct vmproc *vmp, struct vir_region *vr,
	struct vir_region **vr1, struct vir_region **vr2, vir_bytes split_len)
{
	struct vir_region *r1 = NULL;
	struct vir_region *r2 = NULL;
	vir_bytes rem_len = vr->length - split_len;

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
		return ENOMEM;
	}

	r2 = region_new(vmp, vr->vaddr + split_len, rem_len, vr->flags, vr->def_memtype);
	if(!r2) {
		map_free(r1);
		return ENOMEM;
	}

	if(copy_physblocks(vr, r1, 0, split_len) != OK) {
		cleanup_regions(r1, r2);
		return ENOMEM;
	}

	if(copy_physblocks(vr, r2, split_len, rem_len) != OK) {
		cleanup_regions(r1, r2);
		return ENOMEM;
	}

	vr->def_memtype->ev_split(vmp, vr, r1, r2);

	region_remove(&vmp->vm_regions_avl, vr->vaddr);
	map_free(vr);
	region_insert(&vmp->vm_regions_avl, r1);
	region_insert(&vmp->vm_regions_avl, r2);

	*vr1 = r1;
	*vr2 = r2;

	return OK;
}

static int copy_physblocks(struct vir_region *src, struct vir_region *dst, 
	vir_bytes src_offset, vir_bytes length)
{
	vir_bytes voffset;
	
	for(voffset = 0; voffset < length; voffset += VM_PAGE_SIZE) {
		struct phys_region *ph = physblock_get(src, src_offset + voffset);
		if(!ph) {
			continue;
		}
		
		struct phys_region *phn = pb_reference(ph->ph, voffset, dst, ph->memtype);
		if(!phn) {
			return ENOMEM;
		}
	}
	
	return OK;
}

static void cleanup_regions(struct vir_region *r1, struct vir_region *r2)
{
	if(r1) {
		map_free(r1);
	}
	if(r2) {
		map_free(r2);
	}
	printf("split_region: failed\n");
}

int map_unmap_range(struct vmproc *vmp, vir_bytes unmap_start, vir_bytes length)
{
	vir_bytes offset;
	vir_bytes unmap_limit;
	vir_bytes aligned_start;
	vir_bytes aligned_length;
	region_iter v_iter;
	struct vir_region *vr;
	struct vir_region *nextvr;

	if (!vmp) {
		return EINVAL;
	}

	offset = unmap_start % VM_PAGE_SIZE;
	aligned_start = unmap_start - offset;
	aligned_length = roundup(length + offset, VM_PAGE_SIZE);

	if (aligned_length < VM_PAGE_SIZE) {
		return EINVAL;
	}

	if (aligned_length > (SIZE_MAX - aligned_start)) {
		return EINVAL;
	}

	unmap_limit = aligned_start + aligned_length;

	region_start_iter(&vmp->vm_regions_avl, &v_iter, aligned_start, AVL_LESS_EQUAL);
	vr = region_get_iter(&v_iter);

	if (!vr) {
		region_start_iter(&vmp->vm_regions_avl, &v_iter, aligned_start, AVL_GREATER);
		vr = region_get_iter(&v_iter);
		if (!vr) {
			return OK;
		}
	}

	while (vr && vr->vaddr < unmap_limit) {
		vir_bytes region_end = vr->vaddr + vr->length;
		vir_bytes unmap_region_start;
		vir_bytes unmap_region_end;
		int result;

		region_incr_iter(&v_iter);
		nextvr = region_get_iter(&v_iter);

		if (region_end <= vr->vaddr) {
			vr = nextvr;
			continue;
		}

		unmap_region_start = (aligned_start > vr->vaddr) ? aligned_start : vr->vaddr;
		unmap_region_end = (unmap_limit < region_end) ? unmap_limit : region_end;

		if (unmap_region_start >= unmap_region_end) {
			vr = nextvr;
			continue;
		}

		if (unmap_region_start > vr->vaddr && unmap_region_end < region_end) {
			struct vir_region *vr1 = NULL;
			struct vir_region *vr2 = NULL;
			vir_bytes split_len = unmap_region_end - vr->vaddr;

			if (split_len <= 0 || split_len >= vr->length) {
				return EINVAL;
			}

			result = split_region(vmp, vr, &vr1, &vr2, split_len);
			if (result != OK) {
				return result;
			}
			vr = vr1;
			region_end = vr->vaddr + vr->length;
		}

		if (unmap_region_start < vr->vaddr || unmap_region_end > region_end) {
			return EINVAL;
		}

		result = map_unmap_region(vmp, vr, 
			unmap_region_start - vr->vaddr,
			unmap_region_end - unmap_region_start);

		if (result != OK) {
			return result;
		}

		if (nextvr) {
			region_start_iter(&vmp->vm_regions_avl, &v_iter, nextvr->vaddr, AVL_EQUAL);
			if (region_get_iter(&v_iter) != nextvr) {
				return EINVAL;
			}
		}

		vr = nextvr;
	}

	return OK;
}

/*========================================================================*
 *			  map_region_lookup_type			  *
 *========================================================================*/
struct vir_region* map_region_lookup_type(struct vmproc *vmp, u32_t type)
{
	struct vir_region *vr;
	region_iter v_iter;
	
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while((vr = region_get_iter(&v_iter))) {
		region_incr_iter(&v_iter);
		if(vr->flags & type)
			return vr;
	}

	return NULL;
}

/*========================================================================*
 *				map_get_phys				  *
 *========================================================================*/
int map_get_phys(struct vmproc *vmp, vir_bytes addr, phys_bytes *r)
{
	struct vir_region *vr;

	if (vmp == NULL) {
		return EINVAL;
	}

	vr = map_lookup(vmp, addr, NULL);
	if (vr == NULL) {
		return EINVAL;
	}

	if (vr->vaddr != addr) {
		return EINVAL;
	}

	if (vr->def_memtype == NULL) {
		return EINVAL;
	}

	if (vr->def_memtype->regionid == NULL) {
		return EINVAL;
	}

	if (r != NULL) {
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

	if (vmp == NULL) {
		return EINVAL;
	}

	vr = map_lookup(vmp, addr, NULL);
	if (vr == NULL) {
		return EINVAL;
	}

	if (vr->vaddr != addr) {
		return EINVAL;
	}

	if (vr->def_memtype == NULL || vr->def_memtype->refcount == NULL) {
		return EINVAL;
	}

	if (cnt != NULL) {
		*cnt = vr->def_memtype->refcount(vr);
	}

	return OK;
}

void get_usage_info_kernel(struct vm_usage_info *vui)
{
	if (vui == NULL) {
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
	
	size_t self_pages_bytes = get_vm_self_pages() * VM_PAGE_SIZE;
	vui->vui_total = kernel_boot_info.vm_allocated_bytes + self_pages_bytes;
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
static int is_stack_region(struct vir_region *vr)
{
    if (vr == NULL) {
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

	struct vir_region *vr;
	region_iter v_iter;
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while ((vr = region_get_iter(&v_iter))) {
		process_region(vr, vui);
		region_incr_iter(&v_iter);
	}

	vui->vui_maxrss = vmp->vm_total_max / 1024L;
	vui->vui_minflt = vmp->vm_minor_page_fault;
	vui->vui_majflt = vmp->vm_major_page_fault;
}

static void process_region(struct vir_region *vr, struct vm_usage_info *vui)
{
	if (!vr || !vui) {
		return;
	}

	vui->vui_virtual += vr->length;
	vui->vui_mvirtual += vr->length;

	for (vir_bytes voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
		struct phys_region *ph = physblock_get(vr, voffset);
		
		if (!ph) {
			handle_unmapped_page(vr, vui);
			continue;
		}
		
		process_mapped_page(vr, ph, vui);
	}
}

static void handle_unmapped_page(struct vir_region *vr, struct vm_usage_info *vui)
{
	if (is_stack_region(vr)) {
		vui->vui_mvirtual -= VM_PAGE_SIZE;
	}
}

static void process_mapped_page(struct vir_region *vr, struct phys_region *ph, struct vm_usage_info *vui)
{
	if (!ph || !ph->ph) {
		return;
	}

	vui->vui_total += VM_PAGE_SIZE;

	if (ph->ph->refcount > 1) {
		vui->vui_common += VM_PAGE_SIZE;

		if (vr->flags & VR_SHARED) {
			vui->vui_shared += VM_PAGE_SIZE;
		}
	}
}

/*===========================================================================*
 *				get_region_info				     *
 *===========================================================================*/
int get_region_info(struct vmproc *vmp, struct vm_region_info *vri,
	int max, vir_bytes *nextp)
{
	struct vir_region *vr;
	vir_bytes next;
	int count = 0;
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

	while (vr && count < max) {
		struct phys_region *first_phys = NULL;
		struct phys_region *last_phys = NULL;
		vir_bytes voffset;

		next = vr->vaddr + vr->length;

		for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
			struct phys_region *ph = physblock_get(vr, voffset);
			if (ph) {
				if (!first_phys) {
					first_phys = ph;
				}
				last_phys = ph;
			}
		}

		if (first_phys && last_phys) {
			vri[count].vri_addr = vr->vaddr + first_phys->offset;
			vri[count].vri_prot = PROT_READ;
			vri[count].vri_length = last_phys->offset + VM_PAGE_SIZE - first_phys->offset;

			if (vr->flags & VR_WRITABLE) {
				vri[count].vri_prot |= PROT_WRITE;
			}
			count++;
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
	
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while((vr = region_get_iter(&v_iter))) {
		region_incr_iter(&v_iter);
		
		if(vr->flags & VR_DIRECT) {
			continue;
		}
		
		for(vir_bytes voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
			pr = physblock_get(vr, voffset);
			if(pr == NULL) {
				continue;
			}
			
			used += VM_PAGE_SIZE;
			
			if(pr->ph != NULL && pr->ph->refcount > 0) {
				weighted += VM_PAGE_SIZE / pr->ph->refcount;
			}
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
	
	while ((vr = region_get_iter(&iter))) {
		USE(vr, vr->parent = vmp;);
		region_incr_iter(&iter);
	}
}

unsigned int physregions(struct vir_region *vr)
{
	unsigned int n = 0;
	vir_bytes voffset = 0;
	
	if (!vr) {
		return 0;
	}
	
	while (voffset < vr->length) {
		if (physblock_get(vr, voffset)) {
			n++;
		}
		voffset += VM_PAGE_SIZE;
	}
	
	return n;
}
