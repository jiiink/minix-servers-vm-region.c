
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
    unsigned long vaddr, length, kbytes, pages, addr, phys;
    const char *name;
    unsigned long i;
    int writable, refcount;
    struct phys_region *ph;

    if (!vr || !vr->def_memtype) {
        return;
    }

    name = vr->def_memtype->name ? vr->def_memtype->name : "(null)";
    printf("map_printmap: map_name: %s\n", name);

    vaddr = (unsigned long)vr->vaddr;
    length = (unsigned long)vr->length;
    kbytes = length / 1024UL;

    printf("\t%lx (len 0x%lx, %lukB), %p, %s\n",
           vaddr, length, kbytes,
           (void *)vr->def_memtype->name,
           (vr->flags & VR_WRITABLE) ? "writable" : "readonly");

    printf("\t\tphysblocks:\n");

    if (!vr->physblocks) {
        return;
    }

    pages = (VM_PAGE_SIZE != 0) ? (length / (unsigned long)VM_PAGE_SIZE) : 0UL;

    for (i = 0; i < pages; i++) {
        ph = vr->physblocks[i];
        if (!ph || !ph->ph) {
            continue;
        }

        addr = vaddr + (unsigned long)ph->offset;
        phys = (unsigned long)ph->ph->phys;
        refcount = ph->ph->refcount;

        writable = 0;
        if (vr->parent) {
            writable = pt_writable(vr->parent, addr) ? 1 : 0;
        }

        printf("\t\t@ %lx (refs %d): phys 0x%lx, %s\n",
               addr, refcount, phys, writable ? "W" : "R");
    }
}

struct phys_region *physblock_get(struct vir_region *region, vir_bytes offset)
{
	struct phys_region *result;
	int index;

	assert(region != NULL);
	assert(region->physblocks != NULL);
	assert(!(offset % VM_PAGE_SIZE));
	assert(offset < region->length);

	index = (int)(offset / VM_PAGE_SIZE);
	result = region->physblocks[index];

	if (result != NULL) {
		assert(result->offset == offset);
	}

	return result;
}

void physblock_set(struct vir_region *region, vir_bytes offset, struct phys_region *newphysr)
{
	size_t i;
	struct vmproc *proc;
	struct phys_region **slot;

	assert(region != NULL);
	assert((offset % VM_PAGE_SIZE) == 0);
	assert(offset < region->length);

	i = (size_t)(offset / VM_PAGE_SIZE);
	proc = region->parent;
	assert(proc != NULL);

	slot = &region->physblocks[i];

	if (newphysr != NULL) {
		assert(*slot == NULL);
		assert(newphysr->offset == offset);
		proc->vm_total += VM_PAGE_SIZE;
		if (proc->vm_total > proc->vm_total_max) {
			proc->vm_total_max = proc->vm_total;
		}
	} else {
		assert(*slot != NULL);
		proc->vm_total -= VM_PAGE_SIZE;
	}

	*slot = newphysr;
}

/*===========================================================================*
 *				map_printmap				     *
 *===========================================================================*/
void map_printmap(struct vmproc *vmp)
{
	if (vmp == NULL) {
		return;
	}

	printf("memory regions in process %d:\n", vmp->vm_endpoint);

	region_iter iter;
	struct vir_region *vr;

	region_start_iter_least(&vmp->vm_regions_avl, &iter);
	for (;;) {
		vr = region_get_iter(&iter);
		if (vr == NULL) {
			break;
		}
		map_printregion(vr);
		region_incr_iter(&iter);
	}
}

static struct vir_region *getnextvr(struct vir_region *vr)
{
	struct vir_region *curvr;
	struct vir_region *nextvr;
	region_iter v_iter;

	if (vr == NULL || vr->parent == NULL) {
		return NULL;
	}

	SLABSANE(vr);

	region_start_iter(&vr->parent->vm_regions_avl, &v_iter, vr->vaddr, AVL_EQUAL);

	curvr = region_get_iter(&v_iter);
	if (!curvr || curvr != vr) {
		assert(curvr);
		assert(curvr == vr);
		return NULL;
	}

	region_incr_iter(&v_iter);
	nextvr = region_get_iter(&v_iter);
	if (!nextvr) {
		return NULL;
	}

	SLABSANE(nextvr);
	assert(vr->parent == nextvr->parent);
	assert(vr->vaddr < nextvr->vaddr);
	assert(nextvr->vaddr >= vr->vaddr && (nextvr->vaddr - vr->vaddr) >= vr->length);

	return nextvr;
}

static int pr_writable(struct vir_region *vr, struct phys_region *pr)
{
	if (vr == NULL || pr == NULL || pr->memtype == NULL || pr->memtype->writable == NULL) {
		return 0;
	}

	if ((vr->flags & VR_WRITABLE) == 0) {
		return 0;
	}

	return pr->memtype->writable(pr) ? 1 : 0;
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
int map_ph_writept(struct vmproc *vmp, struct vir_region *vr, struct phys_region *pr)
{
	assert(vr);
	assert(pr);

	struct phys_block *pb = pr->ph;

	assert(pb);
	assert(!(vr->vaddr % VM_PAGE_SIZE));
	assert(!(pr->offset % VM_PAGE_SIZE));
	assert(pb->refcount > 0);

	int flags = PTF_PRESENT | PTF_USER | (pr_writable(vr, pr) ? PTF_WRITE : PTF_READ);

	if (vr->def_memtype && vr->def_memtype->pt_flags)
		flags |= vr->def_memtype->pt_flags(vr);

#if SANITYCHECKS
	int wmf = pr->written ? WMF_OVERWRITE : 0;
#else
	int wmf = WMF_OVERWRITE;
#endif

	if (pt_writemap(vmp, &vmp->vm_pt, vr->vaddr + pr->offset,
		pb->phys, VM_PAGE_SIZE, flags, wmf) != OK) {
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
static int try_free_vrange(vir_bytes rangestart, vir_bytes rangeend,
                           vir_bytes minv, vir_bytes maxv,
                           vir_bytes length, vir_bytes *out_startv)
{
    vir_bytes frstart = rangestart;
    vir_bytes frend = rangeend;

    if (frstart < minv) frstart = minv;
    if (frend > maxv)  frend = maxv;

    if (frend > frstart && (frend - frstart) >= length) {
        *out_startv = frend - length;
        return 1;
    }

    return 0;
}

static int find_free_vrange(vir_bytes start, vir_bytes end,
                            vir_bytes minv, vir_bytes maxv,
                            vir_bytes length, vir_bytes *out_startv)
{
    if (try_free_vrange(start + VM_PAGE_SIZE, end - VM_PAGE_SIZE,
                        minv, maxv, length, out_startv)) {
        return 1;
    }

    return try_free_vrange(start, end, minv, maxv, length, out_startv);
}

static vir_bytes region_find_slot_range(struct vmproc *vmp,
		vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
	struct vir_region *lastregion;
	vir_bytes startv = 0;
	int found = 0;
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
		found = find_free_vrange(
			lastregion ? lastregion->vaddr + lastregion->length : 0,
			VM_DATATOP, minv, maxv, length, &startv);
	}

	if(!found) {
		struct vir_region *vr;
		while((vr = region_get_iter(&iter))) {
			struct vir_region *nextvr;
			region_decr_iter(&iter);
			nextvr = region_get_iter(&iter);
			if (find_free_vrange(
				nextvr ? nextvr->vaddr + nextvr->length : 0,
				vr->vaddr, minv, maxv, length, &startv)) {
				found = 1;
				break;
			}
		}
	}

	if(!found) {
		return SLOT_FAIL;
	}

	assert(startv >= minv);
	assert(startv < maxv);
	assert(startv + length <= maxv);

	vmp->vm_region_top = startv + length;

	return startv;
}

/*===========================================================================*
 *				region_find_slot			     *
 *===========================================================================*/
static vir_bytes region_find_slot(struct vmproc *vmp,
    vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
    const vir_bytes hint = vmp->vm_region_top;

    if (maxv != 0 && hint >= minv && hint < maxv) {
        vir_bytes result = region_find_slot_range(vmp, minv, hint, length);
        if (result != SLOT_FAIL) {
            return result;
        }
    }

    return region_find_slot_range(vmp, minv, maxv, length);
}

static unsigned int phys_slot(vir_bytes len)
{
	assert(VM_PAGE_SIZE != 0);
	assert((len % VM_PAGE_SIZE) == 0);
	const vir_bytes pages = len / VM_PAGE_SIZE;
	return (unsigned int)pages;
}

static struct vir_region *region_new(struct vmproc *vmp, vir_bytes startv, vir_bytes length,
	int flags, mem_type_t *memtype)
{
	struct vir_region *newregion;
	struct phys_region **newphysregions = NULL;
	static u32_t id;
	int slots = phys_slot(length);

	if (slots < 0) {
		printf("VM: region_new: invalid phys slot count\n");
		return NULL;
	}

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
		newregion->lower = NULL;
		newregion->higher = NULL;
		newregion->parent = vmp;
	);

	if (slots > 0) {
		newphysregions = calloc((size_t)slots, sizeof(struct phys_region *));
		if (!newphysregions) {
			printf("VM: region_new: allocating phys blocks failed\n");
			SLABFREE(newregion);
			return NULL;
		}
	}

	USE(newregion, newregion->physblocks = newphysregions;);

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

	assert(!(length % VM_PAGE_SIZE));

	SANITYCHECK(SCL_FUNCTIONS);

	startv = region_find_slot(vmp, minv, maxv, length);
	if (startv == SLOT_FAIL)
		return NULL;

	newregion = region_new(vmp, startv, length, flags, memtype);
	if (!newregion) {
		printf("VM: map_page_region: allocating region failed\n");
		return NULL;
	}

	if (!newregion->def_memtype) {
		printf("VM: map_page_region: missing memtype\n");
		map_free(newregion);
		return NULL;
	}

	if (newregion->def_memtype->ev_new) {
		int r = newregion->def_memtype->ev_new(newregion);
		if (r != OK) {
			return NULL;
		}
	}

	if (mapflags & MF_PREALLOC) {
		int r = map_handle_memory(vmp, newregion, 0, length, 1, NULL, 0, 0);
		if (r != OK) {
			printf("VM: map_page_region: prealloc failed\n");
			map_free(newregion);
			return NULL;
		}
	}

	newregion->flags &= ~VR_UNINITIALIZED;

	region_insert(&vmp->vm_regions_avl, newregion);

#if SANITYCHECKS
	assert(startv == newregion->vaddr);
	{
		struct vir_region *nextvr;
		if ((nextvr = getnextvr(newregion))) {
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
static int map_subfree(struct vir_region *region, vir_bytes start, vir_bytes len)
{
	struct phys_region *pr;
	vir_bytes voffset;
	const vir_bytes page = VM_PAGE_SIZE;

	if (!region) return EINVAL;
	if (page == 0) return EINVAL;
	if (len == 0) return OK;

#if SANITYCHECKS
	SLABSANE(region);
	for (voffset = 0; voffset < phys_slot(region->length); voffset += page) {
		struct phys_region *others;
		struct phys_block *pb;

		pr = physblock_get(region, voffset);
		if (!pr) continue;

		pb = pr->ph;

		for (others = pb->firstregion; others; others = others->next_ph_list) {
			assert(others->ph == pb);
		}
	}
#endif

	for (voffset = start; (voffset - start) < len; voffset += page) {
		pr = physblock_get(region, voffset);
		if (!pr) continue;

		assert(pr->offset >= start);
		assert((pr->offset - start) < len);

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
	int r = map_subfree(region, 0, region->length);
	if (r != OK) {
		printf("%d\n", __LINE__);
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
	struct vir_region *region = region_search_root(&vmp->vm_regions_avl);

	while (region != NULL) {
		SANITYCHECK(SCL_DETAIL);
#if SANITYCHECKS
		nocheck++;
#endif
		region_remove(&vmp->vm_regions_avl, region->vaddr);
		map_free(region);
#if SANITYCHECKS
		nocheck--;
#endif
		SANITYCHECK(SCL_DETAIL);

		region = region_search_root(&vmp->vm_regions_avl);
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

	SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
	if(!region_search_root(&vmp->vm_regions_avl))
		panic("process has no regions: %d", vmp->vm_endpoint);
#endif

	r = region_search(&vmp->vm_regions_avl, offset, AVL_LESS_EQUAL);
	if (r && offset >= r->vaddr) {
		vir_bytes rel = offset - r->vaddr;
		if (rel < r->length) {
			if (physr) {
				*physr = physblock_get(r, rel);
				if (*physr) assert((*physr)->offset == rel);
			}
			return r;
		}
	}

	SANITYCHECK(SCL_FUNCTIONS);

	return NULL;
}

u32_t vrallocflags(const u32_t flags)
{
	u32_t allocflags = 0U;

	if ((flags & VR_PHYS64K) != 0U) {
		allocflags |= PAF_ALIGN64K;
	}
	if ((flags & VR_LOWER16MB) != 0U) {
		allocflags |= PAF_LOWER16MB;
	}
	if ((flags & VR_LOWER1MB) != 0U) {
		allocflags |= PAF_LOWER1MB;
	}
	if ((flags & VR_UNINITIALIZED) == 0U) {
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
	int r = OK;

	offset -= offset % VM_PAGE_SIZE;
	assert(offset < region->length);
	assert(!(region->vaddr % VM_PAGE_SIZE));
	assert(!(write && !(region->flags & VR_WRITABLE)));

	SANITYCHECK(SCL_FUNCTIONS);

	ph = physblock_get(region, offset);
	if (!ph) {
		struct phys_block *pb = pb_new(MAP_NONE);
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

	assert(ph);
	assert(ph->ph);
	assert(ph->memtype && ph->memtype->writable);

	if (!write || !ph->memtype->writable(ph)) {
		assert(ph->memtype->ev_pagefault);

		r = ph->memtype->ev_pagefault(vmp, region, ph, write,
			pf_callback, state, len, io);
		if (r == SUSPEND) {
			return SUSPEND;
		}
		if (r != OK) {
			if (ph) pb_unreferenced(region, ph, 1);
			return r;
		}

		assert(ph);
		assert(ph->ph);
		assert(ph->ph->phys != MAP_NONE);
	}

	assert(ph->ph);
	assert(ph->ph->phys != MAP_NONE);

	r = map_ph_writept(vmp, region, ph);
	if (r != OK) {
		printf("map_pf: writept failed\n");
		return r;
	}

	SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
	if (OK != pt_checkrange(&vmp->vm_pt, region->vaddr + offset,
		VM_PAGE_SIZE, write)) {
		panic("map_pf: pt_checkrange failed: %d", r);
	}
#endif

	return OK;
}

int map_handle_memory(struct vmproc *vmp,
	struct vir_region *region, vir_bytes start_offset, vir_bytes length,
	int write, vfs_callback_t cb, void *state, int statelen)
{
	vir_bytes offset, lim;
	int r;
	int io = 0;
	const int do_write = write ? 1 : 0;

	if (vmp == NULL || region == NULL || length == 0)
		return EINVAL;

	lim = start_offset + length;
	if (lim < start_offset)
		return EOVERFLOW;

	offset = start_offset;
	while (offset < lim) {
		r = map_pf(vmp, region, offset, do_write, cb, state, statelen, &io);
		if (r != OK)
			return r;

		{
			vir_bytes rem = lim - offset;
			vir_bytes step = (rem < VM_PAGE_SIZE) ? rem : VM_PAGE_SIZE;
			vir_bytes next = offset + step;
			if (next < offset)
				return EOVERFLOW;
			offset = next;
		}
	}

	return OK;
}

/*===========================================================================*
 *				map_pin_memory      			     *
 *===========================================================================*/
int map_pin_memory(struct vmproc *vmp)
{
	region_iter iter;
	struct vir_region *vr;
	int r;

	if (vmp == NULL) {
		panic("map_pin_memory: vmp is NULL");
	}

	pt_assert(&vmp->vm_pt);

	region_start_iter_least(&vmp->vm_regions_avl, &iter);

	for (; (vr = region_get_iter(&iter)) != NULL; region_incr_iter(&iter)) {
		r = map_handle_memory(vmp, vr, 0, vr->length, 1, NULL, 0, 0);
		if (r != OK) {
		    panic("map_pin_memory: map_handle_memory failed: %d", r);
		}
	}

	pt_assert(&vmp->vm_pt);
	return OK;
}

/*===========================================================================*
 *				map_copy_region			     	*
 *===========================================================================*/
struct vir_region *map_copy_region(struct vmproc *vmp, struct vir_region *vr)
{
	struct vir_region *newvr = NULL;
	struct phys_region *ph;
	int r;
	vir_bytes slot;

	if (!vmp || !vr) return NULL;

#if SANITYCHECKS
	{
		unsigned int cr = physregions(vr);
#endif

	newvr = region_new(vr->parent, vr->vaddr, vr->length, vr->flags, vr->def_memtype);
	if (!newvr) return NULL;

	newvr->parent = vmp;

	if (vr->def_memtype->ev_copy) {
		r = vr->def_memtype->ev_copy(vr, newvr);
		if (r != OK) {
			map_free(newvr);
			printf("VM: memtype-specific copy failed (%d)\n", r);
			return NULL;
		}
	}

	for (slot = 0; slot < phys_slot(vr->length); slot++) {
		struct phys_region *newph;

		ph = physblock_get(vr, slot * VM_PAGE_SIZE);
		if (!ph) continue;

		newph = pb_reference(ph->ph, ph->offset, newvr, vr->def_memtype);
		if (!newph) {
			map_free(newvr);
			return NULL;
		}

		if (ph->memtype->ev_reference)
			ph->memtype->ev_reference(ph, newph);

#if SANITYCHECKS
		newph->written = 0;
		assert(physregions(vr) == cr);
#endif
	}

#if SANITYCHECKS
	assert(physregions(vr) == physregions(newvr));
	}
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
		phys_bytes sublen, suboffset, page_left;
		struct phys_region *ph;

		ph = physblock_get(destregion, offset);
		if (!ph || !ph->ph) {
			printf("VM: copy_abs2region: no phys region found (1).\n");
			return EFAULT;
		}

		if (offset < ph->offset) {
			printf("VM: copy_abs2region: no phys region found (2).\n");
			return EFAULT;
		}

		suboffset = offset - ph->offset;
		if (suboffset >= VM_PAGE_SIZE) {
			printf("VM: copy_abs2region: no phys region found (2).\n");
			return EFAULT;
		}

		page_left = VM_PAGE_SIZE - suboffset;
		sublen = (len < page_left) ? len : page_left;

		if (ph->ph->refcount != 1) {
			printf("VM: copy_abs2region: refcount not 1.\n");
			return EFAULT;
		}

		if (sys_abscopy(absaddr, ph->ph->phys + suboffset, sublen) != OK) {
			printf("VM: copy_abs2region: abscopy failed.\n");
			return EFAULT;
		}

		if (absaddr > (phys_bytes)(~(phys_bytes)0) - sublen ||
		    offset > (phys_bytes)(~(phys_bytes)0) - sublen) {
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
	region_iter v_iter;
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	for (;;) {
		struct vir_region *vr = region_get_iter(&v_iter);
		if (!vr) break;

		for (vir_bytes p = 0; p < vr->length; p += VM_PAGE_SIZE) {
			struct phys_region *ph = physblock_get(vr, p);
			if (!ph) continue;

			int r = map_ph_writept(vmp, vr, ph);
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
	if (dst == NULL || src == NULL) {
		return EINVAL;
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
	struct vir_region *vr = NULL;
	region_iter v_iter;

	if (!start_src_vr)
		start_src_vr = region_search_least(&src->vm_regions_avl);
	if (!end_src_vr)
		end_src_vr = region_search_greatest(&src->vm_regions_avl);

	assert(start_src_vr && end_src_vr);
	assert(start_src_vr->parent == src);
	assert(end_src_vr->parent == src);

	region_start_iter(&src->vm_regions_avl, &v_iter, start_src_vr->vaddr, AVL_EQUAL);
	assert(region_get_iter(&v_iter) == start_src_vr);

	SANITYCHECK(SCL_FUNCTIONS);

	for (;;) {
		struct vir_region *newvr;

		vr = region_get_iter(&v_iter);
		if (!vr)
			break;

		newvr = map_copy_region(dst, vr);
		if (!newvr) {
			map_free_proc(dst);
			return ENOMEM;
		}

		region_insert(&dst->vm_regions_avl, newvr);
		assert(vr->length == newvr->length);

#if SANITYCHECKS
		{
			vir_bytes vaddr;
			struct phys_region *orig_ph, *new_ph;

			assert(vr->physblocks != newvr->physblocks);

			for (vaddr = 0; vaddr < vr->length; vaddr += VM_PAGE_SIZE) {
				orig_ph = physblock_get(vr, vaddr);
				new_ph = physblock_get(newvr, vaddr);
				if (!orig_ph) {
					assert(!new_ph);
					continue;
				}
				assert(new_ph);
				assert(orig_ph != new_ph);
				assert(orig_ph->ph == new_ph->ph);
			}
		}
#endif

		if (vr == end_src_vr)
			break;

		region_incr_iter(&v_iter);
	}

	map_writept(src);
	map_writept(dst);

	SANITYCHECK(SCL_FUNCTIONS);
	return OK;
}

int map_region_extend_upto_v(struct vmproc *vmp, vir_bytes v)
{
	if (vmp == NULL) return EINVAL;

	vir_bytes offset = roundup(v, VM_PAGE_SIZE);

	struct vir_region *vr = region_search(&vmp->vm_regions_avl, offset, AVL_LESS);
	if (!vr) {
		printf("VM: nothing to extend\n");
		return ENOMEM;
	}

	if (vr->vaddr + vr->length >= v) return OK;

	vir_bytes limit = vr->vaddr + vr->length;
	if (limit < vr->vaddr) {
		printf("VM: invalid region size\n");
		return ENOMEM;
	}

	if (vr->vaddr > offset) {
		printf("VM: region lookup mismatch\n");
		return ENOMEM;
	}

	int newslots = phys_slot(offset - vr->vaddr);
	int prevslots = phys_slot(vr->length);
	if (newslots < prevslots) {
		printf("VM: slot calculation error\n");
		return ENOMEM;
	}

	int addedslots = newslots - prevslots;
	vir_bytes extralen = offset - limit;
	if (extralen == 0) return OK;
	if (offset < limit) {
		printf("VM: invalid extension length\n");
		return ENOMEM;
	}

	struct vir_region *nextvr = getnextvr(vr);
	if (nextvr && nextvr->vaddr < offset) {
		printf("VM: can't grow into next region\n");
		return ENOMEM;
	}

	if (!vr->def_memtype || !vr->def_memtype->ev_resize) {
		if (!map_page_region(vmp, limit, 0, extralen, VR_WRITABLE | VR_ANON, 0, &mem_type_anon)) {
			printf("resize: couldn't put anon memory there\n");
			return ENOMEM;
		}
		return OK;
	}

	size_t newsize = (size_t)newslots * sizeof(struct phys_region *);
	if (newslots > 0 && newsize / sizeof(struct phys_region *) != (size_t)newslots) {
		printf("VM: map_region_extend_upto_v: size overflow\n");
		return ENOMEM;
	}

	struct phys_region **newpr = realloc(vr->physblocks, newsize);
	if (!newpr) {
		printf("VM: map_region_extend_upto_v: realloc failed\n");
		return ENOMEM;
	}

	vr->physblocks = newpr;
	if (addedslots > 0) {
		memset(vr->physblocks + prevslots, 0,
		       (size_t)addedslots * sizeof(struct phys_region *));
	}

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

	if (!vmp || !r) {
		return EINVAL;
	}

	if ((len % VM_PAGE_SIZE) != 0 || offset > r->length - len) {
		printf("VM: bogus length 0x%lx\n", len);
		return EINVAL;
	}

	freeslots = phys_slot(len);
	regionstart = r->vaddr + offset;

	/* unreference its memory */
	map_subfree(r, offset, len);

	/* if unmap was at start/end of this region, it actually shrinks */
	if (r->length == len) {
		/* Whole region disappears. Unlink and free it. */
		region_remove(&vmp->vm_regions_avl, r->vaddr);
		map_free(r);
	} else if (offset == 0) {
		struct phys_region *pr;
		vir_bytes voffset;
		int remslots;

		if (!r->def_memtype) {
			printf("VM: low-shrinking not implemented for <null>\n");
			return EINVAL;
		}

		if (!r->def_memtype->ev_lowshrink) {
			printf("VM: low-shrinking not implemented for %s\n",
				r->def_memtype->name);
			return EINVAL;
		}

		if (r->def_memtype->ev_lowshrink(r, len) != OK) {
			printf("VM: low-shrinking failed for %s\n",
				r->def_memtype->name);
			return EINVAL;
		}

		region_remove(&vmp->vm_regions_avl, r->vaddr);

		r->vaddr += len;

		remslots = phys_slot(r->length);

		region_insert(&vmp->vm_regions_avl, r);

		/* vaddr has increased; to make all the phys_regions
		 * point to the same addresses, make them shrink by the
		 * same amount.
		 */
		for (voffset = len; voffset < r->length; voffset += VM_PAGE_SIZE) {
			pr = physblock_get(r, voffset);
			if (!pr) continue;
			assert(pr->offset >= offset);
			assert(pr->offset >= len);
			pr->offset -= len;
		}
		if (remslots > 0)
			memmove(r->physblocks, r->physblocks + freeslots,
				(size_t)remslots * sizeof(struct phys_region *));
		r->length -= len;
	} else if (offset + len == r->length) {
		assert(len <= r->length);
		r->length -= len;
	}

	SANITYCHECK(SCL_DETAIL);

	if (pt_writemap(vmp, &vmp->vm_pt, regionstart,
	  MAP_NONE, len, 0, WMF_OVERWRITE) != OK) {
	    printf("VM: map_unmap_region: pt_writemap failed\n");
	    return ENOMEM;
	}

	SANITYCHECK(SCL_FUNCTIONS);

	return OK;
}

static int ref_phys_subrange(struct vir_region *src, vir_bytes start_off,
    struct vir_region *dst, vir_bytes len)
{
    vir_bytes off;

    for (off = 0; off < len; off += VM_PAGE_SIZE) {
        struct phys_region *ph;
        if (!(ph = physblock_get(src, start_off + off)))
            continue;
        if (!pb_reference(ph->ph, off, dst, ph->memtype))
            return ENOMEM;
    }

    return OK;
}

static int split_region(struct vmproc *vmp, struct vir_region *vr,
    struct vir_region **vr1, struct vir_region **vr2, vir_bytes split_len)
{
    struct vir_region *r1 = NULL, *r2 = NULL;
    vir_bytes rem_len;

    if (!vmp || !vr || !vr1 || !vr2)
        return EINVAL;

    if (!vr->def_memtype || !vr->def_memtype->ev_split) {
        printf("VM: split region not implemented for %s\n",
            vr->def_memtype ? vr->def_memtype->name : "(null)");
        sys_diagctl_stacktrace(vmp->vm_endpoint);
        return EINVAL;
    }

    if ((vr->vaddr % VM_PAGE_SIZE) || (vr->length % VM_PAGE_SIZE) ||
        (split_len % VM_PAGE_SIZE) || split_len == 0 || split_len >= vr->length)
        return EINVAL;

    rem_len = vr->length - split_len;

    r1 = region_new(vmp, vr->vaddr, split_len, vr->flags, vr->def_memtype);
    if (!r1)
        goto bail;

    r2 = region_new(vmp, vr->vaddr + split_len, rem_len, vr->flags, vr->def_memtype);
    if (!r2) {
        map_free(r1);
        r1 = NULL;
        goto bail;
    }

    if (ref_phys_subrange(vr, 0, r1, r1->length) != OK)
        goto bail;

    if (ref_phys_subrange(vr, split_len, r2, r2->length) != OK)
        goto bail;

    vr->def_memtype->ev_split(vmp, vr, r1, r2);

    region_remove(&vmp->vm_regions_avl, vr->vaddr);
    map_free(vr);
    region_insert(&vmp->vm_regions_avl, r1);
    region_insert(&vmp->vm_regions_avl, r2);

    *vr1 = r1;
    *vr2 = r2;

    return OK;

bail:
    if (r1) map_free(r1);
    if (r2) map_free(r2);

    printf("split_region: failed\n");

    return ENOMEM;
}

int map_unmap_range(struct vmproc *vmp, vir_bytes unmap_start, vir_bytes length)
{
	const vir_bytes page_size = VM_PAGE_SIZE;
	const vir_bytes page_mask = VM_PAGE_SIZE - 1;
	vir_bytes offset, unmap_limit;
	region_iter v_iter;
	struct vir_region *vr, *nextvr;

	offset = unmap_start % page_size;

	if (length > (vir_bytes)-1 - offset) return EINVAL;
	length += offset;

	if (length > (vir_bytes)-1 - page_mask) return EINVAL;
	length = roundup(length, page_size);

	if (length < page_size) return EINVAL;

	if (length > (vir_bytes)-1 - unmap_start) return EINVAL;
	unmap_limit = unmap_start + length;

	region_start_iter(&vmp->vm_regions_avl, &v_iter, unmap_start, AVL_LESS_EQUAL);
	vr = region_get_iter(&v_iter);
	if (!vr) {
		region_start_iter(&vmp->vm_regions_avl, &v_iter, unmap_start, AVL_GREATER);
		vr = region_get_iter(&v_iter);
		if (!vr) return OK;
	}

	for (; vr && vr->vaddr < unmap_limit; vr = nextvr) {
		vir_bytes region_end = vr->vaddr + vr->length;
		vir_bytes this_unmap_start, this_unmap_limit;
		int r;

		region_incr_iter(&v_iter);
		nextvr = region_get_iter(&v_iter);

		assert(region_end > vr->vaddr);

		this_unmap_start = MAX(unmap_start, vr->vaddr);
		this_unmap_limit = MIN(unmap_limit, region_end);

		if (this_unmap_start >= this_unmap_limit) {
			continue;
		}

		if (this_unmap_start > vr->vaddr && this_unmap_limit < region_end) {
			struct vir_region *vr1, *vr2;
			vir_bytes split_len = this_unmap_limit - vr->vaddr;

			assert(split_len > 0);
			assert(split_len < vr->length);

			r = split_region(vmp, vr, &vr1, &vr2, split_len);
			if (r != OK) {
				printf("VM: unmap split failed\n");
				return r;
			}

			vr = vr1;
			region_end = vr->vaddr + vr->length;
		}

		assert(this_unmap_start >= vr->vaddr);
		assert(this_unmap_limit <= region_end);
		assert(this_unmap_limit - this_unmap_start > 0);

		{
			vir_bytes offset_in_region = this_unmap_start - vr->vaddr;
			vir_bytes len_in_region = this_unmap_limit - this_unmap_start;

			r = map_unmap_region(vmp, vr, offset_in_region, len_in_region);
			if (r != OK) {
				printf("map_unmap_range: map_unmap_region failed\n");
				return r;
			}
		}

		if (nextvr) {
			region_start_iter(&vmp->vm_regions_avl, &v_iter, nextvr->vaddr, AVL_EQUAL);
			assert(region_get_iter(&v_iter) == nextvr);
		}
	}

	return OK;
}

/*========================================================================*
 *			  map_region_lookup_type			  *
 *========================================================================*/
struct vir_region* map_region_lookup_type(struct vmproc *vmp, u32_t type)
{
    if (vmp == NULL) {
        return NULL;
    }

    region_iter iter;
    struct vir_region *vr;

    for (region_start_iter_least(&vmp->vm_regions_avl, &iter);
         (vr = region_get_iter(&iter)) != NULL;
         region_incr_iter(&iter)) {
        if ((vr->flags & type) != 0) {
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
	struct vir_region *vr = map_lookup(vmp, addr, NULL);

	if (vr == NULL)
		return EINVAL;

	if (vr->vaddr != addr)
		return EINVAL;

	if (vr->def_memtype == NULL || vr->def_memtype->refcount == NULL)
		return EINVAL;

	if (cnt != NULL)
		*cnt = vr->def_memtype->refcount(vr);

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
    vui->vui_total = kernel_boot_info.vm_allocated_bytes +
                     get_vm_self_pages() * VM_PAGE_SIZE;
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
is_stack_region(struct vir_region *vr)
{
	if (vr == NULL) {
		return 0;
	}

	return (vr->vaddr == VM_STACKTOP - DEFAULT_STACK_LIMIT &&
	    vr->length == DEFAULT_STACK_LIMIT) ? 1 : 0;
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
	const vir_bytes page_size = VM_PAGE_SIZE;

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
	for (vr = region_get_iter(&v_iter); vr != NULL; region_incr_iter(&v_iter), vr = region_get_iter(&v_iter)) {
		const vir_bytes vlen = vr->length;
		const int is_stack = is_stack_region(vr);
		const int is_shared = (vr->flags & VR_SHARED) != 0;

		vui->vui_virtual += vlen;
		vui->vui_mvirtual += vlen;

		if (page_size == 0) {
			continue;
		}

		for (voffset = 0; voffset < vlen; voffset += page_size) {
			ph = physblock_get(vr, voffset);
			if (!ph) {
				if (is_stack) {
					vui->vui_mvirtual -= page_size;
				}
				continue;
			}

			vui->vui_total += page_size;

			if (ph->ph && ph->ph->refcount > 1) {
				vui->vui_common += page_size;

				if (is_shared) {
					vui->vui_shared += page_size;
				}
			}
		}
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
	region_iter v_iter;
	struct vir_region *vr;
	vir_bytes next;
	int count;

	if (!vmp || !vri || !nextp || max <= 0) return 0;

	next = *nextp;

	region_start_iter(&vmp->vm_regions_avl, &v_iter, next, AVL_GREATER_EQUAL);

	count = 0;
	while (count < max && (vr = region_get_iter(&v_iter)) != NULL) {
		struct phys_region *ph_first = NULL, *ph_last = NULL;
		vir_bytes voffset;

		next = vr->vaddr + vr->length;

		for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
			struct phys_region *ph = physblock_get(vr, voffset);
			if (!ph) continue;
			if (!ph_first) ph_first = ph;
			ph_last = ph;
		}

		if (ph_first && ph_last) {
			vir_bytes start = vr->vaddr + ph_first->offset;
			vir_bytes length = (ph_last->offset - ph_first->offset) + VM_PAGE_SIZE;

			vri->vri_addr = start;
			vri->vri_prot = PROT_READ;
			vri->vri_length = length;

			if (vr->flags & VR_WRITABLE) vri->vri_prot |= PROT_WRITE;

			vri++;
			count++;
		} else {
			printf("skipping empty region 0x%lx-0x%lx\n",
				(unsigned long)vr->vaddr, (unsigned long)(vr->vaddr + vr->length));
		}

		region_incr_iter(&v_iter);
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
	vir_bytes used = 0;
	vir_bytes weighted = 0;
	region_iter v_iter;

	if (!vmp)
		return;

	if (VM_PAGE_SIZE == 0)
		return;

	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while ((vr = region_get_iter(&v_iter)) != NULL) {
		vir_bytes voffset;

		region_incr_iter(&v_iter);

		if ((vr->flags & VR_DIRECT) != 0)
			continue;

		if (vr->length == 0)
			continue;

		for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
			int refcount;

			pr = physblock_get(vr, voffset);
			if (pr == NULL || pr->ph == NULL)
				continue;

			refcount = pr->ph->refcount;
			if (refcount <= 0)
				continue;

			used += VM_PAGE_SIZE;
			weighted += VM_PAGE_SIZE / (vir_bytes)refcount;
		}
	}

	{
		unsigned long used_kb = (unsigned long)(used / 1024);
		unsigned long weighted_kb = (unsigned long)(weighted / 1024);
		printf("%6lukB  %6lukB\n", used_kb, weighted_kb);
	}
}

void map_setparent(struct vmproc *vmp)
{
    region_iter iter;
    struct vir_region *vr;

    if (vmp == NULL) {
        return;
    }

    for (region_start_iter_least(&vmp->vm_regions_avl, &iter);
         (vr = region_get_iter(&iter)) != NULL;
         region_incr_iter(&iter)) {
        vr->parent = vmp;
    }
}

unsigned int physregions(struct vir_region *vr)
{
	if (vr == NULL || vr->length == 0) {
		return 0U;
	}

	unsigned int count = 0U;
	vir_bytes pages = vr->length / VM_PAGE_SIZE;
	if (vr->length % VM_PAGE_SIZE != 0) {
		pages++;
	}

	vir_bytes voffset = 0;
	vir_bytes i;
	for (i = 0; i < pages; i++) {
		if (physblock_get(vr, voffset) != 0) {
			count++;
		}
		voffset += VM_PAGE_SIZE;
	}

	return count;
}
