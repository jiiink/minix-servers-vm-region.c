
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
	if (vr == NULL) {
		return;
	}

	const char *memtype_name_val = "N/A";
	if (vr->def_memtype != NULL) {
		if (vr->def_memtype->name != NULL) {
			memtype_name_val = vr->def_memtype->name;
		} else {
			memtype_name_val = "(null_name)";
		}
	}

	printf("map_printmap: map_name: %s\n", memtype_name_val);
	printf("\t%lx (len 0x%lx, %lukB), %s, %s\n",
		vr->vaddr, vr->length, (unsigned long)vr->length / 1024,
		memtype_name_val,
		(vr->flags & VR_WRITABLE) ? "writable" : "readonly");

	printf("\t\tphysblocks:\n");

	if (VM_PAGE_SIZE == 0) {
		/* This is an exceptional condition for a system constant. */
		/* Log or handle error if appropriate, for now, just stop. */
		return;
	}

	unsigned long num_pages = vr->length / VM_PAGE_SIZE;

	if (vr->physblocks == NULL) {
		printf("\t\t(no physical blocks array)\n");
		return;
	}

	for (unsigned int i = 0; i < num_pages; i++) {
		struct phys_region *ph = vr->physblocks[i];

		if (ph == NULL) {
			continue;
		}

		const char *writable_status = "R"; /* Default to Readonly */
		if (vr->parent != NULL) {
			if (pt_writable(vr->parent, vr->vaddr + ph->offset)) {
				writable_status = "W";
			}
		} /* else: vr->parent is NULL, can't determine writability, "R" is safe default */

		if (ph->ph != NULL) {
			printf("\t\t@ %lx (refs %d): phys 0x%lx, %s\n",
				(vr->vaddr + ph->offset),
				ph->ph->refcount, ph->ph->phys,
				writable_status);
		} else {
			printf("\t\t@ %lx (refs N/A): phys N/A, %s (missing physical page info)\n",
				(vr->vaddr + ph->offset),
				writable_status);
		}
	}
}

struct phys_region *physblock_get(struct vir_region *region, vir_bytes offset)
{
    if (region == NULL) {
        return NULL;
    }

    if (offset % VM_PAGE_SIZE != 0) {
        return NULL;
    }

    if (offset >= region->length) {
        return NULL;
    }

    size_t page_idx = (size_t)(offset / VM_PAGE_SIZE);

    struct phys_region *found_region = region->physblocks[page_idx];

    if (found_region != NULL && found_region->offset != offset) {
        return NULL;
    }

    return found_region;
}

#include <stddef.h>
#include <stdlib.h>

void physblock_set(struct vir_region *region, vir_bytes offset,
                   struct phys_region *newphysr)
{
    if (region == NULL) {
        abort();
    }

    if (offset % VM_PAGE_SIZE != 0) {
        abort();
    }

    if (offset >= region->length) {
        abort();
    }

    struct vmproc *proc = region->parent;
    if (proc == NULL) {
        abort();
    }

    size_t page_index = offset / VM_PAGE_SIZE;

    if (newphysr) {
        if (region->physblocks[page_index] != NULL) {
            abort();
        }

        if (newphysr->offset != offset) {
            abort();
        }

        proc->vm_total += VM_PAGE_SIZE;

        if (proc->vm_total > proc->vm_total_max) {
            proc->vm_total_max = proc->vm_total;
        }
    } else {
        if (region->physblocks[page_index] == NULL) {
            abort();
        }
        proc->vm_total -= VM_PAGE_SIZE;
    }

    region->physblocks[page_index] = newphysr;
}

/*===========================================================================*
 *				map_printmap				     *
 *===========================================================================*/
void map_printmap(const struct vmproc *vmp)
{
	if (vmp == NULL) {
		fprintf(stderr, "Error: map_printmap received a NULL process pointer.\n");
		return;
	}

	struct vir_region *vr;
	region_iter iter;

	printf("memory regions in process %d:\n", vmp->vm_endpoint);

	region_start_iter_least(&vmp->vm_regions_avl, &iter);
	while((vr = region_get_iter(&iter))) {
		map_printregion(vr);
		region_incr_iter(&iter);
	}
}

static struct vir_region *getnextvr(struct vir_region *vr)
{
    struct vir_region *current_from_iter;
    struct vir_region *nextvr;
    region_iter v_iter;

    if (vr == NULL) {
        return NULL;
    }

    SLABSANE(vr);

    if (vr->parent == NULL) {
        return NULL;
    }

    region_start_iter(&vr->parent->vm_regions_avl, &v_iter, vr->vaddr, AVL_EQUAL);

    current_from_iter = region_get_iter(&v_iter);
    if (current_from_iter == NULL) {
        return NULL;
    }
    if (current_from_iter != vr) {
        return NULL;
    }

    region_incr_iter(&v_iter);
    nextvr = region_get_iter(&v_iter);

    if (nextvr == NULL) {
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
	if (vr == NULL || pr == NULL || pr->memtype == NULL || pr->memtype->writable == NULL) {
		/*
		 * One or more required pointers are NULL. This indicates invalid input.
		 * For a check function, the safest behavior is to return 'false' (0)
		 * as the region cannot be definitively determined to be writable.
		 * This prevents potential NULL pointer dereferences that would
		 * otherwise lead to crashes, especially when assertions are disabled.
		 */
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
	struct phys_block *pb = pr->ph;

	assert(vr);
	assert(pr);
	assert(pb);

	assert(!(vr->vaddr % VM_PAGE_SIZE));
	assert(!(pr->offset % VM_PAGE_SIZE));
	assert(pb->refcount > 0);

	if (pr_writable(vr, pr)) {
		flags |= PTF_WRITE;
	} else {
		flags |= PTF_READ;
	}

	if (vr->def_memtype && vr->def_memtype->pt_flags) {
		flags |= vr->def_memtype->pt_flags(vr);
	}

	int writemap_flags = 0;
#if SANITYCHECKS
	if (pr->written) {
		writemap_flags = WMF_OVERWRITE;
	}
#endif

	if (pt_writemap(vmp, &vmp->vm_pt, vr->vaddr + pr->offset,
	                pb->phys, VM_PAGE_SIZE, flags,
	                writemap_flags) != OK) {
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
static vir_bytes find_slot_in_gap_with_heuristic(vir_bytes gap_min, vir_bytes gap_max,
                                                 vir_bytes search_min_v, vir_bytes search_max_v,
                                                 vir_bytes length)
{
    vir_bytes effective_gap_start = (gap_min > search_min_v) ? gap_min : search_min_v;
    vir_bytes effective_gap_end = (gap_max < search_max_v) ? gap_max : search_max_v;

    if (effective_gap_end <= effective_gap_start ||
        (effective_gap_end - effective_gap_start) < length) {
        return SLOT_FAIL;
    }

    vir_bytes start_candidate = SLOT_FAIL;

    vir_bytes inner_try_start = effective_gap_start + VM_PAGE_SIZE;
    vir_bytes inner_try_end = effective_gap_end - VM_PAGE_SIZE;

    if (inner_try_end > inner_try_start && (inner_try_end - inner_try_start) >= length) {
        start_candidate = inner_try_end - length;
        if (start_candidate < effective_gap_start || (start_candidate + length) > effective_gap_end) {
            start_candidate = SLOT_FAIL;
        }
    }

    if (start_candidate == SLOT_FAIL) {
        start_candidate = effective_gap_end - length;
        if (start_candidate < effective_gap_start || (start_candidate + length) > effective_gap_end) {
            start_candidate = SLOT_FAIL;
        }
    }

    return start_candidate;
}

static vir_bytes region_find_slot_range(struct vmproc *vmp,
		vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
	struct vir_region *iterator_position_region;
	vir_bytes startv = SLOT_FAIL;
	region_iter iter;

	SANITYCHECK(SCL_FUNCTIONS);

	if (length == 0 || (length % VM_PAGE_SIZE) != 0) {
		return SLOT_FAIL;
	}

	vir_bytes effective_maxv = maxv;

	if (effective_maxv == 0) {
		effective_maxv = minv + length;
		if (effective_maxv <= minv) { /* Catches overflow of minv + length */
			return SLOT_FAIL;
		}
	}

	if (minv >= effective_maxv) {
		return SLOT_FAIL;
	}

	if (minv > (effective_maxv - length)) { /* Check if minv + length would exceed effective_maxv or overflow */
		return SLOT_FAIL;
	}

	region_start_iter(&vmp->vm_regions_avl, &iter, effective_maxv, AVL_GREATER_EQUAL);
	iterator_position_region = region_get_iter(&iter);

	if (!iterator_position_region) {
		region_start_iter(&vmp->vm_regions_avl, &iter, effective_maxv, AVL_LESS);
		iterator_position_region = region_get_iter(&iter);

		startv = find_slot_in_gap_with_heuristic(
            iterator_position_region ? iterator_position_region->vaddr + iterator_position_region->length : 0,
            VM_DATATOP,
            minv,
            effective_maxv,
            length
        );
	}

	struct vir_region *current_region;
	while (startv == SLOT_FAIL && (current_region = region_get_iter(&iter)) != NULL) {
		struct vir_region *prev_region;
		
		region_decr_iter(&iter);
		prev_region = region_get_iter(&iter);

		vir_bytes gap_start = prev_region ? prev_region->vaddr + prev_region->length : 0;
		vir_bytes gap_end = current_region->vaddr;

		startv = find_slot_in_gap_with_heuristic(gap_start, gap_end, minv, effective_maxv, length);
	}

	if (startv == SLOT_FAIL) {
		return SLOT_FAIL;
	}

	/* Post-conditions for found slot. */
	assert(startv >= minv);
	assert(startv < effective_maxv);
	assert(startv + length <= effective_maxv);

	vmp->vm_region_top = startv + length;

	return startv;
}

/*===========================================================================*
 *				region_find_slot			     *
 *===========================================================================*/
static vir_bytes region_find_slot(struct vmproc *vmp,
		vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
	vir_bytes hint = vmp->vm_region_top;
	vir_bytes found_v;

	if (maxv != 0 && hint < maxv && hint >= minv) {
		found_v = region_find_slot_range(vmp, minv, hint, length);

		if (found_v != SLOT_FAIL) {
			return found_v;
		}
	}

	return region_find_slot_range(vmp, minv, maxv, length);
}

static inline unsigned int phys_slot(vir_bytes len)
{
    assert(VM_PAGE_SIZE > 0);
    assert(!(len % VM_PAGE_SIZE));
    assert(len / VM_PAGE_SIZE <= UINT_MAX);
    return (unsigned int)(len / VM_PAGE_SIZE);
}

#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdatomic.h>

static _Atomic u32_t global_region_id = 0;

static struct vir_region *region_new(struct vmproc *vmp, vir_bytes startv, vir_bytes length,
	int flags, mem_type_t *memtype)
{
	struct vir_region *newregion = NULL;
	struct phys_region **newphysregions = NULL;
	int slots;

    if (length == 0) {
        fprintf(stderr, "VM: region_new: region length cannot be zero.\n");
        return NULL;
    }

    slots = phys_slot(length);

    if (slots <= 0) {
        fprintf(stderr, "VM: region_new: invalid or zero physical slots calculated for length %zu.\n", length);
        return NULL;
    }

	if (!(SLABALLOC(newregion))) {
		fprintf(stderr, "VM: region_new: failed to allocate new region structure.\n");
		return NULL;
	}

	memset(newregion, 0, sizeof(*newregion));
	newregion->vaddr = startv;
	newregion->length = length;
	newregion->flags = flags;
	newregion->def_memtype = memtype;
	newregion->remaps = 0;
	newregion->id = atomic_fetch_add(&global_region_id, 1);
	newregion->lower = NULL;
	newregion->higher = NULL;
	newregion->parent = vmp;

	newphysregions = calloc((size_t)slots, sizeof(struct phys_region *));
	if (newphysregions == NULL) {
		fprintf(stderr, "VM: region_new: failed to allocate physical block array.\n");
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

	assert(!(length % VM_PAGE_SIZE));

	SANITYCHECK(SCL_FUNCTIONS);

	startv = region_find_slot(vmp, minv, maxv, length);
	if (startv == SLOT_FAIL) {
		return NULL;
	}

	newregion = region_new(vmp, startv, length, flags, memtype);
	if (newregion == NULL) {
		printf("VM: map_page_region: allocating region failed\n");
		return NULL;
	}

	if (newregion->def_memtype->ev_new) {
		if (newregion->def_memtype->ev_new(newregion) != OK) {
			return NULL;
		}
	}

	if (mapflags & MF_PREALLOC) {
		if (map_handle_memory(vmp, newregion, 0, length, 1,
			NULL, 0, 0) != OK) {
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
		if((nextvr = getnextvr(newregion))) {
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
	vir_bytes end = start + len;
	vir_bytes voffset;

#if SANITYCHECKS
	SLABSANE(region);
	for(voffset = 0; voffset < phys_slot(region->length);
		voffset += VM_PAGE_SIZE) {
		struct phys_region *others;
		struct phys_block *pb;

		if(!(pr = physblock_get(region, voffset)))
			continue;

		pb = pr->ph;

		for(others = pb->firstregion; others;
			others = others->next_ph_list) {
			assert(others->ph == pb);
		}
	}
#endif

	for(voffset = start; voffset < end; voffset += VM_PAGE_SIZE) {
		pr = physblock_get(region, voffset);
		if (pr == NULL) {
			continue;
		}

		if (pr->offset < start || pr->offset >= end) {
			return 1;
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
    if (region == NULL) {
        return -1; // Indicate error for NULL input region
    }

    int result;

    result = map_subfree(region, 0, region->length);
    if (result != OK) {
        return result;
    }

    if (region->def_memtype != NULL && region->def_memtype->ev_delete != NULL) {
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

	while((r = region_search_root(&vmp->vm_regions_avl))) {
		SANITYCHECK(SCL_DETAIL);
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

	r = region_search(&vmp->vm_regions_avl, offset, AVL_LESS_EQUAL);

	if (r != NULL) {
		if (offset >= r->vaddr && offset < r->vaddr + r->length) {
			vir_bytes ph = offset - r->vaddr;
			if (physr != NULL) {
				*physr = physblock_get(r, ph);
			}
			return r;
		}
	}

	return NULL;
}

u32_t vrallocflags(u32_t flags)
{
    u32_t allocflags = 0;

    allocflags |= (flags & VR_PHYS64K) ? PAF_ALIGN64K : 0;
    allocflags |= (flags & VR_LOWER16MB) ? PAF_LOWER16MB : 0;
    allocflags |= (flags & VR_LOWER1MB) ? PAF_LOWER1MB : 0;
    allocflags |= (!(flags & VR_UNINITIALIZED)) ? PAF_CLEAR : 0;

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
	struct phys_region *ph = NULL;
	struct phys_block *pb = NULL;
	int r = OK;
	bool ph_newly_allocated = false;

	offset -= offset % VM_PAGE_SIZE;

	assert(offset < region->length);
	assert(!(region->vaddr % VM_PAGE_SIZE));
	assert(!(write && !(region->flags & VR_WRITABLE)));

	SANITYCHECK(SCL_FUNCTIONS);

	ph = physblock_get(region, offset);
	if (!ph) {
		// New block.
		pb = pb_new(MAP_NONE);
		if (!pb) {
			printf("map_pf: pb_new failed\n");
			return ENOMEM;
		}

		ph = pb_reference(pb, offset, region,
			region->def_memtype);
		if (!ph) {
			printf("map_pf: pb_reference failed\n");
			pb_free(pb); // Free the newly created phys_block
			return ENOMEM;
		}
		ph_newly_allocated = true;
	}

	assert(ph);
	assert(ph->ph);
	assert(ph->memtype); // Ensure memtype pointer is valid
	assert(ph->memtype->writable); // Ensure writable function pointer is valid

	// If we're writing and the block is not writable, or it's not a write operation,
	// trigger a page fault.
	if (!write || !ph->memtype->writable(ph)) {
		assert(ph->memtype->ev_pagefault); // Ensure ev_pagefault function pointer is valid
		assert(ph->ph);

		r = ph->memtype->ev_pagefault(vmp,
			region, ph, write, pf_callback, state, len, io);

		if (r == SUSPEND) {
			return SUSPEND;
		}

		if (r != OK) {
			// Handle pagefault failure. Only unreference if this function created the ph.
			if (ph_newly_allocated) {
				pb_unreferenced(region, ph, 1);
			}
			return r;
		}

		assert(ph);
		assert(ph->ph);
		assert(ph->ph->phys != MAP_NONE);
	}

	assert(ph->ph);
	assert(ph->ph->phys != MAP_NONE);

	// Map the physical page into the VM's page table.
	if ((r = map_ph_writept(vmp, region, ph)) != OK) {
		printf("map_pf: writept failed\n");
		// If map_ph_writept fails, and we created 'ph', we must unreference it
		// to prevent resource leaks.
		if (ph_newly_allocated) {
			pb_unreferenced(region, ph, 1);
		}
		return r;
	}

	SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
	if (OK != pt_checkrange(&vmp->vm_pt, region->vaddr + offset,
		VM_PAGE_SIZE, write)) {
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
	int r;
	int io = 0;

	if (length == 0) {
		return -1;
	}

	vir_bytes max_vir_bytes_val = (vir_bytes) -1;
	if (start_offset > max_vir_bytes_val - length) {
		return -2;
	}
	vir_bytes lim = start_offset + length;

	for(offset = start_offset; offset < lim; offset += VM_PAGE_SIZE) {
		if((r = map_pf(vmp, region, offset, write,
		   cb, state, statelen, &io)) != OK) {
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

	pt_assert(&vmp->vm_pt);

	region_start_iter_least(&vmp->vm_regions_avl, &iter);

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
	if (vr == NULL) {
		return NULL;
	}

	struct vir_region *newvr = region_new(vr->parent, vr->vaddr, vr->length, vr->flags, vr->def_memtype);
	if (newvr == NULL) {
		return NULL;
	}

	newvr->parent = vmp;

	if (vr->def_memtype != NULL && vr->def_memtype->ev_copy != NULL) {
		int copy_result = vr->def_memtype->ev_copy(vr, newvr);
		if (copy_result != OK) {
			map_free(newvr);
			printf("VM: memtype-specific copy failed (%d)\n", copy_result);
			return NULL;
		}
	}

	for (vir_bytes p_slot_idx = 0; p_slot_idx < phys_slot(vr->length); ++p_slot_idx) {
		struct phys_region *ph = physblock_get(vr, p_slot_idx * VM_PAGE_SIZE);

		if (ph == NULL) {
			continue;
		}

		struct phys_region *newph = pb_reference(ph->ph, ph->offset, newvr, vr->def_memtype);
		if (newph == NULL) {
			map_free(newvr);
			return NULL;
		}

		if (ph->memtype != NULL && ph->memtype->ev_reference != NULL) {
			ph->memtype->ev_reference(ph, newph);
		}

#if SANITYCHECKS
		newph->written = 0;
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
		printf("VM: copy_abs2region: invalid destination region parameter.\n");
		return EFAULT;
	}

	while (len > 0) {
		struct phys_region *ph;
		phys_bytes current_page_offset;
		phys_bytes bytes_to_process;

		ph = physblock_get(destregion, offset);
		if (!ph) {
			printf("VM: copy_abs2region: no phys region found (1).\n");
			return EFAULT;
		}

		if (offset < ph->offset || offset >= ph->offset + VM_PAGE_SIZE) {
			printf("VM: copy_abs2region: no phys region found (2).\n");
			return EFAULT;
		}

		current_page_offset = offset - ph->offset;

		phys_bytes remaining_in_current_page = VM_PAGE_SIZE - current_page_offset;
		bytes_to_process = (len < remaining_in_current_page) ? len : remaining_in_current_page;

		if (ph->ph->refcount != 1) {
			printf("VM: copy_abs2region: refcount not 1.\n");
			return EFAULT;
		}

		if (sys_abscopy(absaddr, ph->ph->phys + current_page_offset, bytes_to_process) != OK) {
			printf("VM: copy_abs2region: abscopy failed.\n");
			return EFAULT;
		}

		absaddr += bytes_to_process;
		offset += bytes_to_process;
		len -= bytes_to_process;
	}

	return OK;
}

/*=========================================================================*
 *				map_writept				*
 *=========================================================================*/
static int process_virtual_region_pages(struct vmproc *vmp, struct vir_region *vr)
{
	vir_bytes p;
	for (p = 0; p < vr->length; p += VM_PAGE_SIZE) {
		struct phys_region *ph = physblock_get(vr, p);
		if (!ph) {
			continue;
		}

		int r = map_ph_writept(vmp, vr, ph);
		if (r != OK) {
			printf("VM: map_writept: failed\n");
			return r;
		}
	}
	return OK;
}

int map_writept(struct vmproc *vmp)
{
	region_iter v_iter;
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	struct vir_region *vr;
	while ((vr = region_get_iter(&v_iter))) {
		int r = process_virtual_region_pages(vmp, vr);
		if (r != OK) {
			return r;
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
    int ret;

    ret = region_init(&dst->vm_regions_avl);
    if (ret != 0) {
        return ret;
    }

    ret = map_proc_copy_range(dst, src, NULL, NULL);
    return ret;
}

/*========================================================================*
 *			     map_proc_copy_range			     	  *
 *========================================================================*/
int map_proc_copy_range(struct vmproc *dst, struct vmproc *src,
	struct vir_region *start_src_vr, struct vir_region *end_src_vr)
{
	struct vir_region *vr;
	region_iter v_iter;
	struct vir_region *effective_start_vr = start_src_vr;
	struct vir_region *effective_end_vr = end_src_vr;
	int ret = OK;

	if (effective_start_vr == NULL) {
		effective_start_vr = region_search_least(&src->vm_regions_avl);
	}

	if (effective_end_vr == NULL) {
		effective_end_vr = region_search_greatest(&src->vm_regions_avl);
	}

	if (effective_start_vr == NULL || effective_end_vr == NULL) {
		return OK;
	}

	if (effective_start_vr->parent != src) {
		return EINVAL;
	}

	region_start_iter(&src->vm_regions_avl, &v_iter, effective_start_vr->vaddr, AVL_EQUAL);

	assert(region_get_iter(&v_iter) == effective_start_vr);

	SANITYCHECK(SCL_FUNCTIONS);

	while ((vr = region_get_iter(&v_iter))) {
		struct vir_region *newvr;

		if (!(newvr = map_copy_region(dst, vr))) {
			ret = ENOMEM;
			break;
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
				if (!orig_ph) { assert(!new_ph); continue; }
				assert(new_ph);
				assert(orig_ph != new_ph);
				assert(orig_ph->ph == new_ph->ph);
			}
		}
#endif
		if (vr == effective_end_vr) {
			break;
		}

		region_incr_iter(&v_iter);
	}

	if (ret != OK) {
		map_free_proc(dst);
		return ret;
	}

	map_writept(src);
	map_writept(dst);

	SANITYCHECK(SCL_FUNCTIONS);
	return ret;
}

int map_region_extend_upto_v(struct vmproc *vmp, vir_bytes v)
{
	vir_bytes target_aligned_v;
	vir_bytes current_region_limit;
	vir_bytes extension_length;
	struct vir_region *vr;
	struct vir_region *next_vr;
	struct phys_region **new_phys_blocks;
	int current_phys_slots;
	int new_phys_slots;
	int added_phys_slots;
	int result;

	target_aligned_v = roundup(v, VM_PAGE_SIZE);

	vr = region_search(&vmp->vm_regions_avl, target_aligned_v, AVL_LESS);
	if (!vr) {
		printf("VM: map_region_extend_upto_v: No region found to extend.\n");
		return ENOMEM;
	}

	current_region_limit = vr->vaddr + vr->length;
	if (current_region_limit >= v) {
		return OK;
	}

	extension_length = target_aligned_v - current_region_limit;
	if (extension_length <= 0) {
		printf("VM: map_region_extend_upto_v: Internal logic error, extension length not positive.\n");
		return EINVAL;
	}

	next_vr = getnextvr(vr);
	if (next_vr && next_vr->vaddr < target_aligned_v) {
		printf("VM: map_region_extend_upto_v: Cannot grow into next region.\n");
		return ENOMEM;
	}

	if (!vr->def_memtype->ev_resize) {
		result = map_page_region(vmp, current_region_limit, 0, extension_length,
		                         VR_WRITABLE | VR_ANON, 0, &mem_type_anon);
		if (result != OK) {
			printf("VM: map_region_extend_upto_v: Couldn't map anonymous memory for extension.\n");
			return ENOMEM;
		}
		return OK;
	}

	new_phys_slots = phys_slot(target_aligned_v - vr->vaddr);
	current_phys_slots = phys_slot(vr->length);

	if (new_phys_slots < current_phys_slots) {
		printf("VM: map_region_extend_upto_v: Internal logic error, new physical slots less than current.\n");
		return EINVAL;
	}

	added_phys_slots = new_phys_slots - current_phys_slots;

	new_phys_blocks = realloc(vr->physblocks, (size_t)new_phys_slots * sizeof(struct phys_region *));
	if (!new_phys_blocks) {
		printf("VM: map_region_extend_upto_v: Realloc failed for physical blocks.\n");
		return ENOMEM;
	}

	vr->physblocks = new_phys_blocks;

	if (added_phys_slots > 0) {
		memset(vr->physblocks + current_phys_slots, 0,
		       (size_t)added_phys_slots * sizeof(struct phys_region *));
	}

	result = vr->def_memtype->ev_resize(vmp, vr, target_aligned_v - vr->vaddr);

	return result;
}

/*========================================================================*
 *				map_unmap_region	     	  	*
 *========================================================================*/
int map_unmap_region(struct vmproc *vmp, struct vir_region *r,
	vir_bytes offset, vir_bytes len)
{
	vir_bytes regionstart;
	int freed_slots_count = phys_slot(len);

	if (offset + len > r->length || (len % VM_PAGE_SIZE) != 0) {
		printf("VM: map_unmap_region: bogus length or unaligned: offset 0x%lx, len 0x%lx, r->length 0x%lx\n",
			(unsigned long)offset, (unsigned long)len, (unsigned long)r->length);
		return EINVAL;
	}

	regionstart = r->vaddr + offset;

	map_subfree(r, offset, len);

	if (r->length == len) {
		region_remove(&vmp->vm_regions_avl, r->vaddr);
		map_free(r);
	} else if (offset == 0) {
		struct phys_region *pr;
		vir_bytes voffset_old;
		vir_bytes old_r_vaddr = r->vaddr;
		vir_bytes old_r_length = r->length;

		if (!r->def_memtype->ev_lowshrink) {
			printf("VM: map_unmap_region: low-shrinking not implemented for %s\n",
				r->def_memtype->name);
			return EINVAL;
		}

		if (r->def_memtype->ev_lowshrink(r, len) != OK) {
			printf("VM: map_unmap_region: low-shrinking failed for %s\n",
				r->def_memtype->name);
			return EINVAL;
		}

		region_remove(&vmp->vm_regions_avl, old_r_vaddr);

		for (voffset_old = len; voffset_old < old_r_length; voffset_old += VM_PAGE_SIZE) {
			if (!(pr = physblock_get(r, voffset_old))) {
				continue;
			}
			pr->offset -= len;
		}

		r->vaddr += len;
		r->length -= len;

		region_insert(&vmp->vm_regions_avl, r);

		int remaining_slots_count = phys_slot(r->length);
		if (remaining_slots_count > 0) {
			memmove(r->physblocks, r->physblocks + freed_slots_count,
				remaining_slots_count * sizeof(struct phys_region *));
		}
	} else if (offset + len == r->length) {
		r->length -= len;
	}

	if (pt_writemap(vmp, &vmp->vm_pt, regionstart,
	  MAP_NONE, len, 0, WMF_OVERWRITE) != OK) {
	    printf("VM: map_unmap_region: pt_writemap failed for 0x%lx (len 0x%lx)\n",
			(unsigned long)regionstart, (unsigned long)len);
	    return ENOMEM;
	}

	return OK;
}

static int reference_phys_blocks(struct vir_region *source_vr,
                                 struct vir_region *target_vr, vir_bytes start_voffset) {
    vir_bytes voffset;
    for (voffset = 0; voffset < target_vr->length; voffset += VM_PAGE_SIZE) {
        struct phys_region *ph, *phn;
        if (!(ph = physblock_get(source_vr, start_voffset + voffset))) {
            continue;
        }
        if (!(phn = pb_reference(ph->ph, voffset, target_vr, ph->memtype))) {
            return ENOMEM;
        }
    }
    return OK;
}

static int split_region(struct vmproc *vmp, struct vir_region *vr,
	struct vir_region **vr1, struct vir_region **vr2, vir_bytes split_len)
{
	struct vir_region *r1 = NULL, *r2 = NULL;
	vir_bytes rem_len;
	int ret = OK;

    if (vmp == NULL || vr == NULL || vr1 == NULL || vr2 == NULL) {
        return EINVAL;
    }
    if (split_len == 0 || split_len >= vr->length) {
        return EINVAL;
    }
    if (split_len % VM_PAGE_SIZE != 0) {
        return EINVAL;
    }
    if (vr->vaddr % VM_PAGE_SIZE != 0) {
        return EINVAL;
    }
    if (vr->length % VM_PAGE_SIZE != 0) {
        return EINVAL;
    }

	rem_len = vr->length - split_len;
    if (rem_len == 0) {
        return EINVAL;
    }
    if (rem_len % VM_PAGE_SIZE != 0) {
        return EINVAL;
    }

	if (!vr->def_memtype || !vr->def_memtype->ev_split) {
		printf("VM: split region not implemented for %s\n",
			vr->def_memtype ? vr->def_memtype->name : "unknown_memtype");
		sys_diagctl_stacktrace(vmp->vm_endpoint);
		return EINVAL;
	}

	if (!(r1 = region_new(vmp, vr->vaddr, split_len, vr->flags,
		vr->def_memtype))) {
		ret = ENOMEM;
		goto cleanup;
	}

	if (!(r2 = region_new(vmp, vr->vaddr + split_len, rem_len, vr->flags,
		vr->def_memtype))) {
		ret = ENOMEM;
		goto cleanup;
	}

    if ((ret = reference_phys_blocks(vr, r1, 0)) != OK) {
        goto cleanup;
    }

    if ((ret = reference_phys_blocks(vr, r2, split_len)) != OK) {
        goto cleanup;
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
	if (r1) map_free(r1);
	if (r2) map_free(r2);

	printf("split_region: failed with error %d\n", ret);

	return ret;
}

#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define MIN(a, b) ((a) < (b) ? (a) : (b))

int map_unmap_range(struct vmproc *vmp, vir_bytes unmap_start_orig, vir_bytes length_orig)
{
    // 1. Normalize and validate the input unmap range
    vir_bytes offset_in_page = unmap_start_orig % VM_PAGE_SIZE;
    vir_bytes aligned_start = unmap_start_orig - offset_in_page;
    vir_bytes effective_length = length_orig + offset_in_page;
    vir_bytes aligned_length = roundup(effective_length, VM_PAGE_SIZE);
    vir_bytes unmap_end_exclusive = aligned_start + aligned_length;

    // Validate the aligned length. As per original, length less than a page is invalid.
    // This also handles cases where effective_length was 0 or negative, resulting in aligned_length = 0.
    if (aligned_length < VM_PAGE_SIZE) {
        return EINVAL;
    }

    // Safety check against potential vir_bytes overflow or an empty/inverted range
    if (unmap_end_exclusive <= aligned_start) {
        return EINVAL;
    }

    region_iter v_iter;
    struct vir_region *current_region;
    struct vir_region *next_region_in_tree;
    int result;

    // 2. Find the first relevant region in the AVL tree that might overlap
    // First, try to find a region that starts at or before `aligned_start`.
    region_start_iter(&vmp->vm_regions_avl, &v_iter, aligned_start, AVL_LESS_EQUAL);
    current_region = region_get_iter(&v_iter);

    // If no such region exists (meaning `aligned_start` is before the first region),
    // then find the very first region that starts after `aligned_start`.
    if (!current_region) {
        region_start_iter(&vmp->vm_regions_avl, &v_iter, aligned_start, AVL_GREATER);
        current_region = region_get_iter(&v_iter);
    }

    // If no regions are found at all, there's nothing to unmap.
    if (!current_region) {
        return OK;
    }

    // 3. Iterate through all regions that overlap with the unmap range
    // Loop continues as long as a current_region exists and its start address is before the unmap end.
    // Regions that are entirely before the unmap range or do not overlap will be filtered by the
    // overlap calculation inside the loop.
    for (; current_region && current_region->vaddr < unmap_end_exclusive; current_region = next_region_in_tree) {
        vir_bytes region_end_exclusive = current_region->vaddr + current_region->length;
        vir_bytes overlap_start;
        vir_bytes overlap_end_exclusive;
        vir_bytes unmap_portion_offset;
        vir_bytes unmap_portion_length;

        // Get the next region pointer *before* any modifications to `current_region`,
        // as `split_region` or `map_unmap_region` might invalidate `current_region` or the iterator.
        region_incr_iter(&v_iter);
        next_region_in_tree = region_get_iter(&v_iter);

        // Calculate the actual overlapping range between the unmap request and the current_region
        overlap_start = MAX(aligned_start, current_region->vaddr);
        overlap_end_exclusive = MIN(unmap_end_exclusive, region_end_exclusive);

        // If there's no actual overlap, or the overlap range is empty/invalid, skip to the next region.
        if (overlap_start >= overlap_end_exclusive) {
            continue;
        }

        // 4. Handle region splitting for "hole punching" scenarios
        // This condition identifies when the unmap range is strictly contained within current_region,
        // necessitating a split to preserve the leading and trailing parts.
        // Example: Region [A, D], unmap [B, C]. This splits [A, D] into [A, C] (new current_region) and [C, D] (left for next_region_in_tree).
        // Then map_unmap_region will handle unmapping [B, C] from [A, C], preserving [A, B].
        if (overlap_start > current_region->vaddr && overlap_end_exclusive < region_end_exclusive) {
            struct vir_region *left_part, *right_part;
            vir_bytes split_at_len = overlap_end_exclusive - current_region->vaddr;

            // Split the current region: `current_region` (original) is removed,
            // `left_part` ([current_region->vaddr, overlap_end_exclusive)) and
            // `right_part` ([overlap_end_exclusive, region_end_exclusive)) are added.
            result = split_region(vmp, current_region, &left_part, &right_part, split_at_len);
            if (result != OK) {
                return result;
            }
            // The `map_unmap_region` will now operate on the `left_part` of the split.
            current_region = left_part;
            // Update region_end_exclusive for the newly assigned `current_region`.
            region_end_exclusive = current_region->vaddr + current_region->length;
        }

        // Calculate the offset and length for the `map_unmap_region` call
        // relative to the start of the (potentially new) `current_region`.
        unmap_portion_offset = overlap_start - current_region->vaddr;
        unmap_portion_length = overlap_end_exclusive - overlap_start;

        // 5. Perform the actual unmapping operation on the identified portion of the region
        result = map_unmap_region(vmp, current_region, unmap_portion_offset, unmap_portion_length);
        if (result != OK) {
            return result;
        }

        // 6. Re-synchronize iterator state defensively
        // If tree modifications (insertions/deletions by split_region or map_unmap_region)
        // might have invalidated the iterator's internal state, this re-sync ensures it's
        // correctly positioned for `next_region_in_tree` in the next loop iteration.
        if (next_region_in_tree) {
            region_start_iter(&vmp->vm_regions_avl, &v_iter, next_region_in_tree->vaddr, AVL_EQUAL);
        }
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

	vr = map_lookup(vmp, addr, NULL);

	if (!vr) {
		return EINVAL;
	}

	if (vr->vaddr != addr) {
		return EINVAL;
	}

	if (!vr->def_memtype || !vr->def_memtype->regionid) {
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
	if (vui == ((void *)0)) {
		return;
	}

	memset(vui, 0, sizeof(*vui));
	vui->vui_total = kernel_boot_info.kernel_allocated_bytes +
		kernel_boot_info.kernel_allocated_bytes_dynamic;
	vui->vui_virtual = vui->vui_mvirtual = vui->vui_total;
}

static void get_usage_info_vm(struct vm_usage_info *vui)
{
	if (vui == NULL) {
		return;
	}

	memset(vui, 0, sizeof(*vui));
	vui->vui_total = kernel_boot_info.vm_allocated_bytes +
		get_vm_self_pages() * VM_PAGE_SIZE;
	vui->vui_virtual = vui->vui_mvirtual = vui->vui_total;
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
	struct vir_region *vr;
	struct phys_region *physical_block;
	region_iter v_iter;
	vir_bytes voffset;

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
			physical_block = physblock_get(vr, voffset);

			if (physical_block == NULL) {
				/* mvirtual: discount unmapped stack pages. */
				if (is_stack_region(vr)) {
					vui->vui_mvirtual -= VM_PAGE_SIZE;
				}
				continue;
			}

			/* All present pages are counted towards the total. */
			vui->vui_total += VM_PAGE_SIZE;

			if (physical_block->ph->refcount > 1) {
				/* Any page with a refcount > 1 is common. */
				vui->vui_common += VM_PAGE_SIZE;
	
				/* Any common, non-COW page is shared. */
				if (vr->flags & VR_SHARED) {
					vui->vui_shared += VM_PAGE_SIZE;
				}
			}
		}
		region_incr_iter(&v_iter);
	}

	/* Also include getrusage resource information. */
	vui->vui_maxrss = vmp->vm_total_max / 1024L;
	vui->vui_minflt = vmp->vm_minor_page_fault;
	vui->vui_majflt = vmp->vm_major_page_fault;
}

/*===========================================================================*
 *				get_region_info				     *
 *===========================================================================*/
int get_region_info(struct vmproc *vmp, struct vm_region_info *vri_out,
	int max_entries, vir_bytes *nextp)
{
	struct vir_region *vr;
	vir_bytes next_addr_for_next_call;
	int entries_found = 0;
	region_iter v_iter;

	next_addr_for_next_call = *nextp;

	if (!max_entries) {
        return 0;
    }

	region_start_iter(&vmp->vm_regions_avl, &v_iter, next_addr_for_next_call, AVL_GREATER_EQUAL);

	for (vr = region_get_iter(&v_iter);
         vr != NULL && entries_found < max_entries;
         region_incr_iter(&v_iter))
    {
		struct phys_region *ph1 = NULL, *ph2 = NULL;
		vir_bytes voffset;

		next_addr_for_next_call = vr->vaddr + vr->length;

		for(voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
			struct phys_region *ph = physblock_get(vr, voffset);
			if(ph == NULL) {
                continue;
            }
			if(ph1 == NULL) {
                ph1 = ph;
            }
			ph2 = ph;
		}

		if(ph1 == NULL || ph2 == NULL) {
			printf("skipping empty region 0x%lx-0x%lx\n",
				vr->vaddr, vr->vaddr + vr->length);
			continue;
		}

		vri_out->vri_addr = vr->vaddr + ph1->offset;
		vri_out->vri_prot = PROT_READ;
		vri_out->vri_length = ph2->offset + VM_PAGE_SIZE - ph1->offset;

		if (vr->flags & VR_WRITABLE) {
			vri_out->vri_prot |= PROT_WRITE;
        }

		entries_found++;
		vri_out++;
	}

	*nextp = next_addr_for_next_call;
	return entries_found;
}

/*========================================================================*
 *				regionprintstats			  *
 *========================================================================*/
void printregionstats(struct vmproc *vmp)
{
    static const unsigned int KB_SCALE = 1024;

    struct vir_region *current_virtual_region;
    struct phys_region *corresponding_physical_region;
    vir_bytes total_used_bytes = 0;
    vir_bytes total_weighted_bytes = 0;
    region_iter region_iterator;

    region_start_iter_least(&vmp->vm_regions_avl, &region_iterator);

    while ((current_virtual_region = region_get_iter(&region_iterator))) {
        region_incr_iter(&region_iterator);

        if (current_virtual_region->flags & VR_DIRECT) {
            continue;
        }

        for (vir_bytes voffset = 0; voffset < current_virtual_region->length; voffset += VM_PAGE_SIZE) {
            corresponding_physical_region = physblock_get(current_virtual_region, voffset);

            if (!corresponding_physical_region) {
                continue;
            }

            total_used_bytes += VM_PAGE_SIZE;

            unsigned int refcount = corresponding_physical_region->ph->refcount;

            if (refcount == 0) {
                refcount = 1;
            }

            total_weighted_bytes += VM_PAGE_SIZE / refcount;
        }
    }

    printf("%6lukB  %6lukB\n", total_used_bytes / KB_SCALE, total_weighted_bytes / KB_SCALE);
}

void map_setparent(struct vmproc *vmp)
{
	if (vmp == NULL) {
		return;
	}

	region_iter iter;
	struct vir_region *vr;
        region_start_iter_least(&vmp->vm_regions_avl, &iter);
        while((vr = region_get_iter(&iter))) {
                vr->parent = vmp;
                region_incr_iter(&iter);
        }
}

unsigned int physregions(struct vir_region *vr)
{
	if (vr == NULL) {
		return 0;
	}

	unsigned int n = 0;
	vir_bytes voffset;

	for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
		if (physblock_get(vr, voffset)) {
			n++;
		}
	}

	return n;
}
