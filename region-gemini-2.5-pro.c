
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
    /* No initialization required for this mapping. */
}

static void map_printregion(struct vir_region *vr)
{
	if (!vr || !vr->def_memtype || !vr->physblocks) {
		return;
	}

	printf("map_printmap: map_name: %s\n", vr->def_memtype->name);

	const char *writable_str = (vr->flags & VR_WRITABLE) ? "writable" : "readonly";
	printf("\t%lx (len 0x%lx, %lukB), %s, %s\n",
		vr->vaddr, vr->length, vr->length / 1024,
		vr->def_memtype->name, writable_str);

	printf("\t\tphysblocks:\n");

	const size_t num_pages = vr->length / VM_PAGE_SIZE;
	for (size_t i = 0; i < num_pages; i++) {
		struct phys_region *ph = vr->physblocks[i];
		if (!ph || !ph->ph) {
			continue;
		}

		unsigned long current_vaddr = vr->vaddr + ph->offset;
		const char *pt_writable_str = pt_writable(vr->parent, current_vaddr) ? "W" : "R";

		printf("\t\t@ %lx (refs %d): phys 0x%lx, %s\n",
			current_vaddr,
			ph->ph->refcount,
			ph->ph->phys,
			pt_writable_str);
	}
}

#include <stddef.h>
#include <assert.h>

struct phys_region *physblock_get(struct vir_region *region, vir_bytes offset)
{
    if (!region || (offset % VM_PAGE_SIZE) != 0 || offset >= region->length) {
        return NULL;
    }

    size_t index = offset / VM_PAGE_SIZE;
    struct phys_region *phys_block = region->physblocks[index];

    if (phys_block) {
        assert(phys_block->offset == offset);
    }

    return phys_block;
}

void physblock_set(struct vir_region *region, vir_bytes offset,
                   struct phys_region *newphysr)
{
	assert(region != NULL);
	assert((offset % VM_PAGE_SIZE) == 0);
	assert(offset < region->length);

	struct vmproc *proc = region->parent;
	assert(proc != NULL);

	const size_t i = offset / VM_PAGE_SIZE;
	struct phys_region *oldphysr = region->physblocks[i];

	if (newphysr != NULL) {
		assert(oldphysr == NULL);
		assert(newphysr->offset == offset);

		proc->vm_total += VM_PAGE_SIZE;
		if (proc->vm_total > proc->vm_total_max) {
			proc->vm_total_max = proc->vm_total;
		}
	} else {
		assert(oldphysr != NULL);
		proc->vm_total -= VM_PAGE_SIZE;
	}

	region->physblocks[i] = newphysr;
}

/*===========================================================================*
 *				map_printmap				     *
 *===========================================================================*/
void map_printmap(struct vmproc *vmp)
{
	if (!vmp) {
		return;
	}

	printf("memory regions in process %d:\n", vmp->vm_endpoint);

	struct vir_region *vr;
	region_iter iter;

	for (region_start_iter_least(&vmp->vm_regions_avl, &iter);
	     (vr = region_get_iter(&iter)) != NULL;
	     region_incr_iter(&iter)) {
		map_printregion(vr);
	}
}

static struct vir_region *getnextvr(struct vir_region *vr)
{
	struct vir_region *nextvr;
	region_iter v_iter;

	if (!vr || !vr->parent) {
		return NULL;
	}

	SLABSANE(vr);

	region_start_iter(&vr->parent->vm_regions_avl, &v_iter, vr->vaddr, AVL_EQUAL);

	if (region_get_iter(&v_iter) != vr) {
		return NULL;
	}

	region_incr_iter(&v_iter);
	nextvr = region_get_iter(&v_iter);

	if (!nextvr) {
		return NULL;
	}

	SLABSANE(nextvr);

	if (vr->parent != nextvr->parent ||
	    vr->vaddr >= nextvr->vaddr ||
	    vr->length > nextvr->vaddr - vr->vaddr) {
		return NULL;
	}

	return nextvr;
}

static int pr_writable(struct vir_region *vr, struct phys_region *pr)
{
    if (!vr || !pr || !pr->memtype || !pr->memtype->writable) {
        return 0;
    }

    return (vr->flags & VR_WRITABLE) && pr->memtype->writable(pr);
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
	int page_table_flags = PTF_PRESENT | PTF_USER;
	struct phys_block *pb = pr->ph;
	int writemap_flags;

	assert(vr);
	assert(pr);
	assert(pb);
	assert(!(vr->vaddr % VM_PAGE_SIZE));
	assert(!(pr->offset % VM_PAGE_SIZE));
	assert(pb->refcount > 0);

	page_table_flags |= pr_writable(vr, pr) ? PTF_WRITE : PTF_READ;

	if (vr->def_memtype->pt_flags) {
		page_table_flags |= vr->def_memtype->pt_flags(vr);
	}

#if SANITYCHECKS
	writemap_flags = pr->written ? WMF_OVERWRITE : 0;
#else
	writemap_flags = WMF_OVERWRITE;
#endif

	if (pt_writemap(vmp, &vmp->vm_pt, vr->vaddr + pr->offset, pb->phys,
			VM_PAGE_SIZE, page_table_flags, writemap_flags) != OK) {
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
	vir_bytes startv = SLOT_FAIL;
	region_iter iter;
	struct vir_region *curr_region, *prev_region;

	SANITYCHECK(SCL_FUNCTIONS);

	assert(length > 0);
	assert((length % VM_PAGE_SIZE) == 0);

	if (maxv == 0) {
		maxv = minv + length;
		if (maxv <= minv) {
			printf("region_find_slot: minv 0x%lx and bytes 0x%lx\n",
				minv, length);
			return SLOT_FAIL;
		}
	}

	if (minv >= maxv || (maxv - minv) < length) {
		return SLOT_FAIL;
	}

	region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_GREATER_EQUAL);
	curr_region = region_get_iter(&iter);

	while (1) {
		vir_bytes gap_end = curr_region ? curr_region->vaddr : VM_DATATOP;

		if (curr_region) {
			region_decr_iter(&iter);
			prev_region = region_get_iter(&iter);
		} else {
			region_start_iter(&vmp->vm_regions_avl, &iter, 0, AVL_LAST);
			prev_region = region_get_iter(&iter);
		}
		vir_bytes gap_start = prev_region ? (prev_region->vaddr + prev_region->length) : 0;

		vir_bytes search_start = MAX(gap_start, minv);
		vir_bytes search_end = MIN(gap_end, maxv);

		if (search_end > search_start && (search_end - search_start) >= length) {
			vir_bytes try_start = search_start + VM_PAGE_SIZE;
			vir_bytes try_end = search_end - VM_PAGE_SIZE;

			if (try_end > try_start && (try_end - try_start) >= length) {
				startv = try_end - length;
			} else {
				startv = search_end - length;
			}
			break;
		}

		if (!prev_region) {
			break;
		}

		curr_region = prev_region;
	}

	if (startv == SLOT_FAIL) {
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
	vir_bytes hint = vmp->vm_region_top;

	if (maxv != 0 && hint >= minv && hint < maxv) {
		vir_bytes slot = region_find_slot_range(vmp, minv, hint, length);
		if (slot != SLOT_FAIL) {
			return slot;
		}
	}

	return region_find_slot_range(vmp, minv, maxv, length);
}

static unsigned int phys_slot(vir_bytes len)
{
    if ((len & (VM_PAGE_SIZE - 1)) != 0) {
        abort();
    }
    return len / VM_PAGE_SIZE;
}

static struct vir_region *region_new(struct vmproc *vmp, vir_bytes startv, vir_bytes length,
	int flags, mem_type_t *memtype)
{
	static u32_t next_id = 0;
	struct vir_region *new_region;
	struct phys_region **phys_blocks;
	int slots;

	slots = phys_slot(length);
	if (slots <= 0) {
		return NULL;
	}

	if (!SLABALLOC(new_region)) {
		return NULL;
	}

	phys_blocks = calloc((size_t)slots, sizeof(*phys_blocks));
	if (!phys_blocks) {
		SLABFREE(new_region);
		return NULL;
	}

	memset(new_region, 0, sizeof(*new_region));
	new_region->vaddr = startv;
	new_region->length = length;
	new_region->flags = flags;
	new_region->def_memtype = memtype;
	new_region->parent = vmp;
	new_region->physblocks = phys_blocks;
	new_region->id = next_id++;

	return new_region;
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
	if (!newregion) {
		printf("VM: map_page_region: allocating region failed\n");
		return NULL;
	}

	if (newregion->def_memtype->ev_new &&
	    newregion->def_memtype->ev_new(newregion) != OK) {
		/* ev_new will have freed and removed the region */
		return NULL;
	}

	if ((mapflags & MF_PREALLOC) &&
	    map_handle_memory(vmp, newregion, 0, length, 1, NULL, 0, 0) != OK) {
		printf("VM: map_page_region: prealloc failed\n");
		map_free(newregion);
		return NULL;
	}

	/* Pre-allocations should be uninitialized, but after that it's a
	 * different story.
	 */
	newregion->flags &= ~VR_UNINITIALIZED;

	region_insert(&vmp->vm_regions_avl, newregion);

#if SANITYCHECKS
	assert(startv == newregion->vaddr);
	struct vir_region *nextvr = getnextvr(newregion);
	if (nextvr) {
		assert(newregion->vaddr < nextvr->vaddr);
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
	if (!region) {
		return EINVAL;
	}

	if (len == 0) {
		return OK;
	}

	if (start > (vir_bytes)-1 - len) {
		return EINVAL;
	}

	vir_bytes end = start + len;
	struct phys_region *pr;
	vir_bytes voffset;

#if SANITYCHECKS
	SLABSANE(region);
	for (voffset = 0; voffset < phys_slot(region->length);
		voffset += VM_PAGE_SIZE) {
		pr = physblock_get(region, voffset);
		if (pr) {
			struct phys_block *pb = pr->ph;
			for (struct phys_region *others = pb->firstregion; others;
				others = others->next_ph_list) {
				assert(others->ph == pb);
			}
		}
	}
#endif

	for (voffset = start; voffset < end; voffset += VM_PAGE_SIZE) {
		pr = physblock_get(region, voffset);
		if (pr) {
			assert(pr->offset >= start);
			assert(pr->offset < end);
			pb_unreferenced(region, pr, 1);
			SLABFREE(pr);
		}
	}

	return OK;
}

/*===========================================================================*
 *				map_free				     *
 *===========================================================================*/
int map_free(struct vir_region *region)
{
	if (!region) {
		return EINVAL;
	}

	int r = map_subfree(region, 0, region->length);
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
	if (vmp == NULL) {
		return OK;
	}

	for (;;) {
		struct vir_region *r = region_search_root(&vmp->vm_regions_avl);
		if (r == NULL) {
			break;
		}

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

	SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
	if(!region_search_root(&vmp->vm_regions_avl))
		panic("process has no regions: %d", vmp->vm_endpoint);
#endif

	r = region_search(&vmp->vm_regions_avl, offset, AVL_LESS_EQUAL);

	if (r && offset >= r->vaddr && offset < r->vaddr + r->length) {
		vir_bytes ph = offset - r->vaddr;
		if (physr) {
			*physr = physblock_get(r, ph);
			if (*physr) {
				assert((*physr)->offset == ph);
			}
		}
		return r;
	}

	SANITYCHECK(SCL_FUNCTIONS);

	return NULL;
}

u32_t vrallocflags(u32_t flags)
{
    return ((flags & VR_PHYS64K) ? PAF_ALIGN64K : 0)
         | ((flags & VR_LOWER16MB) ? PAF_LOWER16MB : 0)
         | ((flags & VR_LOWER1MB) ? PAF_LOWER1MB : 0)
         | ((flags & VR_UNINITIALIZED) ? 0 : PAF_CLEAR);
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

	vir_bytes aligned_offset = offset - (offset % VM_PAGE_SIZE);

	assert(aligned_offset < region->length);
	assert(!(region->vaddr % VM_PAGE_SIZE));

	if (write && !(region->flags & VR_WRITABLE)) {
		return EPERM;
	}

	SANITYCHECK(SCL_FUNCTIONS);

	ph = physblock_get(region, aligned_offset);
	if (!ph) {
		struct phys_block *pb;

		if (!(pb = pb_new(MAP_NONE))) {
			printf("map_pf: pb_new failed\n");
			return ENOMEM;
		}

		ph = pb_reference(pb, aligned_offset, region, region->def_memtype);
		if (!ph) {
			printf("map_pf: pb_reference failed\n");
			pb_free(pb);
			return ENOMEM;
		}
	}

	assert(ph && ph->ph);
	assert(ph->memtype->writable);

	if (!write || !ph->memtype->writable(ph)) {
		assert(ph->memtype->ev_pagefault);

		r = ph->memtype->ev_pagefault(vmp, region, ph, write,
			pf_callback, state, len, io);

		if (r == SUSPEND) {
			return SUSPEND;
		}

		if (r != OK) {
			pb_unreferenced(region, ph, 1);
			return r;
		}
	}

	assert(ph && ph->ph && ph->ph->phys != MAP_NONE);

	r = map_ph_writept(vmp, region, ph);
	if (r != OK) {
		printf("map_pf: writept failed\n");
		pb_unreferenced(region, ph, 1);
		return r;
	}

	SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
	if (pt_checkrange(&vmp->vm_pt, region->vaddr + aligned_offset,
		VM_PAGE_SIZE, write) != OK) {
		panic("map_pf: pt_checkrange failed");
	}
#endif

	return OK;
}

int map_handle_memory(struct vmproc *vmp,
	struct vir_region *region, vir_bytes start_offset, vir_bytes length,
	int write, vfs_callback_t cb, void *state, int statelen)
{
	if (length == 0) {
		return OK;
	}

	vir_bytes lim = start_offset + length;

	if (lim <= start_offset) {
		return EOVERFLOW;
	}

	int io = 0;
	for (vir_bytes offset = start_offset; offset < lim; offset += VM_PAGE_SIZE) {
		int r = map_pf(vmp, region, offset, write,
			cb, state, statelen, &io);
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
	region_iter iter;

	pt_assert(&vmp->vm_pt);

	region_start_iter_least(&vmp->vm_regions_avl, &iter);
	while ((vr = region_get_iter(&iter)) != NULL) {
		int r = map_handle_memory(vmp, vr, 0, vr->length, 1, NULL, 0, 0);
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
	/* map_copy_region creates a complete copy of the vir_region
	 * data structure, linking in the same phys_blocks directly,
	 * but all in limbo, i.e., the caller has to link the vir_region
	 * to a process. Therefore it doesn't increase the refcount in
	 * the phys_block; the caller has to do this once it's linked.
	 * The reason for this is to keep the sanity checks working
	 * within this function.
	 */
	struct vir_region *newvr;
#if SANITYCHECKS
	unsigned int original_phys_regions_count = physregions(vr);
#endif

	newvr = region_new(vr->parent, vr->vaddr, vr->length, vr->flags, vr->def_memtype);
	if (!newvr) {
		return NULL;
	}

	newvr->parent = vmp;

	if (vr->def_memtype->ev_copy) {
		if (vr->def_memtype->ev_copy(vr, newvr) != OK) {
			goto error_exit;
		}
	}

	for (vir_bytes p = 0; p < phys_slot(vr->length); p++) {
		struct phys_region *ph = physblock_get(vr, p * VM_PAGE_SIZE);
		if (!ph) {
			continue;
		}

		struct phys_region *newph = pb_reference(ph->ph, ph->offset, newvr,
			vr->def_memtype);
		if (!newph) {
			goto error_exit;
		}

		if (ph->memtype->ev_reference) {
			ph->memtype->ev_reference(ph, newph);
		}

#if SANITYCHECKS
		newph->written = 0;
		assert(physregions(vr) == original_phys_regions_count);
#endif
	}

#if SANITYCHECKS
	assert(physregions(vr) == physregions(newvr));
#endif

	return newvr;

error_exit:
	map_free(newvr);
	return NULL;
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
			printf("VM: copy_abs2region: no physical block for offset.\n");
			return EFAULT;
		}

		phys_bytes suboffset = offset - ph->offset;
		if (suboffset >= VM_PAGE_SIZE) {
			printf("VM: copy_abs2region: offset is out of block bounds.\n");
			return EFAULT;
		}

		phys_bytes sublen = VM_PAGE_SIZE - suboffset;
		if (sublen > len) {
			sublen = len;
		}

		if (ph->ph->refcount != 1) {
			printf("VM: copy_abs2region: page is shared and not writable.\n");
			return EFAULT;
		}

		phys_bytes dest_phys_addr = ph->ph->phys + suboffset;
		if (sys_abscopy(absaddr, dest_phys_addr, sublen) != OK) {
			printf("VM: copy_abs2region: sys_abscopy failed.\n");
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
	if (!vmp) {
		return EINVAL;
	}

	region_iter v_iter;
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while (1) {
		struct vir_region *vr = region_get_iter(&v_iter);
		if (!vr) {
			break;
		}

		for (vir_bytes p = 0; p < vr->length; p += VM_PAGE_SIZE) {
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
		return -EINVAL;
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
	if (!dst || !src) {
		return EINVAL;
	}

	struct vir_region *start_vr = start_src_vr;
	if (!start_vr) {
		start_vr = region_search_least(&src->vm_regions_avl);
	}

	if (!start_vr) {
		return OK;
	}

	struct vir_region *end_vr = end_src_vr;
	if (!end_vr) {
		end_vr = region_search_greatest(&src->vm_regions_avl);
	}

	assert(end_vr);
	assert(start_vr->parent == src);
	assert(end_vr->parent == src);

	region_iter v_iter;
	region_start_iter(&src->vm_regions_avl, &v_iter, start_vr->vaddr, AVL_EQUAL);
	assert(region_get_iter(&v_iter) == start_vr);

	SANITYCHECK(SCL_FUNCTIONS);

	struct vir_region *vr;
	while ((vr = region_get_iter(&v_iter))) {
		struct vir_region *newvr = map_copy_region(dst, vr);
		if (!newvr) {
			map_free_proc(dst);
			return ENOMEM;
		}

		region_insert(&dst->vm_regions_avl, newvr);

#if SANITYCHECKS
		{
			assert(vr->length == newvr->length);
			assert(vr->physblocks != newvr->physblocks);
			for (vir_bytes vaddr = 0; vaddr < vr->length; vaddr += VM_PAGE_SIZE) {
				struct phys_region *orig_ph = physblock_get(vr, vaddr);
				struct phys_region *new_ph = physblock_get(newvr, vaddr);
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
		if (vr == end_vr) {
			break;
		}
		region_incr_iter(&v_iter);
	}

	map_writept(src);
	map_writept(dst);

	SANITYCHECK(SCL_FUNCTIONS);
	return OK;
}

int map_region_extend_upto_v(struct vmproc *vmp, vir_bytes v)
{
	vir_bytes offset = roundup(v, VM_PAGE_SIZE);
	struct vir_region *vr;
	struct vir_region *nextvr;

	vr = region_search(&vmp->vm_regions_avl, offset, AVL_LESS);
	if (!vr) {
		return ENOMEM;
	}

	if (vr->vaddr + vr->length >= v) {
		return OK;
	}

	nextvr = getnextvr(vr);
	if (nextvr && nextvr->vaddr < offset) {
		return ENOMEM;
	}

	if (!vr->def_memtype->ev_resize) {
		vir_bytes limit = vr->vaddr + vr->length;
		vir_bytes extralen = offset - limit;
		if (!map_page_region(vmp, limit, 0, extralen,
			VR_WRITABLE | VR_ANON, 0, &mem_type_anon)) {
			return ENOMEM;
		}
		return OK;
	}

	vir_bytes new_len = offset - vr->vaddr;
	int prevslots = phys_slot(vr->length);
	int newslots = phys_slot(new_len);

	if (newslots <= prevslots) {
		return OK;
	}

	if ((size_t)newslots > SIZE_MAX / sizeof(struct phys_region *)) {
		return ENOMEM;
	}
	size_t new_alloc_size = (size_t)newslots * sizeof(struct phys_region *);

	struct phys_region **newpr = realloc(vr->physblocks, new_alloc_size);
	if (!newpr) {
		return ENOMEM;
	}

	vr->physblocks = newpr;

	int addedslots = newslots - prevslots;
	size_t added_size = (size_t)addedslots * sizeof(struct phys_region *);
	memset(vr->physblocks + prevslots, 0, added_size);

	return vr->def_memtype->ev_resize(vmp, vr, new_len);
}

/*========================================================================*
 *				map_unmap_region	     	  	*
 *========================================================================*/
static void handle_full_unmap(struct vmproc *vmp, struct vir_region *r)
{
	region_remove(&vmp->vm_regions_avl, r->vaddr);
	map_free(r);
}

static void handle_end_unmap(struct vir_region *r, vir_bytes len)
{
	r->length -= len;
}

static int handle_start_unmap(struct vmproc *vmp, struct vir_region *r, vir_bytes len)
{
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

	vir_bytes original_length = r->length;
	int freeslots = phys_slot(len);

	region_remove(&vmp->vm_regions_avl, r->vaddr);
	r->vaddr += len;
	r->length -= len;
	region_insert(&vmp->vm_regions_avl, r);

	for (vir_bytes voffset = len; voffset < original_length;
		voffset += VM_PAGE_SIZE) {
		struct phys_region *pr = physblock_get(r, voffset);
		if (pr) {
			pr->offset -= len;
		}
	}

	int remslots = phys_slot(r->length);
	if (remslots > 0) {
		memmove(r->physblocks, r->physblocks + freeslots,
			remslots * sizeof(struct phys_region *));
	}

	return OK;
}

int map_unmap_region(struct vmproc *vmp, struct vir_region *r,
	vir_bytes offset, vir_bytes len)
{
	SANITYCHECK(SCL_FUNCTIONS);

	if (offset + len > r->length || (len % VM_PAGE_SIZE) != 0) {
		printf("VM: bogus length 0x%lx\n", len);
		return EINVAL;
	}

	vir_bytes regionstart = r->vaddr + offset;

	map_subfree(r, offset, len);

	int result = OK;
	if (r->length == len) {
		handle_full_unmap(vmp, r);
	} else if (offset == 0) {
		result = handle_start_unmap(vmp, r, len);
	} else if (offset + len == r->length) {
		handle_end_unmap(r, len);
	}

	if (result != OK) {
		return result;
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

static int populate_split_region_from_source(struct vir_region *new_vr,
	const struct vir_region *orig_vr, vir_bytes offset_in_orig)
{
	for (vir_bytes voffset = 0; voffset < new_vr->length; voffset += VM_PAGE_SIZE) {
		struct phys_region *ph = physblock_get(orig_vr, offset_in_orig + voffset);
		if (!ph) {
			continue;
		}
		if (!pb_reference(ph->ph, voffset, new_vr, ph->memtype)) {
			return ENOMEM;
		}
	}
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

	if (!vr->def_memtype->ev_split) {
		printf("VM: split region not implemented for %s\n",
			vr->def_memtype->name);
		sys_diagctl_stacktrace(vmp->vm_endpoint);
		return EINVAL;
	}

	r1 = region_new(vmp, vr->vaddr, split_len, vr->flags, vr->def_memtype);
	if (!r1) {
		goto fail;
	}

	r2 = region_new(vmp, vr->vaddr + split_len, rem_len, vr->flags, vr->def_memtype);
	if (!r2) {
		goto fail;
	}

	if (populate_split_region_from_source(r1, vr, 0) != OK) {
		goto fail;
	}

	if (populate_split_region_from_source(r2, vr, split_len) != OK) {
		goto fail;
	}

	vr->def_memtype->ev_split(vmp, vr, r1, r2);

	region_remove(&vmp->vm_regions_avl, vr->vaddr);
	map_free(vr);
	region_insert(&vmp->vm_regions_avl, r1);
	region_insert(&vmp->vm_regions_avl, r2);

	*vr1 = r1;
	*vr2 = r2;

	return OK;

fail:
	if (r1) {
		map_free(r1);
	}
	if (r2) {
		map_free(r2);
	}
	printf("split_region: failed\n");
	return ENOMEM;
}

int map_unmap_range(struct vmproc *vmp, vir_bytes unmap_start, vir_bytes length)
{
	vir_bytes offset, page_start, page_limit;
	vir_bytes page_length;
	region_iter v_iter;
	struct vir_region *current_region;

	if (length == 0) {
		return OK;
	}

	offset = unmap_start % VM_PAGE_SIZE;
	page_start = unmap_start - offset;

	if (length > VIR_BYTES_MAX - offset) {
		return EINVAL;
	}
	page_length = roundup(length + offset, VM_PAGE_SIZE);

	page_limit = page_start + page_length;
	if (page_limit <= page_start) {
		return EINVAL;
	}

	region_start_iter(&vmp->vm_regions_avl, &v_iter, page_start, AVL_LESS_EQUAL);
	current_region = region_get_iter(&v_iter);
	if (!current_region) {
		region_start_iter(&vmp->vm_regions_avl, &v_iter, page_start, AVL_GREATER);
		current_region = region_get_iter(&v_iter);
	}

	while (current_region && current_region->vaddr < page_limit) {
		struct vir_region *next_in_sequence;
		struct vir_region *next_to_process;
		vir_bytes region_limit = current_region->vaddr + current_region->length;
		vir_bytes overlap_start = MAX(page_start, current_region->vaddr);
		vir_bytes overlap_limit = MIN(page_limit, region_limit);

		region_incr_iter(&v_iter);
		next_in_sequence = region_get_iter(&v_iter);

		if (overlap_start >= overlap_limit) {
			current_region = next_in_sequence;
			continue;
		}

		int r;
		vir_bytes unmap_offset = overlap_start - current_region->vaddr;
		vir_bytes unmap_len = overlap_limit - overlap_start;

		if (overlap_start > current_region->vaddr && overlap_limit < region_limit) {
			struct vir_region *head_region, *tail_region;
			vir_bytes split_len = overlap_limit - current_region->vaddr;

			r = split_region(vmp, current_region, &head_region, &tail_region, split_len);
			if (r != OK) {
				printf("VM: unmap split failed\n");
				return r;
			}
			
			r = map_unmap_region(vmp, head_region, unmap_offset, unmap_len);
			next_to_process = tail_region;
		} else {
			r = map_unmap_region(vmp, current_region, unmap_offset, unmap_len);
			next_to_process = next_in_sequence;
		}

		if (r != OK) {
			printf("map_unmap_range: map_unmap_region failed\n");
			return r;
		}

		current_region = next_to_process;
		if (current_region) {
			region_start_iter(&vmp->vm_regions_avl, &v_iter, current_region->vaddr, AVL_EQUAL);
			assert(region_get_iter(&v_iter) == current_region);
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

	while ((vr = region_get_iter(&v_iter))) {
		region_incr_iter(&v_iter);
		if (vr->flags & type) {
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

	if (vr == NULL || vr->vaddr != addr) {
		return EINVAL;
	}

	if (vr->def_memtype == NULL || vr->def_memtype->regionid == NULL) {
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
	const struct vir_region *vr = map_lookup(vmp, addr, NULL);

	if (vr == NULL || vr->vaddr != addr || vr->def_memtype == NULL ||
	    vr->def_memtype->refcount == NULL) {
		return EINVAL;
	}

	if (cnt != NULL) {
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

#include <stdint.h>
#include <string.h>

static void get_usage_info_vm(struct vm_usage_info *vui)
{
	if (vui == NULL) {
		return;
	}

	memset(vui, 0, sizeof(*vui));

	const uint64_t self_pages_in_bytes = (uint64_t)get_vm_self_pages() * VM_PAGE_SIZE;
	const uint64_t total_usage = kernel_boot_info.vm_allocated_bytes + self_pages_in_bytes;

	vui->vui_total = total_usage;
	vui->vui_virtual = total_usage;
	vui->vui_mvirtual = total_usage;
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
is_stack_region(const struct vir_region *vr)
{
	if (!vr) {
		return 0;
	}

	const uintptr_t stack_base = VM_STACKTOP - DEFAULT_STACK_LIMIT;
	return vr->vaddr == stack_base && vr->length == DEFAULT_STACK_LIMIT;
}

/*========================================================================*
 *				get_usage_info				  *
 *========================================================================*/
static void process_region_usage(const struct vir_region *vr,
	struct vm_usage_info *vui)
{
	struct phys_region *ph;
	vir_bytes voffset;

	vui->vui_virtual += vr->length;
	vui->vui_mvirtual += vr->length;

	for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
		ph = physblock_get(vr, voffset);

		if (ph == NULL) {
			if (is_stack_region(vr)) {
				vui->vui_mvirtual -= VM_PAGE_SIZE;
			}
			continue;
		}

		vui->vui_total += VM_PAGE_SIZE;

		if (ph->ph->refcount > 1) {
			vui->vui_common += VM_PAGE_SIZE;
			if ((vr->flags & VR_SHARED) != 0) {
				vui->vui_shared += VM_PAGE_SIZE;
			}
		}
	}
}

static void set_resource_stats(const struct vmproc *vmp,
	struct vm_usage_info *vui)
{
	const long bytes_per_kb = 1024L;

	vui->vui_maxrss = vmp->vm_total_max / bytes_per_kb;
	vui->vui_minflt = vmp->vm_minor_page_fault;
	vui->vui_majflt = vmp->vm_major_page_fault;
}

void get_usage_info(struct vmproc *vmp, struct vm_usage_info *vui)
{
	struct vir_region *vr;
	region_iter v_iter;

	if (vmp == NULL || vui == NULL) {
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

	while ((vr = region_get_iter(&v_iter)) != NULL) {
		process_region_usage(vr, vui);
		region_incr_iter(&v_iter);
	}

	set_resource_stats(vmp, vui);
}

/*===========================================================================*
 *				get_region_info				     *
 *===========================================================================*/
int get_region_info(struct vmproc *vmp, struct vm_region_info *vri,
	int max, vir_bytes *nextp)
{
	struct vir_region *vr;
	region_iter v_iter;
	int count = 0;
	vir_bytes current_next = *nextp;

	if (max <= 0) {
		return 0;
	}

	region_start_iter(&vmp->vm_regions_avl, &v_iter, current_next, AVL_GREATER_EQUAL);

	while (count < max && (vr = region_get_iter(&v_iter)) != NULL) {
		struct phys_region *first_phys = NULL;
		struct phys_region *last_phys = NULL;
		vir_bytes voffset;

		current_next = vr->vaddr + vr->length;

		for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
			struct phys_region *ph = physblock_get(vr, voffset);
			if (ph != NULL) {
				if (first_phys == NULL) {
					first_phys = ph;
				}
				last_phys = ph;
			}
		}

		if (first_phys != NULL) {
			vri[count].vri_addr = vr->vaddr + first_phys->offset;
			vri[count].vri_length = last_phys->offset + VM_PAGE_SIZE - first_phys->offset;
			vri[count].vri_prot = PROT_READ;

			if (vr->flags & VR_WRITABLE) {
				vri[count].vri_prot |= PROT_WRITE;
			}
			count++;
		}

		region_incr_iter(&v_iter);
	}

	*nextp = current_next;
	return count;
}

/*========================================================================*
 *				regionprintstats			  *
 *========================================================================*/
#define BYTES_PER_KB 1024

static void accumulate_region_stats(const struct vir_region *vr,
                                    vir_bytes *used,
                                    vir_bytes *weighted)
{
	if (vr->flags & VR_DIRECT) {
		return;
	}

	for (vir_bytes voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
		const struct phys_region *pr = physblock_get(vr, voffset);

		if (pr && pr->ph && pr->ph->refcount > 0) {
			*used += VM_PAGE_SIZE;
			*weighted += VM_PAGE_SIZE / pr->ph->refcount;
		}
	}
}

void printregionstats(struct vmproc *vmp)
{
	if (!vmp) {
		return;
	}

	vir_bytes used = 0;
	vir_bytes weighted = 0;

	struct vir_region *vr;
	region_iter v_iter;

	for (region_start_iter_least(&vmp->vm_regions_avl, &v_iter);
	     (vr = region_get_iter(&v_iter)) != NULL;
	     region_incr_iter(&v_iter)) {
		accumulate_region_stats(vr, &used, &weighted);
	}

	printf("%6lukB  %6lukB\n", used / BYTES_PER_KB, weighted / BYTES_PER_KB);
}

void map_setparent(struct vmproc *vmp)
{
    struct vir_region *vr;
    region_iter iter;

    if (!vmp) {
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
	if (!vr) {
		return 0;
	}

	unsigned int count = 0;
	vir_bytes voffset;

	for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
		if (physblock_get(vr, voffset)) {
			count++;
		}
	}

	return count;
}
