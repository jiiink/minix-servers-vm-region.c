
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
    // Function intentionally left blank
}

static void map_printregion(struct vir_region *vr)
{
    if (!vr || !vr->def_memtype || !vr->def_memtype->name || !vr->physblocks) {
        printf("Invalid input to map_printregion\n");
        return;
    }

    unsigned long npages = vr->length / VM_PAGE_SIZE;
    printf("map_printmap: map_name: %s\n", vr->def_memtype->name);
    printf("\t%lx (len 0x%lx, %lukB), %s, %s\n",
           vr->vaddr, vr->length, vr->length / 1024,
           vr->def_memtype->name,
           (vr->flags & VR_WRITABLE) ? "writable" : "readonly");
    printf("\t\tphysblocks:\n");
    for (unsigned long i = 0; i < npages; ++i) {
        struct phys_region *ph = vr->physblocks[i];
        if (!ph || !ph->ph) {
            continue;
        }
        printf("\t\t@ %lx (refs %d): phys 0x%lx, %s\n",
               vr->vaddr + ph->offset,
               ph->ph->refcount, ph->ph->phys,
               pt_writable(vr->parent, vr->vaddr + ph->offset) ? "W" : "R");
    }
}

struct phys_region *physblock_get(struct vir_region *region, vir_bytes offset)
{
	if (region == NULL || region->physblocks == NULL) {
		return NULL;
	}

	if ((offset % VM_PAGE_SIZE) != 0 || offset >= region->length) {
		return NULL;
	}

	int i = offset / VM_PAGE_SIZE;
	struct phys_region *foundregion = region->physblocks[i];

	if (foundregion != NULL && foundregion->offset != offset) {
		return NULL;
	}

	return foundregion;
}

void physblock_set(struct vir_region *region, vir_bytes offset, struct phys_region *newphysr)
{
	int i;
	struct vmproc *proc;

	if (!region || !region->parent || offset % VM_PAGE_SIZE != 0 || offset >= region->length)
		return;

	i = offset / VM_PAGE_SIZE;
	proc = region->parent;

	if (newphysr) {
		if (region->physblocks[i] || newphysr->offset != offset)
			return;
		proc->vm_total += VM_PAGE_SIZE;
		if (proc->vm_total > proc->vm_total_max)
			proc->vm_total_max = proc->vm_total;
	} else {
		if (!region->physblocks[i])
			return;
		proc->vm_total -= VM_PAGE_SIZE;
	}
	region->physblocks[i] = newphysr;
}

/*===========================================================================*
 *				map_printmap				     *
 *===========================================================================*/
void map_printmap(const struct vmproc *vmp)
{
    if (vmp == NULL) {
        fprintf(stderr, "Error: NULL vmproc pointer in map_printmap\n");
        return;
    }

    printf("memory regions in process %d:\n", vmp->vm_endpoint);

    region_iter iter;
    region_start_iter_least(&vmp->vm_regions_avl, &iter);

    struct vir_region *vr;
    while ((vr = region_get_iter(&iter)) != NULL) {
        map_printregion(vr);
        region_incr_iter(&iter);
    }
}

static struct vir_region *getnextvr(struct vir_region *vr)
{
    if (!vr || !vr->parent) {
        return NULL;
    }

    region_iter v_iter;
    SLABSANE(vr);

    region_start_iter(&vr->parent->vm_regions_avl, &v_iter, vr->vaddr, AVL_EQUAL);

    struct vir_region *current = region_get_iter(&v_iter);
    if (!current || current != vr) {
        return NULL;
    }

    region_incr_iter(&v_iter);
    struct vir_region *nextvr = region_get_iter(&v_iter);

    if (!nextvr) {
        return NULL;
    }

    SLABSANE(nextvr);

    if (vr->parent != nextvr->parent || vr->vaddr >= nextvr->vaddr ||
        vr->vaddr + vr->length > nextvr->vaddr) {
        return NULL;
    }

    return nextvr;
}

static int pr_writable(const struct vir_region *vr, const struct phys_region *pr)
{
	if (!vr || !pr || !pr->memtype || !pr->memtype->writable)
		return 0;
	if (!(vr->flags & VR_WRITABLE))
		return 0;
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
    int flags;
    struct phys_block *pb;

    if (!vmp || !vr || !pr || !(pb = pr->ph)) {
        printf("VM: map_writept: null argument(s)\n");
        return ENOMEM;
    }

    if ((vr->vaddr % VM_PAGE_SIZE) != 0 || (pr->offset % VM_PAGE_SIZE) != 0 || pb->refcount <= 0) {
        printf("VM: map_writept: invalid region/offset/refcount\n");
        return ENOMEM;
    }

    flags = PTF_PRESENT | PTF_USER;

    flags |= pr_writable(vr, pr) ? PTF_WRITE : PTF_READ;

    if (vr->def_memtype && vr->def_memtype->pt_flags) {
        flags |= vr->def_memtype->pt_flags(vr);
    }

    if (pt_writemap(vmp, &vmp->vm_pt, vr->vaddr + pr->offset, pb->phys, VM_PAGE_SIZE, flags,
#if SANITYCHECKS
        !pr->written ? 0 :
#endif
        WMF_OVERWRITE) != OK) {
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

	if (length == 0 || length % VM_PAGE_SIZE != 0) {
		printf("region_find_slot: invalid length 0x%lx\n", length);
		return SLOT_FAIL;
	}

	if (maxv == 0) {
		maxv = minv + length;
		if (maxv <= minv) {
			printf("region_find_slot: minv 0x%lx and bytes 0x%lx\n", minv, length);
			return SLOT_FAIL;
		}
	}

	if (minv >= maxv || minv + length > maxv) {
		printf("VM: 1 minv: 0x%lx maxv: 0x%lx length: 0x%lx\n", minv, maxv, length);
		return SLOT_FAIL;
	}

#define TRY_ALLOC_RANGE(range_start, range_end) do { \
		vir_bytes fr_start = MAX((range_start), minv); \
		vir_bytes fr_end = MIN((range_end), maxv); \
		if (fr_end > fr_start && fr_end - fr_start >= length) { \
			startv = fr_end - length; \
			foundflag = 1; \
		} \
	} while (0)

#define ATTEMPT_FREE_RANGE(start, end) do { \
		if (foundflag) break; \
		TRY_ALLOC_RANGE((start) + VM_PAGE_SIZE, (end) - VM_PAGE_SIZE); \
		if (!foundflag) { \
			TRY_ALLOC_RANGE(start, end); \
		} \
	} while (0)

	region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_GREATER_EQUAL);
	lastregion = region_get_iter(&iter);

	if (!lastregion) {
		region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_LESS);
		lastregion = region_get_iter(&iter);
		ATTEMPT_FREE_RANGE(lastregion ? lastregion->vaddr + lastregion->length : 0, VM_DATATOP);
	}

	if (!foundflag) {
		struct vir_region *vr;
		while (!foundflag && (vr = region_get_iter(&iter))) {
			struct vir_region *nextvr;
			region_decr_iter(&iter);
			nextvr = region_get_iter(&iter);
			ATTEMPT_FREE_RANGE(nextvr ? nextvr->vaddr + nextvr->length : 0, vr->vaddr);
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
	vir_bytes hint = vmp->vm_region_top;

	if(maxv != 0 && hint < maxv && hint >= minv) {
		vir_bytes v = region_find_slot_range(vmp, minv, hint, length);
		if(v != SLOT_FAIL) {
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
	struct vir_region *newregion = NULL;
	struct phys_region **newphysregions = NULL;
	static u32_t id = 0;
	int slots = phys_slot(length);

	newregion = SLABALLOC(newregion);
	if (!newregion) {
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
	if (!newphysregions) {
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

	assert(length % VM_PAGE_SIZE == 0);

	SANITYCHECK(SCL_FUNCTIONS);

	startv = region_find_slot(vmp, minv, maxv, length);
	if (startv == SLOT_FAIL)
		return NULL;

	newregion = region_new(vmp, startv, length, flags, memtype);
	if (!newregion) {
		printf("VM: map_page_region: allocating region failed\n");
		return NULL;
	}

	if (newregion->def_memtype->ev_new) {
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

	newregion->flags &= ~VR_UNINITIALIZED;

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
static int map_subfree(struct vir_region *region, vir_bytes start, vir_bytes len)
{
	vir_bytes end = start + len;
	vir_bytes voffset;

#if SANITYCHECKS
	SLABSANE(region);
	for (voffset = 0; voffset < phys_slot(region->length); voffset += VM_PAGE_SIZE) {
		struct phys_region *pr = physblock_get(region, voffset);
		if (!pr)
			continue;
		struct phys_block *pb = pr->ph;
		for (struct phys_region *others = pb->firstregion; others; others = others->next_ph_list) {
			assert(others->ph == pb);
		}
	}
#endif

	for (voffset = start; voffset < end; voffset += VM_PAGE_SIZE) {
		struct phys_region *pr = physblock_get(region, voffset);
		if (!pr)
			continue;
		if (pr->offset < start || pr->offset >= end)
			return EINVAL;
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
	if (!region || !region->def_memtype) {
		return ERR_INVALID_ARG;
	}

	int result = map_subfree(region, 0, region->length);
	if (result != OK) {
		printf("%d\n", __LINE__);
		return result;
	}

	if (region->def_memtype->ev_delete) {
		region->def_memtype->ev_delete(region);
	}
	if (region->physblocks) {
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

	while ((r = region_search_root(&vmp->vm_regions_avl)) != NULL) {
#if SANITYCHECKS
		nocheck++;
#endif
		region_remove(&vmp->vm_regions_avl, r->vaddr);
		map_free(r);
#if SANITYCHECKS
		nocheck--;
#endif
	}

	region_init(&vmp->vm_regions_avl);

	return OK;
}

/*===========================================================================*
 *				map_lookup				     *
 *===========================================================================*/
struct vir_region *map_lookup(struct vmproc *vmp, vir_bytes offset, struct phys_region **physr)
{
	SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
	if (!region_search_root(&vmp->vm_regions_avl))
	{
		panic("process has no regions: %d", vmp->vm_endpoint);
	}
#endif

	struct vir_region *r = region_search(&vmp->vm_regions_avl, offset, AVL_LESS_EQUAL);
	if (!r)
	{
		SANITYCHECK(SCL_FUNCTIONS);
		return NULL;
	}

	if (offset < r->vaddr || offset >= r->vaddr + r->length)
	{
		SANITYCHECK(SCL_FUNCTIONS);
		return NULL;
	}

	vir_bytes ph = offset - r->vaddr;
	if (physr)
	{
		*physr = physblock_get(r, ph);
		if (!*physr)
		{
			SANITYCHECK(SCL_FUNCTIONS);
			return NULL;
		}
		assert((*physr)->offset == ph);
	}

	SANITYCHECK(SCL_FUNCTIONS);
	return r;
}

u32_t vrallocflags(u32_t flags)
{
	u32_t allocflags = 0;

	if ((flags & VR_PHYS64K) != 0)
		allocflags |= PAF_ALIGN64K;
	if ((flags & VR_LOWER16MB) != 0)
		allocflags |= PAF_LOWER16MB;
	if ((flags & VR_LOWER1MB) != 0)
		allocflags |= PAF_LOWER1MB;
	if ((flags & VR_UNINITIALIZED) == 0)
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
    int r = OK;

    offset -= offset % VM_PAGE_SIZE;
    assert(offset < region->length);
    assert(!(region->vaddr % VM_PAGE_SIZE));
    assert(!(write && !(region->flags & VR_WRITABLE)));

    SANITYCHECK(SCL_FUNCTIONS);

    ph = physblock_get(region, offset);
    if (!ph) {
        struct phys_block *pb = pb_new(MAP_NONE);
        if (!pb)
            return ENOMEM;

        ph = pb_reference(pb, offset, region, region->def_memtype);
        if (!ph) {
            pb_free(pb);
            return ENOMEM;
        }
    }

    assert(ph && ph->ph);
    assert(ph->memtype->writable);

    if (!write || !ph->memtype->writable(ph)) {
        assert(ph->memtype->ev_pagefault && ph->ph);

        r = ph->memtype->ev_pagefault(vmp, region, ph, write, pf_callback, state, len, io);
        if (r == SUSPEND)
            return SUSPEND;

        if (r != OK) {
            pb_unreferenced(region, ph, 1);
            return r;
        }

        assert(ph && ph->ph && ph->ph->phys != MAP_NONE);
    }

    assert(ph->ph && ph->ph->phys != MAP_NONE);

    r = map_ph_writept(vmp, region, ph);
    if (r != OK)
        return r;

    SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
    if (pt_checkrange(&vmp->vm_pt, region->vaddr + offset, VM_PAGE_SIZE, write) != OK)
        panic("map_pf: pt_checkrange failed: %d", r);
#endif

    return OK;
}

int map_handle_memory(struct vmproc *vmp,
    struct vir_region *region, vir_bytes start_offset, vir_bytes length,
    int write, vfs_callback_t cb, void *state, int statelen)
{
    if (length == 0)
        return EINVAL;

    if (start_offset > start_offset + length - 1)
        return EOVERFLOW;

    vir_bytes lim = start_offset + length;
    int io = 0;

    for (vir_bytes offset = start_offset; offset < lim; offset += VM_PAGE_SIZE) {
        int r = map_pf(vmp, region, offset, write, cb, state, statelen, &io);
        if (r != OK)
            return r;
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

    while ((vr = region_get_iter(&iter)) != NULL) {
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
    struct vir_region *newvr = NULL;
    struct phys_region *ph = NULL;
    vir_bytes p;
    int r;
#if SANITYCHECKS
    unsigned int cr;
    cr = physregions(vr);
#endif

    if (!vr || !vmp)
        return NULL;

    newvr = region_new(vr->parent, vr->vaddr, vr->length, vr->flags, vr->def_memtype);
    if (!newvr)
        return NULL;

    newvr->parent = vmp;

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
        if (!ph)
            continue;

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
        printf("VM: copy_abs2region: invalid destregion or physblocks.\n");
        return EFAULT;
    }

    while (len > 0) {
        phys_bytes sublen, suboffset;
        struct phys_region *ph;

        ph = physblock_get(destregion, offset);
        if (!ph || ph->offset > offset || ph->offset + VM_PAGE_SIZE <= offset) {
            printf("VM: copy_abs2region: no phys region found.\n");
            return EFAULT;
        }

        suboffset = offset - ph->offset;
        if (suboffset >= VM_PAGE_SIZE) {
            printf("VM: copy_abs2region: suboffset out of bounds.\n");
            return EFAULT;
        }

        sublen = VM_PAGE_SIZE - suboffset;
        if (sublen > len)
            sublen = len;

        if (suboffset + sublen > VM_PAGE_SIZE) {
            printf("VM: copy_abs2region: region overflow.\n");
            return EFAULT;
        }

        if (!ph->ph || ph->ph->refcount != 1) {
            printf("VM: copy_abs2region: refcount not 1 or ph is NULL.\n");
            return EFAULT;
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
	int r;
	region_iter v_iter;

	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while ((vr = region_get_iter(&v_iter))) {
		vir_bytes p, region_end;
		region_end = vr->length;

		for (p = 0; p < region_end; p += VM_PAGE_SIZE) {
			struct phys_region *ph = physblock_get(vr, p);
			if (!ph)
				continue;

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
int map_proc_copy(struct vmproc *dst, const struct vmproc *src) {
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

    if (!start_src_vr)
        start_src_vr = region_search_least(&src->vm_regions_avl);
    if (!end_src_vr)
        end_src_vr = region_search_greatest(&src->vm_regions_avl);

    if (!start_src_vr || !end_src_vr)
        return EINVAL;
    if (start_src_vr->parent != src)
        return EINVAL;

    region_start_iter(&src->vm_regions_avl, &v_iter,
        start_src_vr->vaddr, AVL_EQUAL);

    if (region_get_iter(&v_iter) != start_src_vr)
        return EINVAL;

    SANITYCHECK(SCL_FUNCTIONS);

    for (;;) {
        vr = region_get_iter(&v_iter);
        if (!vr)
            break;

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
        {
            vir_bytes vaddr;
            struct phys_region *orig_ph, *new_ph;
            if (vr->physblocks == newvr->physblocks) {
                map_free_proc(dst);
                return EINVAL;
            }
            for (vaddr = 0; vaddr < vr->length; vaddr += VM_PAGE_SIZE) {
                orig_ph = physblock_get(vr, vaddr);
                new_ph = physblock_get(newvr, vaddr);
                if (!orig_ph) {
                    if (new_ph) {
                        map_free_proc(dst);
                        return EINVAL;
                    }
                    continue;
                }
                if (!new_ph || orig_ph == new_ph || orig_ph->ph != new_ph->ph) {
                    map_free_proc(dst);
                    return EINVAL;
                }
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
    vir_bytes offset = roundup(v, VM_PAGE_SIZE);
    struct vir_region *vr = region_search(&vmp->vm_regions_avl, offset, AVL_LESS);
    if (!vr) {
        printf("VM: nothing to extend\n");
        return ENOMEM;
    }

    if (vr->vaddr + vr->length >= v)
        return OK;

    vir_bytes limit = vr->vaddr + vr->length;
    if (vr->vaddr > offset) {
        printf("VM: invalid region boundaries\n");
        return ENOMEM;
    }

    int newslots = phys_slot(offset - vr->vaddr);
    int prevslots = phys_slot(vr->length);
    if (newslots < prevslots) {
        printf("VM: newslots less than prevslots\n");
        return ENOMEM;
    }
    int addedslots = newslots - prevslots;
    vir_bytes extralen = offset - limit;
    if (extralen <= 0) {
        printf("VM: extralen <= 0\n");
        return ENOMEM;
    }

    struct vir_region *nextvr = getnextvr(vr);
    if (nextvr && nextvr->vaddr < offset) {
        printf("VM: can't grow into next region\n");
        return ENOMEM;
    }

    if (!vr->def_memtype || !vr->def_memtype->ev_resize) {
        if (!map_page_region(vmp, limit, 0, extralen,
            VR_WRITABLE | VR_ANON, 0, &mem_type_anon)) {
            printf("resize: couldn't put anon memory there\n");
            return ENOMEM;
        }
        return OK;
    }

    struct phys_region **newpr = realloc(vr->physblocks, newslots * sizeof(struct phys_region *));
    if (!newpr) {
        printf("VM: map_region_extend_upto_v: realloc failed\n");
        return ENOMEM;
    }

    vr->physblocks = newpr;
    memset(vr->physblocks + prevslots, 0, addedslots * sizeof(struct phys_region *));

    int r = vr->def_memtype->ev_resize(vmp, vr, offset - vr->vaddr);
    return r;
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

	if (offset + len > r->length || (len % VM_PAGE_SIZE)) {
		printf("VM: bogus length 0x%lx\n", len);
		return EINVAL;
	}

	regionstart = r->vaddr + offset;
	freeslots = phys_slot(len);

	map_subfree(r, offset, len);

	if (r->length == len) {
		region_remove(&vmp->vm_regions_avl, r->vaddr);
		map_free(r);
	} else if (offset == 0) {
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
		r->vaddr += len;
		remslots = phys_slot(r->length);
		region_insert(&vmp->vm_regions_avl, r);

		for (voffset = len; voffset < r->length; voffset += VM_PAGE_SIZE) {
			pr = physblock_get(r, voffset);
			if (!pr) continue;
			if (pr->offset < offset || pr->offset < len) return EFAULT;
			pr->offset -= len;
		}
		if (remslots) {
			memmove(r->physblocks, r->physblocks + freeslots,
				remslots * sizeof(struct phys_region *));
		}
		r->length -= len;
	} else if (offset + len == r->length) {
		if (len > r->length) return EINVAL;
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

static int split_region(struct vmproc *vmp, struct vir_region *vr,
	struct vir_region **vr1, struct vir_region **vr2, vir_bytes split_len)
{
	struct vir_region *r1 = NULL, *r2 = NULL;
	vir_bytes rem_len;
	int slots1, slots2;
	vir_bytes voffset;

	if (split_len == 0 || split_len >= vr->length) {
		return EINVAL;
	}
	if ((split_len % VM_PAGE_SIZE) || (vr->length % VM_PAGE_SIZE) || (vr->vaddr % VM_PAGE_SIZE)) {
		return EINVAL;
	}

	rem_len = vr->length - split_len;

	if (!(vr->def_memtype && vr->def_memtype->ev_split)) {
		printf("VM: split region not implemented for %s\n",
			vr->def_memtype ? vr->def_memtype->name : "<null>");
		sys_diagctl_stacktrace(vmp->vm_endpoint);
		return EINVAL;
	}

	slots1 = phys_slot(split_len);
	slots2 = phys_slot(rem_len);

	r1 = region_new(vmp, vr->vaddr, split_len, vr->flags, vr->def_memtype);
	if (!r1) {
		goto bail;
	}

	r2 = region_new(vmp, vr->vaddr + split_len, rem_len, vr->flags, vr->def_memtype);
	if (!r2) {
		map_free(r1);
		goto bail;
	}

	for (voffset = 0; voffset < r1->length; voffset += VM_PAGE_SIZE) {
		struct phys_region *ph = physblock_get(vr, voffset);
		if (!ph) continue;
		if (!pb_reference(ph->ph, voffset, r1, ph->memtype)) {
			goto bail;
		}
	}

	for (voffset = 0; voffset < r2->length; voffset += VM_PAGE_SIZE) {
		struct phys_region *ph = physblock_get(vr, split_len + voffset);
		if (!ph) continue;
		if (!pb_reference(ph->ph, voffset, r2, ph->memtype)) {
			goto bail;
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

bail:
	if (r1) map_free(r1);
	if (r2) map_free(r2);

	printf("split_region: failed\n");

	return ENOMEM;
}

int map_unmap_range(struct vmproc *vmp, vir_bytes unmap_start, vir_bytes length)
{
    vir_bytes offset = unmap_start % VM_PAGE_SIZE;
    vir_bytes unmap_limit;
    region_iter v_iter;
    struct vir_region *vr = NULL, *nextvr = NULL;

    if (!vmp || length == 0)
        return EINVAL;

    unmap_start -= offset;
    length += offset;
    if (length < VM_PAGE_SIZE)
        return EINVAL;
    length = roundup(length, VM_PAGE_SIZE);
    unmap_limit = unmap_start + length;
    if (unmap_limit <= unmap_start)
        return EINVAL;

    region_start_iter(&vmp->vm_regions_avl, &v_iter, unmap_start, AVL_LESS_EQUAL);
    vr = region_get_iter(&v_iter);
    if (!vr) {
        region_start_iter(&vmp->vm_regions_avl, &v_iter, unmap_start, AVL_GREATER);
        vr = region_get_iter(&v_iter);
        if (!vr)
            return OK;
    }

    while (vr && vr->vaddr < unmap_limit) {
        vir_bytes vr_end = vr->vaddr + vr->length;
        vir_bytes this_unmap_start = MAX(unmap_start, vr->vaddr);
        vir_bytes this_unmap_limit = MIN(unmap_limit, vr_end);
        int r;

        region_incr_iter(&v_iter);
        nextvr = region_get_iter(&v_iter);

        if (this_unmap_start >= this_unmap_limit) {
            vr = nextvr;
            continue;
        }

        if (this_unmap_start > vr->vaddr && this_unmap_limit < vr_end) {
            struct vir_region *vr1 = NULL, *vr2 = NULL;
            vir_bytes split_len = this_unmap_limit - vr->vaddr;
            if (split_len == 0 || split_len >= vr->length)
                return EINVAL;
            r = split_region(vmp, vr, &vr1, &vr2, split_len);
            if (r != OK)
                return r;
            vr = vr1;
            vr_end = vr->vaddr + vr->length;
        }

        r = map_unmap_region(vmp, vr, this_unmap_start - vr->vaddr, this_unmap_limit - this_unmap_start);
        if (r != OK)
            return r;

        if (nextvr) {
            region_start_iter(&vmp->vm_regions_avl, &v_iter, nextvr->vaddr, AVL_EQUAL);
            if (region_get_iter(&v_iter) != nextvr)
                return EINVAL;
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
    region_iter v_iter;
    region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

    struct vir_region *vr;
    while ((vr = region_get_iter(&v_iter)) != NULL) {
        if ((vr->flags & type) != 0) {
            return vr;
        }
        region_incr_iter(&v_iter);
    }

    return NULL;
}

/*========================================================================*
 *				map_get_phys				  *
 *========================================================================*/
int map_get_phys(struct vmproc *vmp, vir_bytes addr, phys_bytes *r)
{
	struct vir_region *vr = map_lookup(vmp, addr, NULL);
	if (!vr || vr->vaddr != addr)
		return EINVAL;

	if (!vr->def_memtype || !vr->def_memtype->regionid)
		return EINVAL;

	if (r)
		*r = vr->def_memtype->regionid(vr);

	return OK;
}

/*========================================================================*
 *				map_get_ref				  *
 *========================================================================*/
int map_get_ref(struct vmproc *vmp, vir_bytes addr, u8_t *cnt)
{
	struct vir_region *vr = map_lookup(vmp, addr, NULL);

	if (!vr || vr->vaddr != addr || !vr->def_memtype || !vr->def_memtype->refcount)
		return EINVAL;

	if (cnt) {
		u8_t ref = vr->def_memtype->refcount(vr);
		*cnt = ref;
	}

	return OK;
}

void get_usage_info_kernel(struct vm_usage_info *vui)
{
	if (vui == NULL) {
		return;
	}
	memset(vui, 0, sizeof(*vui));
	size_t total = kernel_boot_info.kernel_allocated_bytes +
	               kernel_boot_info.kernel_allocated_bytes_dynamic;
	vui->vui_total = total;
	vui->vui_virtual = total;
	vui->vui_mvirtual = total;
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
static int is_stack_region(const struct vir_region *vr)
{
    if (vr == NULL) {
        return 0;
    }
    return (vr->vaddr == VM_STACKTOP - DEFAULT_STACK_LIMIT) &&
           (vr->length == DEFAULT_STACK_LIMIT);
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

    if (!vmp || !vui)
        return;

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
        vui->vui_virtual += vr->length;
        vui->vui_mvirtual += vr->length;

        for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
            ph = physblock_get(vr, voffset);
            if (!ph) {
                if (is_stack_region(vr))
                    vui->vui_mvirtual -= VM_PAGE_SIZE;
                continue;
            }

            vui->vui_total += VM_PAGE_SIZE;

            if (ph->ph->refcount > 1) {
                vui->vui_common += VM_PAGE_SIZE;
                if (vr->flags & VR_SHARED)
                    vui->vui_shared += VM_PAGE_SIZE;
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
int get_region_info(struct vmproc *vmp, struct vm_region_info *vri, int max, vir_bytes *nextp)
{
    if (!vmp || !vri || !nextp || max <= 0)
        return 0;

    struct vir_region *vr;
    vir_bytes next = *nextp;
    int count = 0;
    region_iter v_iter;

    region_start_iter(&vmp->vm_regions_avl, &v_iter, next, AVL_GREATER_EQUAL);

    while (count < max && (vr = region_get_iter(&v_iter))) {
        struct phys_region *ph_first = NULL, *ph_last = NULL;
        vir_bytes voffset;

        /* Identify the physical regions in use within the virtual region */
        for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
            struct phys_region *ph = physblock_get(vr, voffset);
            if (!ph)
                continue;
            if (!ph_first)
                ph_first = ph;
            ph_last = ph;
        }

        vir_bytes region_start = vr->vaddr;
        vir_bytes region_end = vr->vaddr + vr->length;
        next = region_end;

        if (!ph_first || !ph_last) {
            printf("skipping empty region 0x%lx-0x%lx\n", region_start, region_end);
            region_incr_iter(&v_iter);
            continue;
        }

        vri[count].vri_addr = region_start + ph_first->offset;
        vri[count].vri_prot = PROT_READ;
        vri[count].vri_length = ph_last->offset + VM_PAGE_SIZE - ph_first->offset;

        if (vr->flags & VR_WRITABLE)
            vri[count].vri_prot |= PROT_WRITE;

        count++;
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
	vir_bytes used = 0, weighted = 0;
	region_iter v_iter;

	if (!vmp) {
		printf("Invalid vmproc pointer.\n");
		return;
	}

	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while ((vr = region_get_iter(&v_iter))) {
		region_incr_iter(&v_iter);

		if (vr->flags & VR_DIRECT)
			continue;

		vir_bytes voffset;
		for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
			struct phys_region *pr = physblock_get(vr, voffset);
			if (!pr || !pr->ph || pr->ph->refcount == 0)
				continue;

			used += VM_PAGE_SIZE;
			weighted += VM_PAGE_SIZE / pr->ph->refcount;
		}
	}

	printf("%6lu kB  %6lu kB\n", used / 1024, weighted / 1024);
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
        vr->parent = vmp;
        region_incr_iter(&iter);
    }
}

unsigned int physregions(const struct vir_region *vr)
{
	unsigned int count = 0;
	if (!vr || vr->length == 0)
		return 0;
	for (vir_bytes offset = 0; offset < vr->length; offset += VM_PAGE_SIZE) {
		if (physblock_get(vr, offset))
			count++;
	}
	return count;
}
