
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

void map_region_init(void) {
    // Initialize necessary resources or configurations for the map region
}

#include <stdio.h>

static void map_printregion(struct vir_region *vr) {
    unsigned int i;
    struct phys_region *ph;
    const char *access_type = (vr->flags & VR_WRITABLE) ? "writable" : "readonly";

    printf("map_printmap: map_name: %s\n", vr->def_memtype->name);
    printf("\t%lx (len 0x%lx, %lukB), %p, %s\n", vr->vaddr, vr->length, vr->length / 1024, vr->def_memtype->name, access_type);
    printf("\t\tphysblocks:\n");

    for (i = 0; i < vr->length / VM_PAGE_SIZE; i++) {
        ph = vr->physblocks[i];
        if (!ph) continue;

        printf("\t\t@ %lx (refs %d): phys 0x%lx, %s\n", 
               (vr->vaddr + ph->offset), 
               ph->ph->refcount, 
               ph->ph->phys, 
               pt_writable(vr->parent, vr->vaddr + ph->offset) ? "W" : "R");
    }
}

struct phys_region *physblock_get(struct vir_region *region, vir_bytes offset) {
    struct phys_region *foundregion;
    
    if (offset % VM_PAGE_SIZE != 0 || offset >= region->length) {
        return NULL;
    }
    
    foundregion = region->physblocks[offset / VM_PAGE_SIZE];
    
    if (foundregion && foundregion->offset != offset) {
        return NULL;
    }
    
    return foundregion;
}

void physblock_set(struct vir_region *region, vir_bytes offset, struct phys_region *newphysr) {
    if (offset % VM_PAGE_SIZE != 0 || offset >= region->length) {
        return;
    }

    int i = offset / VM_PAGE_SIZE;
    struct vmproc *proc = region->parent;

    if (!proc) {
        return;
    }

    if (newphysr) {
        if (region->physblocks[i] || newphysr->offset != offset) {
            return;
        }
        proc->vm_total += VM_PAGE_SIZE;
        if (proc->vm_total > proc->vm_total_max) {
            proc->vm_total_max = proc->vm_total;
        }
    } else {
        if (!region->physblocks[i]) {
            return;
        }
        proc->vm_total -= VM_PAGE_SIZE;
    }

    region->physblocks[i] = newphysr;
}

/*===========================================================================*
 *				map_printmap				     *
 *===========================================================================*/
void map_printmap(struct vmproc *vmp) {
	if (vmp == NULL) return;

	printf("Memory regions in process %d:\n", vmp->vm_endpoint);

	region_iter iter;
	region_start_iter_least(&vmp->vm_regions_avl, &iter);

	struct vir_region *vr;
	while ((vr = region_get_iter(&iter)) != NULL) {
		map_printregion(vr);
		region_incr_iter(&iter);
	}
}

static struct vir_region *getnextvr(struct vir_region *vr) {
	if (!vr) return NULL;

	region_iter v_iter;
	SLABSANE(vr);
	region_start_iter(&vr->parent->vm_regions_avl, &v_iter, vr->vaddr, AVL_EQUAL);

	if (!region_get_iter(&v_iter) || region_get_iter(&v_iter) != vr) {
		return NULL;
	}

	region_incr_iter(&v_iter);
	struct vir_region *nextvr = region_get_iter(&v_iter);

	if (!nextvr) return NULL;

	SLABSANE(nextvr);

	if (vr->parent != nextvr->parent || vr->vaddr >= nextvr->vaddr || vr->vaddr + vr->length > nextvr->vaddr) {
		return NULL;
	}

	return nextvr;
}

#include <assert.h>

static int pr_writable(struct vir_region *vr, struct phys_region *pr)
{
	if (!pr->memtype || !pr->memtype->writable) {
		return 0;
	}
	return (vr->flags & VR_WRITABLE) ? pr->memtype->writable(pr) : 0;
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
int map_ph_writept(struct vmproc *vmp, struct vir_region *vr, struct phys_region *pr) {
    int flags = PTF_PRESENT | PTF_USER;
    struct phys_block *pb = pr->ph;

    if (!vmp || !vr || !pr || !pb) return EINVAL;
    if ((vr->vaddr % VM_PAGE_SIZE) || (pr->offset % VM_PAGE_SIZE) || (pb->refcount <= 0)) return EINVAL;

    flags |= pr_writable(vr, pr) ? PTF_WRITE : PTF_READ;
    if (vr->def_memtype->pt_flags) flags |= vr->def_memtype->pt_flags(vr);

    int result = pt_writemap(vmp, &vmp->vm_pt, vr->vaddr + pr->offset, pb->phys, VM_PAGE_SIZE, flags,
#if SANITYCHECKS
       pr->written ? WMF_OVERWRITE : 0
#else
       WMF_OVERWRITE
#endif
    );

    if (result != OK) {
        fprintf(stderr, "VM: map_writept: pt_writemap failed\n");
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
static vir_bytes region_find_slot_range(struct vmproc *vmp, vir_bytes minv, vir_bytes maxv, vir_bytes length) {
    struct vir_region *lastregion;
    vir_bytes startv = 0;
    int foundflag = 0;
    region_iter iter;

    SANITYCHECK(SCL_FUNCTIONS);
    assert(length > 0);

    if (maxv == 0) {
        maxv = minv + length;
        if (maxv <= minv) {
            printf("region_find_slot: minv 0x%lx and bytes 0x%lx\n", minv, length);
            return SLOT_FAIL;
        }
    }

    assert(!(length % VM_PAGE_SIZE));
    if (minv >= maxv) {
        printf("VM: 1 minv: 0x%lx maxv: 0x%lx length: 0x%lx\n", minv, maxv, length);
        return SLOT_FAIL;
    }

    if (minv + length > maxv) return SLOT_FAIL;

    #define FREEVRANGE_TRY(rangestart, rangeend) {     \
        vir_bytes frstart = MAX((rangestart), minv);   \
        vir_bytes frend   = MIN((rangeend), maxv);     \
        if (frend > frstart && (frend - frstart) >= length) { \
            startv = frend - length;                   \
            foundflag = 1;                             \
        }                                              \
    }

    #define FREEVRANGE(start, end) {                   \
        assert(!foundflag);                            \
        FREEVRANGE_TRY(((start) + VM_PAGE_SIZE), ((end) - VM_PAGE_SIZE)); \
        if (!foundflag) {                              \
            FREEVRANGE_TRY((start), (end));            \
        }                                              \
    }

    region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_GREATER_EQUAL);
    lastregion = region_get_iter(&iter);

    if (!lastregion) {
        region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_LESS);
        lastregion = region_get_iter(&iter);
        FREEVRANGE(lastregion ? lastregion->vaddr + lastregion->length : 0, VM_DATATOP);
    }

    if (!foundflag) {
        struct vir_region *vr;
        while ((vr = region_get_iter(&iter)) && !foundflag) {
            struct vir_region *nextvr;
            region_decr_iter(&iter);
            nextvr = region_get_iter(&iter);
            FREEVRANGE(nextvr ? nextvr->vaddr + nextvr->length : 0, vr->vaddr);
        }
    }

    if (!foundflag) {
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

    if (maxv != 0 && hint < maxv && hint >= minv) {
        vir_bytes v = region_find_slot_range(vmp, minv, hint, length);
        if (v != SLOT_FAIL) {
            return v;
        }
    }

    return region_find_slot_range(vmp, minv, maxv, length);
}

#include <assert.h>

#define VM_PAGE_SIZE 4096

static unsigned int phys_slot(vir_bytes len) {
	if (len % VM_PAGE_SIZE != 0) {
		return 0; // Error handling if necessary
	}
	return len / VM_PAGE_SIZE;
}

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

struct vir_region {
    vir_bytes vaddr;
    vir_bytes length;
    int flags;
    mem_type_t *def_memtype;
    int remaps;
    u32_t id;
    struct vir_region *lower, *higher;
    struct vmproc *parent;
    struct phys_region **physblocks;
};

struct vmproc {};
struct phys_region {};
typedef unsigned int u32_t;
typedef unsigned int vir_bytes;
typedef int mem_type_t;

#define USE(ptr, operation) do { if (ptr) { operation; } } while (0)
#define SLABALLOC(ptr) ((ptr = malloc(sizeof(*ptr))) != NULL)
#define SLABFREE(ptr) free(ptr)
#define phys_slot(length) ((length) / sizeof(struct phys_region *)) // Placeholder definition

struct vir_region *region_new(struct vmproc *vmp, vir_bytes startv, vir_bytes length,
    int flags, mem_type_t *memtype) {
    static u32_t id = 0;
    struct vir_region *newregion = NULL;
    struct phys_region **newphysregions = NULL;
    int slots = phys_slot(length);
    
    if (!SLABALLOC(newregion)) {
        fprintf(stderr, "vm: region_new: could not allocate\n");
        return NULL;
    }
    
    memset(newregion, 0, sizeof(*newregion));
    newregion->vaddr = startv;
    newregion->length = length;
    newregion->flags = flags;
    newregion->def_memtype = memtype;
    newregion->id = id++;
    newregion->parent = vmp;

    newphysregions = calloc(slots, sizeof(struct phys_region *));
    if (!newphysregions) {
        fprintf(stderr, "VM: region_new: allocating phys blocks failed\n");
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
	mem_type_t *memtype) {
	struct vir_region *newregion;
	vir_bytes startv;

	assert(length % VM_PAGE_SIZE == 0);

	startv = region_find_slot(vmp, minv, maxv, length);
	if (startv == SLOT_FAIL) {
		return NULL;
	}

	newregion = region_new(vmp, startv, length, flags, memtype);
	if (!newregion) {
		return NULL;
	}

	if (newregion->def_memtype->ev_new) {
		if (newregion->def_memtype->ev_new(newregion) != OK) {
			return NULL;
		}
	}

	if (mapflags & MF_PREALLOC) {
		if (map_handle_memory(vmp, newregion, 0, length, 1, NULL, 0, 0) != OK) {
			map_free(newregion);
			return NULL;
		}
	}

	newregion->flags &= ~VR_UNINITIALIZED;

	region_insert(&vmp->vm_regions_avl, newregion);

	return newregion;
}

/*===========================================================================*
 *				map_subfree				     *
 *===========================================================================*/
#include <assert.h>

static int map_subfree(struct vir_region *region, vir_bytes start, vir_bytes len) {
    struct phys_region *pr;
    vir_bytes end = start + len;
    vir_bytes voffset;

#if SANITYCHECKS
    SLABSANE(region);
    for (voffset = 0; voffset < phys_slot(region->length); voffset += VM_PAGE_SIZE) {
        struct phys_region *others;
        struct phys_block *pb;

        if (!(pr = physblock_get(region, voffset))) {
            continue;
        }

        pb = pr->ph;

        for (others = pb->firstregion; others; others = others->next_ph_list) {
            assert(others->ph == pb);
        }
    }
#endif

    for (voffset = start; voffset < end; voffset += VM_PAGE_SIZE) {
        pr = physblock_get(region, voffset);
        if (!pr) {
            continue;
        }
        assert(pr->offset >= start && pr->offset < end);
        pb_unreferenced(region, pr, 1);
        SLABFREE(pr);
    }

    return OK;
}

/*===========================================================================*
 *				map_free				     *
 *===========================================================================*/
int map_free(struct vir_region *region) {
    int result = map_subfree(region, 0, region->length);
    if (result != OK) {
        printf("Error at line %d\n", __LINE__);
        return result;
    }

    if (region->def_memtype->ev_delete) {
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
	struct vir_region *region;

	while ((region = region_search_root(&vmp->vm_regions_avl)) != NULL) {
#if SANITYCHECKS
		nocheck++;
#endif
		region_remove(&vmp->vm_regions_avl, region->vaddr);
		map_free(region);
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
struct vir_region *map_lookup(struct vmproc *vmp, vir_bytes offset, struct phys_region **physr) {
    SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS
    if (!region_search_root(&vmp->vm_regions_avl)) {
        panic("process has no regions: %d", vmp->vm_endpoint);
    }
#endif

    struct vir_region *r = region_search(&vmp->vm_regions_avl, offset, AVL_LESS_EQUAL);
    if (r && offset >= r->vaddr && offset < r->vaddr + r->length) {
        vir_bytes ph = offset - r->vaddr;
        if (physr) {
            *physr = physblock_get(r, ph);
            if (*physr && (*physr)->offset != ph) {
                assert((*physr)->offset == ph);
            }
        }
        return r;
    }

    SANITYCHECK(SCL_FUNCTIONS);

    return NULL;
}

u32_t vrallocflags(u32_t flags) {
    u32_t allocflags = 0;

    if (flags & VR_PHYS64K) allocflags |= PAF_ALIGN64K;
    if (flags & VR_LOWER16MB) allocflags |= PAF_LOWER16MB;
    if (flags & VR_LOWER1MB) allocflags |= PAF_LOWER1MB;
    if ((flags & VR_UNINITIALIZED) == 0) allocflags |= PAF_CLEAR;

    return allocflags;
}

/*===========================================================================*
 *				map_pf			     *
 *===========================================================================*/
int map_pf(struct vmproc *vmp, struct vir_region *region, vir_bytes offset, int write, vfs_callback_t pf_callback, void *state, int len, int *io) {
	struct phys_region *ph = NULL;
	int result = OK;
	int is_writable_region = region->flags & VR_WRITABLE;
	int offset_mod_page_size = offset % VM_PAGE_SIZE;

	offset -= offset_mod_page_size;

	if (offset < 0 || offset >= region->length || (write && !is_writable_region)) {
		return FAIL;
	}

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

	if (write && ph->memtype->writable(ph)) {
		result = OK;
	} else if (!ph->memtype->ev_pagefault || (result = ph->memtype->ev_pagefault(vmp, region, ph, write, pf_callback, state, len, io)) != OK) {
		if (result == SUSPEND) {
			return SUSPEND;
		}
		printf("map_pf: pagefault failed\n");
		pb_unreferenced(region, ph, 1);
		return result;
	}

	if (map_ph_writept(vmp, region, ph) != OK) {
		printf("map_pf: writept failed\n");
		return FAIL;
	}

	SANITYCHECK(SCL_FUNCTIONS);

#if SANITYCHECKS	
	if (OK != pt_checkrange(&vmp->vm_pt, region->vaddr + offset, VM_PAGE_SIZE, write)) {
		panic("map_pf: pt_checkrange failed: %d", result);
	}
#endif

	return result;
}

int map_handle_memory(struct vmproc *vmp, struct vir_region *region, vir_bytes start_offset, 
                       vir_bytes length, int write, vfs_callback_t cb, void *state, int statelen) {
    vir_bytes offset;
    int result;
    int io = 0;

    if (length <= 0 || start_offset + length < start_offset) {
        return -1; // or another appropriate error code
    }

    for (offset = start_offset; offset < start_offset + length; offset += VM_PAGE_SIZE) {
        result = map_pf(vmp, region, offset, write, cb, state, statelen, &io);
        if (result != OK) {
            return result;
        }
    }

    return OK;
}

/*===========================================================================*
 *				map_pin_memory      			     *
 *===========================================================================*/
int map_pin_memory(struct vmproc *vmp) {
    struct vir_region *vr;
    int r;
    region_iter iter;

    if (!pt_assert(&vmp->vm_pt)) {
        return ERROR;  // Handle error if page table assertion fails
    }

    region_start_iter_least(&vmp->vm_regions_avl, &iter);

    while ((vr = region_get_iter(&iter)) != NULL) {
        r = map_handle_memory(vmp, vr, 0, vr->length, 1, NULL, 0, 0);
        
        if (r != OK) {
            return r;  // Return error code instead of calling panic
        }
        
        region_incr_iter(&iter);
    }

    if (!pt_assert(&vmp->vm_pt)) {
        return ERROR;  // Handle error if page table assertion fails
    }

    return OK;
}

/*===========================================================================*
 *				map_copy_region			     	*
 *===========================================================================*/
struct vir_region *map_copy_region(struct vmproc *vmp, struct vir_region *vr) {
    struct vir_region *newvr = region_new(vr->parent, vr->vaddr, vr->length, vr->flags, vr->def_memtype);
    if (!newvr) return NULL;

    newvr->parent = vmp;

    if (vr->def_memtype->ev_copy) {
        int r = vr->def_memtype->ev_copy(vr, newvr);
        if (r != OK) {
            map_free(newvr);
            printf("VM: memtype-specific copy failed (%d)\n", r);
            return NULL;
        }
    }

    for (vir_bytes p = 0; p < phys_slot(vr->length); p++) {
        struct phys_region *ph = physblock_get(vr, p * VM_PAGE_SIZE);
        if (!ph) continue;

        struct phys_region *newph = pb_reference(ph->ph, ph->offset, newvr, vr->def_memtype);
        if (!newph) {
            map_free(newvr);
            return NULL;
        }

        if (ph->memtype->ev_reference) {
            ph->memtype->ev_reference(ph, newph);
        }
    }

    return newvr;
}

/*===========================================================================*
 *				copy_abs2region			     	*
 *===========================================================================*/
int copy_abs2region(phys_bytes absaddr, struct vir_region *destregion, phys_bytes offset, phys_bytes len) {
	if (!destregion || !destregion->physblocks) {
		fprintf(stderr, "Invalid destination region.\n");
		return EFAULT;
	}

	while (len > 0) {
		struct phys_region *ph = physblock_get(destregion, offset);
		if (!ph || ph->offset > offset || ph->offset + VM_PAGE_SIZE <= offset) {
			fprintf(stderr, "VM: copy_abs2region: no valid phys region found.\n");
			return EFAULT;
		}

		phys_bytes suboffset = offset - ph->offset;
		phys_bytes sublen = len < (VM_PAGE_SIZE - suboffset) ? len : (VM_PAGE_SIZE - suboffset);

		if (ph->ph->refcount != 1) {
			fprintf(stderr, "VM: copy_abs2region: refcount not 1.\n");
			return EFAULT;
		}

		int abscopy_result = sys_abscopy(absaddr, ph->ph->phys + suboffset, sublen);
		if (abscopy_result != OK) {
			fprintf(stderr, "VM: copy_abs2region: abscopy failed with error %d.\n", abscopy_result);
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
int map_writept(struct vmproc *vmp) {
    int r;
    region_iter v_iter;
    struct vir_region *vr;
    struct phys_region *ph;

    region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

    while ((vr = region_get_iter(&v_iter)) != NULL) {
        for (vir_bytes p = 0; p < vr->length; p += VM_PAGE_SIZE) {
            ph = physblock_get(vr, p);
            if (ph == NULL) {
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
    if (dst == NULL || src == NULL) {
        return -1; // Return error code for invalid input
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

	start_src_vr = start_src_vr ? start_src_vr : region_search_least(&src->vm_regions_avl);
	end_src_vr = end_src_vr ? end_src_vr : region_search_greatest(&src->vm_regions_avl);

	if (!start_src_vr || !end_src_vr || start_src_vr->parent != src) return EINVAL;

	region_start_iter(&src->vm_regions_avl, &v_iter, start_src_vr->vaddr, AVL_EQUAL);

	if (region_get_iter(&v_iter) != start_src_vr) return EINVAL;

	SANITYCHECK(SCL_FUNCTIONS);

	while ((vr = region_get_iter(&v_iter))) {
		struct vir_region *newvr = map_copy_region(dst, vr);
		if (!newvr) {
			map_free_proc(dst);
			return ENOMEM;
		}
		region_insert(&dst->vm_regions_avl, newvr);

#if SANITYCHECKS
		for (vir_bytes vaddr = 0; vaddr < vr->length; vaddr += VM_PAGE_SIZE) {
			struct phys_region *orig_ph = physblock_get(vr, vaddr);
			struct phys_region *new_ph = physblock_get(newvr, vaddr);
			if (orig_ph) {
				assert(new_ph && orig_ph != new_ph && orig_ph->ph == new_ph->ph);
			} else {
				assert(!new_ph);
			}
		}
#endif
		if (vr == end_src_vr) break;
		region_incr_iter(&v_iter);
	}

	map_writept(src);
	map_writept(dst);

	SANITYCHECK(SCL_FUNCTIONS);
	return OK;
}

int map_region_extend_upto_v(struct vmproc *vmp, vir_bytes target_vaddr) {
    vir_bytes aligned_offset = roundup(target_vaddr, VM_PAGE_SIZE);
    struct vir_region *curr_region, *next_region;
    struct phys_region **updated_physblocks;
    int required_slots, current_slots, additional_slots, result;

    curr_region = region_search(&vmp->vm_regions_avl, aligned_offset, AVL_LESS);
    if (!curr_region) {
        printf("VM: nothing to extend\n");
        return ENOMEM;
    }

    if (curr_region->vaddr + curr_region->length >= target_vaddr) {
        return OK;
    }

    vir_bytes current_limit = curr_region->vaddr + curr_region->length;
    vir_bytes extra_length = aligned_offset - current_limit;
    assert(curr_region->vaddr <= aligned_offset && extra_length > 0);

    required_slots = phys_slot(aligned_offset - curr_region->vaddr);
    current_slots = phys_slot(curr_region->length);
    additional_slots = required_slots - current_slots;
    assert(required_slots >= current_slots);

    next_region = getnextvr(curr_region);
    if (next_region && next_region->vaddr < aligned_offset) {
        printf("VM: can't grow into next region\n");
        return ENOMEM;
    }

    if (!curr_region->def_memtype->ev_resize) {
        if (!map_page_region(vmp, current_limit, 0, extra_length, VR_WRITABLE | VR_ANON, 0, &mem_type_anon)) {
            printf("resize: couldn't put anon memory there\n");
            return ENOMEM;
        }
        return OK;
    }

    updated_physblocks = realloc(curr_region->physblocks, required_slots * sizeof(struct phys_region *));
    if (!updated_physblocks) {
        printf("VM: map_region_extend_upto_v: realloc failed\n");
        return ENOMEM;
    }

    curr_region->physblocks = updated_physblocks;
    memset(curr_region->physblocks + current_slots, 0, additional_slots * sizeof(struct phys_region *));

    result = curr_region->def_memtype->ev_resize(vmp, curr_region, aligned_offset - curr_region->vaddr);
    return result;
}

/*========================================================================*
 *				map_unmap_region	     	  	*
 *========================================================================*/
int map_unmap_region(struct vmproc *vmp, struct vir_region *r, vir_bytes offset, vir_bytes len) {
    vir_bytes regionstart;
    int freeslots;

    SANITYCHECK(SCL_FUNCTIONS);

    // Validate input
    if (offset + len > r->length || len % VM_PAGE_SIZE != 0) {
        printf("VM: invalid length 0x%lx\n", len);
        return EINVAL;
    }

    regionstart = r->vaddr + offset;
    freeslots = phys_slot(len);

    // Free memory associated with the region
    map_subfree(r, offset, len);

    // Handle different cases of region shrinking
    if (r->length == len) {
        // Entire region is removed
        region_remove(&vmp->vm_regions_avl, r->vaddr);
        map_free(r);
    } else if (offset == 0) {
        // Shrink from the lower end
        if (!r->def_memtype->ev_lowshrink || r->def_memtype->ev_lowshrink(r, len) != OK) {
            printf("VM: low-shrinking failed for %s\n", r->def_memtype->name);
            return EINVAL;
        }

        region_remove(&vmp->vm_regions_avl, r->vaddr);
        r->vaddr += len;
        region_insert(&vmp->vm_regions_avl, r);

        int remslots = phys_slot(r->length);
        for (vir_bytes voffset = len; voffset < r->length; voffset += VM_PAGE_SIZE) {
            struct phys_region *pr = physblock_get(r, voffset);
            if (pr) {
                pr->offset -= len;
            }
        }
        if (remslots > 0) {
            memmove(r->physblocks, r->physblocks + freeslots, remslots * sizeof(struct phys_region *));
        }
        r->length -= len;
    } else if (offset + len == r->length) {
        // Shrink from the upper end
        r->length -= len;
    }

    SANITYCHECK(SCL_DETAIL);

    // Update page table mappings
    if (pt_writemap(vmp, &vmp->vm_pt, regionstart, MAP_NONE, len, 0, WMF_OVERWRITE) != OK) {
        printf("VM: map_unmap_region: pt_writemap failed\n");
        return ENOMEM;
    }

    SANITYCHECK(SCL_FUNCTIONS);

    return OK;
}

static int split_region(struct vmproc *vmp, struct vir_region *vr,
    struct vir_region **vr1, struct vir_region **vr2, vir_bytes split_len)
{
    assert(vr && vr1 && vr2);
    assert(!(split_len % VM_PAGE_SIZE));
    assert(!((vr->length - split_len) % VM_PAGE_SIZE));
    assert(!(vr->vaddr % VM_PAGE_SIZE));
    assert(!(vr->length % VM_PAGE_SIZE));

    if (!vr->def_memtype->ev_split) {
        fprintf(stderr, "VM: split region not implemented for %s\n", vr->def_memtype->name);
        sys_diagctl_stacktrace(vmp->vm_endpoint);
        return EINVAL;
    }

    vir_bytes rem_len = vr->length - split_len;
    struct vir_region *r1 = region_new(vmp, vr->vaddr, split_len, vr->flags, vr->def_memtype);
    struct vir_region *r2 = region_new(vmp, vr->vaddr + split_len, rem_len, vr->flags, vr->def_memtype);

    if (!r1 || !r2) {
        map_free(r1);
        map_free(r2);
        fprintf(stderr, "split_region: failed to allocate regions\n");
        return ENOMEM;
    }

    vir_bytes voffset;
    for (voffset = 0; voffset < r1->length; voffset += VM_PAGE_SIZE) {
        struct phys_region *ph = physblock_get(vr, voffset);
        if (ph && !pb_reference(ph->ph, voffset, r1, ph->memtype)) {
            map_free(r1);
            map_free(r2);
            fprintf(stderr, "split_region: failed to reference phys region for r1\n");
            return ENOMEM;
        }
    }

    for (voffset = 0; voffset < r2->length; voffset += VM_PAGE_SIZE) {
        struct phys_region *ph = physblock_get(vr, split_len + voffset);
        if (ph && !pb_reference(ph->ph, voffset, r2, ph->memtype)) {
            map_free(r1);
            map_free(r2);
            fprintf(stderr, "split_region: failed to reference phys region for r2\n");
            return ENOMEM;
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
}

int map_unmap_range(struct vmproc *vmp, vir_bytes unmap_start, vir_bytes length) {
    if (length < 1) return EINVAL; 

    vir_bytes unmap_limit = unmap_start + length;
    if (unmap_limit <= unmap_start || length % VM_PAGE_SIZE != 0) return EINVAL;

    region_iter v_iter;
    region_start_iter(&vmp->vm_regions_avl, &v_iter, unmap_start, AVL_LESS_EQUAL);

    struct vir_region *vr = region_get_iter(&v_iter);
    if (!vr) {
        region_start_iter(&vmp->vm_regions_avl, &v_iter, unmap_start, AVL_GREATER);
        vr = region_get_iter(&v_iter);
        if (!vr) return OK;
    }

    while (vr && vr->vaddr < unmap_limit) {
        vir_bytes thislimit = vr->vaddr + vr->length;
        vir_bytes this_unmap_start = MAX(unmap_start, vr->vaddr);
        vir_bytes this_unmap_limit = MIN(unmap_limit, thislimit);

        if (this_unmap_start < this_unmap_limit) {
            if (this_unmap_start > vr->vaddr && this_unmap_limit < thislimit) {
                struct vir_region *vr1, *vr2;
                vir_bytes split_len = this_unmap_limit - vr->vaddr;
                if (split_region(vmp, vr, &vr1, &vr2, split_len) != OK) {
                    fprintf(stderr, "map_unmap_range: split_region failed\n");
                    return ERR_SPLIT;
                }
                vr = vr1;
                thislimit = vr->vaddr + vr->length;
            }

            vir_bytes unmap_len = this_unmap_limit - this_unmap_start;
            if (map_unmap_region(vmp, vr, this_unmap_start - vr->vaddr, unmap_len) != OK) {
                fprintf(stderr, "map_unmap_range: map_unmap_region failed\n");
                return ERR_UNMAP;
            }
        }

        region_incr_iter(&v_iter);
        vr = region_get_iter(&v_iter);
    }

    return OK;
}

/*========================================================================*
 *			  map_region_lookup_type			  *
 *========================================================================*/
struct vir_region* map_region_lookup_type(struct vmproc *vmp, u32_t type) {
    region_iter v_iter;
    region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

    while (struct vir_region *vr = region_get_iter(&v_iter)) {
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
	struct vir_region *vr = map_lookup(vmp, addr, NULL);

	if (!vr)
		return EINVAL;

	if (vr->vaddr != addr)
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
int map_get_ref(struct vmproc *vmp, vir_bytes addr, u8_t *cnt) {
    struct vir_region *vr = map_lookup(vmp, addr, NULL);

    if (vr == NULL || vr->vaddr != addr || vr->def_memtype->refcount == NULL) {
        return EINVAL;
    }

    if (cnt != NULL) {
        *cnt = vr->def_memtype->refcount(vr);
    }

    return OK;
}

void get_usage_info_kernel(struct vm_usage_info *vui) {
    if (!vui) return;
    
    vui->vui_total = kernel_boot_info.kernel_allocated_bytes + 
                     kernel_boot_info.kernel_allocated_bytes_dynamic;
    vui->vui_virtual = vui->vui_mvirtual = vui->vui_total;
}

#include <string.h>

static void get_usage_info_vm(struct vm_usage_info *vui) {
    if (vui == NULL) {
        return;
    }

    memset(vui, 0, sizeof(*vui));
    vui->vui_total = kernel_boot_info.vm_allocated_bytes + (get_vm_self_pages() * VM_PAGE_SIZE);
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
static int is_stack_region(struct vir_region *vr) {
    if (vr == NULL) return 0;
    return (vr->vaddr == VM_STACKTOP - DEFAULT_STACK_LIMIT &&
            vr->length == DEFAULT_STACK_LIMIT);
}

/*========================================================================*
 *				get_usage_info				  *
 *========================================================================*/
#include <string.h>
#include <stddef.h>

#define VM_PAGE_SIZE 4096
#define VM_PROC_NR 0

void get_usage_info(struct vmproc *vmp, struct vm_usage_info *vui) {
    if (!vmp || !vui) return;

    memset(vui, 0, sizeof(*vui));

    if (vmp->vm_endpoint == VM_PROC_NR) {
        get_usage_info_vm(vui);
        return;
    }

    if (vmp->vm_endpoint < 0) {
        get_usage_info_kernel(vui);
        return;
    }

    struct vir_region *vr = NULL;
    region_iter v_iter;
    region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

    while ((vr = region_get_iter(&v_iter)) != NULL) {
        vui->vui_virtual += vr->length;
        vui->vui_mvirtual += vr->length;

        for (vir_bytes voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
            struct phys_region *ph = physblock_get(vr, voffset);

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
int get_region_info(struct vmproc *vmp, struct vm_region_info *vri, int max, vir_bytes *nextp) {
    struct vir_region *vr;
    vir_bytes next;
    int count = 0;
    region_iter v_iter;

    next = *nextp;

    if (max <= 0) return 0;

    region_start_iter(&vmp->vm_regions_avl, &v_iter, next, AVL_GREATER_EQUAL);

    while ((vr = region_get_iter(&v_iter)) && count < max) {
        struct phys_region *ph1 = NULL, *ph2 = NULL;
        vir_bytes voffset, region_end;

        region_end = vr->vaddr + vr->length;
        next = region_end;

        for (voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
            struct phys_region *ph = physblock_get(vr, voffset);
            if (ph) {
                if (!ph1) ph1 = ph;
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
            printf("skipping empty region 0x%lx-0x%lx\n", vr->vaddr, region_end);
        }

        region_incr_iter(&v_iter);
    }

    *nextp = next;
    return count;
}

/*========================================================================*
 *				regionprintstats			  *
 *========================================================================*/
void printregionstats(struct vmproc *vmp) {
    struct vir_region *vr;
    vir_bytes used = 0, weighted = 0;
    region_iter v_iter;
    region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

    while ((vr = region_get_iter(&v_iter)) != NULL) {
        region_incr_iter(&v_iter);
        if (vr->flags & VR_DIRECT) continue;

        for (vir_bytes voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
            struct phys_region *pr = physblock_get(vr, voffset);
            if (pr == NULL) continue;

            used += VM_PAGE_SIZE;
            if (pr->ph->refcount > 0) {
                weighted += VM_PAGE_SIZE / pr->ph->refcount;
            }
        }
    }

    printf("%6lukB  %6lukB\n", used / 1024, weighted / 1024);
}

void map_setparent(struct vmproc *vmp) {
    region_iter iter;
    struct vir_region *vr;
    if (!vmp) return; // Error handling: ensure vmp is not NULL
    region_start_iter_least(&vmp->vm_regions_avl, &iter);
    while ((vr = region_get_iter(&iter)) != NULL) {
        vr->parent = vmp;
        region_incr_iter(&iter);
    }
}

unsigned int physregions(struct vir_region *vr) {
    if (vr == NULL) {
        return 0;
    }
    unsigned int n = 0;
    vir_bytes voffset = 0;
    while (voffset < vr->length) {
        if (physblock_get(vr, voffset)) {
            n++;
        }
        voffset += VM_PAGE_SIZE;
    }
    return n;
}
