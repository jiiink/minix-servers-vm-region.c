
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

static const char* get_writable_string(int is_writable)
{
	return is_writable ? "writable" : "readonly";
}

static const char* get_permission_string(struct vmproc *parent, vir_bytes addr)
{
	return pt_writable(parent, addr) ? "W" : "R";
}

static void print_region_header(struct vir_region *vr)
{
	printf("map_printmap: map_name: %s\n", vr->def_memtype->name);
	printf("\t%lx (len 0x%lx, %lukB), %p, %s\n",
		vr->vaddr, vr->length, vr->length/1024,
		vr->def_memtype->name,
		get_writable_string(vr->flags & VR_WRITABLE));
}

static void print_phys_block(struct vir_region *vr, struct phys_region *ph)
{
	vir_bytes block_addr = vr->vaddr + ph->offset;
	printf("\t\t@ %lx (refs %d): phys 0x%lx, %s\n",
		block_addr,
		ph->ph->refcount, 
		ph->ph->phys,
		get_permission_string(vr->parent, block_addr));
}

static void print_phys_blocks(struct vir_region *vr)
{
	unsigned int num_pages = vr->length / VM_PAGE_SIZE;
	unsigned int i;
	struct phys_region *ph;
	
	printf("\t\tphysblocks:\n");
	for(i = 0; i < num_pages; i++) {
		ph = vr->physblocks[i];
		if(!ph) continue;
		print_phys_block(vr, ph);
	}
}

static void map_printregion(struct vir_region *vr)
{
	print_region_header(vr);
	print_phys_blocks(vr);
}

struct phys_region *physblock_get(struct vir_region *region, vir_bytes offset)
{
	assert(!(offset % VM_PAGE_SIZE));
	assert(offset < region->length);
	
	int i = offset / VM_PAGE_SIZE;
	struct phys_region *foundregion = region->physblocks[i];
	
	if (foundregion) {
		assert(foundregion->offset == offset);
	}
	
	return foundregion;
}

void physblock_set(struct vir_region *region, vir_bytes offset,
	struct phys_region *newphysr)
{
	assert(!(offset % VM_PAGE_SIZE));
	assert(offset < region->length);
	
	int i = offset / VM_PAGE_SIZE;
	struct vmproc *proc = region->parent;
	assert(proc);
	
	if (newphysr) {
		add_physblock(region, proc, newphysr, i, offset);
	} else {
		remove_physblock(region, proc, i);
	}
	
	region->physblocks[i] = newphysr;
}

static void add_physblock(struct vir_region *region, struct vmproc *proc,
	struct phys_region *newphysr, int i, vir_bytes offset)
{
	assert(!region->physblocks[i]);
	assert(newphysr->offset == offset);
	update_vm_total(proc, VM_PAGE_SIZE);
}

static void remove_physblock(struct vir_region *region, struct vmproc *proc, int i)
{
	assert(region->physblocks[i]);
	update_vm_total(proc, -VM_PAGE_SIZE);
}

static void update_vm_total(struct vmproc *proc, int delta)
{
	proc->vm_total += delta;
	if (proc->vm_total > proc->vm_total_max) {
		proc->vm_total_max = proc->vm_total;
	}
}

/*===========================================================================*
 *				map_printmap				     *
 *===========================================================================*/
void map_printmap(struct vmproc *vmp)
{
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
	struct vir_region *nextvr;
	region_iter v_iter;
	
	SLABSANE(vr);
	
	region_start_iter(&vr->parent->vm_regions_avl, &v_iter, vr->vaddr, AVL_EQUAL);
	assert(region_get_iter(&v_iter));
	assert(region_get_iter(&v_iter) == vr);
	
	region_incr_iter(&v_iter);
	nextvr = region_get_iter(&v_iter);
	
	if(!nextvr) return NULL;
	
	SLABSANE(nextvr);
	assert(vr->parent == nextvr->parent);
	assert(vr->vaddr < nextvr->vaddr);
	assert(vr->vaddr + vr->length <= nextvr->vaddr);
	
	return nextvr;
}

static int pr_writable(struct vir_region *vr, struct phys_region *pr)
{
	assert(pr->memtype->writable);
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
	struct phys_block *pb = pr->ph;

	assert(vr);
	assert(pr);
	assert(pb);
	assert(!(vr->vaddr % VM_PAGE_SIZE));
	assert(!(pr->offset % VM_PAGE_SIZE));
	assert(pb->refcount > 0);

	int flags = build_page_flags(vr, pr);
	int write_flags = get_write_flags(pr);

	if(pt_writemap(vmp, &vmp->vm_pt, vr->vaddr + pr->offset,
			pb->phys, VM_PAGE_SIZE, flags, write_flags) != OK) {
	    printf("VM: map_writept: pt_writemap failed\n");
	    return ENOMEM;
	}

	mark_page_written(pr);
	return OK;
}

static int build_page_flags(struct vir_region *vr, struct phys_region *pr)
{
	int flags = PTF_PRESENT | PTF_USER;
	
	if(pr_writable(vr, pr))
		flags |= PTF_WRITE;
	else
		flags |= PTF_READ;

	if(vr->def_memtype->pt_flags)
		flags |= vr->def_memtype->pt_flags(vr);
		
	return flags;
}

static int get_write_flags(struct phys_region *pr)
{
#if SANITYCHECKS
	return !pr->written ? 0 : WMF_OVERWRITE;
#else
	return WMF_OVERWRITE;
#endif
}

static void mark_page_written(struct phys_region *pr)
{
#if SANITYCHECKS
	USE(pr, pr->written = 1;);
#endif
}

#define SLOT_FAIL ((vir_bytes) -1)

/*===========================================================================*
 *				region_find_slot_range			     *
 *===========================================================================*/
static vir_bytes validate_maxv(vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
    if (maxv == 0) {
        maxv = minv + length;
        if (maxv <= minv) {
            printf("region_find_slot: minv 0x%lx and bytes 0x%lx\n", minv, length);
            return 0;
        }
    }
    return maxv;
}

static int validate_inputs(vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
    assert(!(length % VM_PAGE_SIZE));
    if (minv >= maxv) {
        printf("VM: 1 minv: 0x%lx maxv: 0x%lx length: 0x%lx\n", minv, maxv, length);
    }
    assert(minv < maxv);
    return (minv + length <= maxv);
}

static vir_bytes max_value(vir_bytes a, vir_bytes b)
{
    return (a > b) ? a : b;
}

static vir_bytes min_value(vir_bytes a, vir_bytes b)
{
    return (a < b) ? a : b;
}

static int try_free_range(vir_bytes rangestart, vir_bytes rangeend, 
                          vir_bytes minv, vir_bytes maxv, vir_bytes length,
                          vir_bytes *startv)
{
    vir_bytes frstart = max_value(rangestart, minv);
    vir_bytes frend = min_value(rangeend, maxv);
    
    if (frend > frstart && (frend - frstart) >= length) {
        *startv = frend - length;
        return 1;
    }
    return 0;
}

static int find_free_range(vir_bytes start, vir_bytes end,
                          vir_bytes minv, vir_bytes maxv, vir_bytes length,
                          vir_bytes *startv)
{
    if (try_free_range(start + VM_PAGE_SIZE, end - VM_PAGE_SIZE, 
                      minv, maxv, length, startv)) {
        return 1;
    }
    return try_free_range(start, end, minv, maxv, length, startv);
}

static int search_after_maxv(struct vmproc *vmp, vir_bytes maxv,
                            vir_bytes minv, vir_bytes length, vir_bytes *startv)
{
    region_iter iter;
    struct vir_region *lastregion;
    
    region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_GREATER_EQUAL);
    lastregion = region_get_iter(&iter);
    
    if (!lastregion) {
        region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_LESS);
        lastregion = region_get_iter(&iter);
        vir_bytes start = lastregion ? lastregion->vaddr + lastregion->length : 0;
        return find_free_range(start, VM_DATATOP, minv, maxv, length, startv);
    }
    return 0;
}

static int search_between_regions(struct vmproc *vmp, vir_bytes maxv,
                                 vir_bytes minv, vir_bytes length, vir_bytes *startv)
{
    region_iter iter;
    struct vir_region *vr;
    
    region_start_iter(&vmp->vm_regions_avl, &iter, maxv, AVL_GREATER_EQUAL);
    region_get_iter(&iter);
    
    while ((vr = region_get_iter(&iter))) {
        struct vir_region *nextvr;
        region_decr_iter(&iter);
        nextvr = region_get_iter(&iter);
        vir_bytes start = nextvr ? nextvr->vaddr + nextvr->length : 0;
        
        if (find_free_range(start, vr->vaddr, minv, maxv, length, startv)) {
            return 1;
        }
    }
    return 0;
}

static vir_bytes region_find_slot_range(struct vmproc *vmp,
                                       vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
    vir_bytes startv = 0;
    
    SANITYCHECK(SCL_FUNCTIONS);
    assert(length > 0);
    
    maxv = validate_maxv(minv, maxv, length);
    if (maxv == 0) {
        return SLOT_FAIL;
    }
    
    if (!validate_inputs(minv, maxv, length)) {
        return SLOT_FAIL;
    }
    
    if (search_after_maxv(vmp, maxv, minv, length, &startv)) {
        assert(startv >= minv);
        assert(startv < maxv);
        assert(startv + length <= maxv);
        vmp->vm_region_top = startv + length;
        return startv;
    }
    
    if (search_between_regions(vmp, maxv, minv, length, &startv)) {
        assert(startv >= minv);
        assert(startv < maxv);
        assert(startv + length <= maxv);
        vmp->vm_region_top = startv + length;
        return startv;
    }
    
    return SLOT_FAIL;
}

/*===========================================================================*
 *				region_find_slot			     *
 *===========================================================================*/
static vir_bytes region_find_slot(struct vmproc *vmp,
		vir_bytes minv, vir_bytes maxv, vir_bytes length)
{
	vir_bytes hint = vmp->vm_region_top;
	
	if(maxv && hint < maxv && hint >= minv) {
		vir_bytes v = region_find_slot_range(vmp, minv, hint, length);
		if(v != SLOT_FAIL)
			return v;
	}
	
	return region_find_slot_range(vmp, minv, maxv, length);
}

static unsigned int phys_slot(vir_bytes len)
{
	assert(!(len % VM_PAGE_SIZE));
	return len / VM_PAGE_SIZE;
}

static struct vir_region *allocate_region(void)
{
	struct vir_region *newregion;
	
	if(!(SLABALLOC(newregion))) {
		printf("vm: region_new: could not allocate\n");
		return NULL;
	}
	
	return newregion;
}

static void initialize_region(struct vir_region *newregion, struct vmproc *vmp,
	vir_bytes startv, vir_bytes length, int flags, mem_type_t *memtype)
{
	static u32_t id;
	
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
}

static struct phys_region **allocate_phys_blocks(int slots)
{
	struct phys_region **newphysregions;
	
	if(!(newphysregions = calloc(slots, sizeof(struct phys_region *)))) {
		printf("VM: region_new: allocating phys blocks failed\n");
		return NULL;
	}
	
	return newphysregions;
}

static struct vir_region *region_new(struct vmproc *vmp, vir_bytes startv, vir_bytes length,
	int flags, mem_type_t *memtype)
{
	struct vir_region *newregion;
	struct phys_region **newphysregions;
	int slots = phys_slot(length);

	newregion = allocate_region();
	if(!newregion) {
		return NULL;
	}

	initialize_region(newregion, vmp, startv, length, flags, memtype);

	newphysregions = allocate_phys_blocks(slots);
	if(!newphysregions) {
		SLABFREE(newregion);
		return NULL;
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
	struct vir_region *newregion;
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

	if (!invoke_new_event(newregion))
		return NULL;

	if (!handle_preallocation(vmp, newregion, mapflags, length))
		return NULL;

	USE(newregion, newregion->flags &= ~VR_UNINITIALIZED;);

	region_insert(&vmp->vm_regions_avl, newregion);

	validate_region_placement(newregion, startv);

	SANITYCHECK(SCL_FUNCTIONS);

	return newregion;
}

static int invoke_new_event(struct vir_region *newregion)
{
	if (!newregion->def_memtype->ev_new)
		return 1;

	if (newregion->def_memtype->ev_new(newregion) != OK)
		return 0;

	return 1;
}

static int handle_preallocation(struct vmproc *vmp, struct vir_region *newregion, 
	int mapflags, vir_bytes length)
{
	if (!(mapflags & MF_PREALLOC))
		return 1;

	if (map_handle_memory(vmp, newregion, 0, length, 1, NULL, 0, 0) != OK) {
		printf("VM: map_page_region: prealloc failed\n");
		map_free(newregion);
		return 0;
	}

	return 1;
}

static void validate_region_placement(struct vir_region *newregion, vir_bytes startv)
{
#if SANITYCHECKS
	assert(startv == newregion->vaddr);
	
	struct vir_region *nextvr = getnextvr(newregion);
	if (nextvr) {
		assert(newregion->vaddr < nextvr->vaddr);
	}
#endif
}

/*===========================================================================*
 *				map_subfree				     *
 *===========================================================================*/
static int map_subfree(struct vir_region *region, 
	vir_bytes start, vir_bytes len)
{
	vir_bytes end = start + len;

#if SANITYCHECKS
	SLABSANE(region);
	validate_region_physblocks(region);
#endif

	free_physblocks_in_range(region, start, end);
	return OK;
}

#if SANITYCHECKS
static void validate_region_physblocks(struct vir_region *region)
{
	vir_bytes voffset;
	
	for(voffset = 0; voffset < phys_slot(region->length); voffset += VM_PAGE_SIZE) {
		validate_single_physblock(region, voffset);
	}
}

static void validate_single_physblock(struct vir_region *region, vir_bytes voffset)
{
	struct phys_region *pr;
	struct phys_block *pb;
	struct phys_region *others;
	
	if(!(pr = physblock_get(region, voffset)))
		return;
		
	pb = pr->ph;
	
	for(others = pb->firstregion; others; others = others->next_ph_list) {
		assert(others->ph == pb);
	}
}
#endif

static void free_physblocks_in_range(struct vir_region *region, vir_bytes start, vir_bytes end)
{
	vir_bytes voffset;
	
	for(voffset = start; voffset < end; voffset += VM_PAGE_SIZE) {
		free_single_physblock(region, voffset, start, end);
	}
}

static void free_single_physblock(struct vir_region *region, vir_bytes voffset, vir_bytes start, vir_bytes end)
{
	struct phys_region *pr;
	
	if(!(pr = physblock_get(region, voffset)))
		return;
		
	assert(pr->offset >= start);
	assert(pr->offset < end);
	pb_unreferenced(region, pr, 1);
	SLABFREE(pr);
}

/*===========================================================================*
 *				map_free				     *
 *===========================================================================*/
int map_free(struct vir_region *region)
{
	int r;

	if((r=map_subfree(region, 0, region->length)) != OK) {
		return r;
	}

	if(region->def_memtype->ev_delete)
		region->def_memtype->ev_delete(region);
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
		free_single_region(vmp, r);
	}

	region_init(&vmp->vm_regions_avl);

	SANITYCHECK(SCL_FUNCTIONS);

	return OK;
}

static void free_single_region(struct vmproc *vmp, struct vir_region *r)
{
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

/*===========================================================================*
 *				map_lookup				     *
 *===========================================================================*/
struct vir_region *map_lookup(struct vmproc *vmp,
	vir_bytes offset, struct phys_region **physr)
{
	struct vir_region *r;

	SANITYCHECK(SCL_FUNCTIONS);
	validate_process_regions(vmp);

	r = region_search(&vmp->vm_regions_avl, offset, AVL_LESS_EQUAL);
	if (!r) {
		SANITYCHECK(SCL_FUNCTIONS);
		return NULL;
	}

	if (!is_offset_in_region(r, offset)) {
		SANITYCHECK(SCL_FUNCTIONS);
		return NULL;
	}

	if (physr) {
		set_physical_region(r, offset, physr);
	}

	return r;
}

static void validate_process_regions(struct vmproc *vmp)
{
#if SANITYCHECKS
	if (!region_search_root(&vmp->vm_regions_avl)) {
		panic("process has no regions: %d", vmp->vm_endpoint);
	}
#endif
}

static int is_offset_in_region(struct vir_region *r, vir_bytes offset)
{
	return (offset >= r->vaddr && offset < r->vaddr + r->length);
}

static void set_physical_region(struct vir_region *r, vir_bytes offset, 
	struct phys_region **physr)
{
	vir_bytes ph = offset - r->vaddr;
	*physr = physblock_get(r, ph);
	if (*physr) {
		assert((*physr)->offset == ph);
	}
}

u32_t vrallocflags(u32_t flags)
{
	static const struct {
		u32_t vr_flag;
		u32_t alloc_flag;
	} flag_mappings[] = {
		{ VR_PHYS64K, PAF_ALIGN64K },
		{ VR_LOWER16MB, PAF_LOWER16MB },
		{ VR_LOWER1MB, PAF_LOWER1MB }
	};
	
	u32_t allocflags = 0;
	size_t i;
	
	for (i = 0; i < sizeof(flag_mappings) / sizeof(flag_mappings[0]); i++) {
		if (flags & flag_mappings[i].vr_flag)
			allocflags |= flag_mappings[i].alloc_flag;
	}
	
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
	int r = OK;

	offset -= offset % VM_PAGE_SIZE;

	assert(offset < region->length);
	assert(!(region->vaddr % VM_PAGE_SIZE));
	assert(!(write && !(region->flags & VR_WRITABLE)));

	SANITYCHECK(SCL_FUNCTIONS);

	ph = physblock_get(region, offset);
	if (!ph) {
		ph = create_new_phys_region(region, offset);
		if (!ph) {
			return ENOMEM;
		}
	}

	assert(ph);
	assert(ph->ph);
	assert(ph->memtype->writable);

	if (should_handle_pagefault(write, ph)) {
		r = handle_pagefault(vmp, region, ph, write, pf_callback, state, len, io);
		if (r == SUSPEND) {
			return SUSPEND;
		}
		if (r != OK) {
			pb_unreferenced(region, ph, 1);
			return r;
		}
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
	perform_pt_check(vmp, region, offset, write);
#endif	

	return r;
}

static struct phys_region *create_new_phys_region(struct vir_region *region, vir_bytes offset)
{
	struct phys_block *pb;
	struct phys_region *ph;

	pb = pb_new(MAP_NONE);
	if (!pb) {
		printf("map_pf: pb_new failed\n");
		return NULL;
	}

	ph = pb_reference(pb, offset, region, region->def_memtype);
	if (!ph) {
		printf("map_pf: pb_reference failed\n");
		pb_free(pb);
		return NULL;
	}

	return ph;
}

static int should_handle_pagefault(int write, struct phys_region *ph)
{
	return !write || !ph->memtype->writable(ph);
}

static int handle_pagefault(struct vmproc *vmp, struct vir_region *region,
	struct phys_region *ph, int write, vfs_callback_t pf_callback,
	void *state, int len, int *io)
{
	assert(ph->memtype->ev_pagefault);
	assert(ph->ph);

	return ph->memtype->ev_pagefault(vmp, region, ph, write, pf_callback, state, len, io);
}

#if SANITYCHECKS
static void perform_pt_check(struct vmproc *vmp, struct vir_region *region,
	vir_bytes offset, int write)
{
	int r = pt_checkrange(&vmp->vm_pt, region->vaddr + offset, VM_PAGE_SIZE, write);
	if (r != OK) {
		panic("map_pf: pt_checkrange failed: %d", r);
	}
}
#endif

int map_handle_memory(struct vmproc *vmp,
	struct vir_region *region, vir_bytes start_offset, vir_bytes length,
	int write, vfs_callback_t cb, void *state, int statelen)
{
	vir_bytes offset, lim;
	int r;
	int io = 0;

	assert(length > 0);
	lim = start_offset + length;
	assert(lim > start_offset);

	for(offset = start_offset; offset < lim; offset += VM_PAGE_SIZE) {
		r = map_pf(vmp, region, offset, write, cb, state, statelen, &io);
		if(r != OK)
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
	region_iter iter;
	
	region_start_iter_least(&vmp->vm_regions_avl, &iter);
	pt_assert(&vmp->vm_pt);
	
	while((vr = region_get_iter(&iter))) {
		int r = map_handle_memory(vmp, vr, 0, vr->length, 1, NULL, 0, 0);
		if(r != OK) {
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
#if SANITYCHECKS
	unsigned int cr = physregions(vr);
#endif

	newvr = create_new_region(vmp, vr);
	if (!newvr)
		return NULL;

	if (!perform_memtype_copy(vr, newvr)) {
		map_free(newvr);
		return NULL;
	}

	if (!copy_phys_regions(vr, newvr)) {
		map_free(newvr);
		return NULL;
	}

#if SANITYCHECKS
	assert(physregions(vr) == physregions(newvr));
#endif

	return newvr;
}

static struct vir_region *create_new_region(struct vmproc *vmp, struct vir_region *vr)
{
	struct vir_region *newvr = region_new(vr->parent, vr->vaddr, vr->length, 
					      vr->flags, vr->def_memtype);
	if (newvr) {
		USE(newvr, newvr->parent = vmp;);
	}
	return newvr;
}

static int perform_memtype_copy(struct vir_region *vr, struct vir_region *newvr)
{
	int r;
	if (vr->def_memtype->ev_copy) {
		r = vr->def_memtype->ev_copy(vr, newvr);
		if (r != OK) {
			printf("VM: memtype-specific copy failed (%d)\n", r);
			return 0;
		}
	}
	return 1;
}

static int copy_phys_regions(struct vir_region *vr, struct vir_region *newvr)
{
	vir_bytes p;
	
	for (p = 0; p < phys_slot(vr->length); p++) {
		if (!copy_single_phys_region(vr, newvr, p))
			return 0;
	}
	return 1;
}

static int copy_single_phys_region(struct vir_region *vr, struct vir_region *newvr, vir_bytes p)
{
	struct phys_region *ph;
	struct phys_region *newph;
	
	ph = physblock_get(vr, p * VM_PAGE_SIZE);
	if (!ph)
		return 1;
	
	newph = pb_reference(ph->ph, ph->offset, newvr, vr->def_memtype);
	if (!newph)
		return 0;
	
	if (ph->memtype->ev_reference)
		ph->memtype->ev_reference(ph, newph);
	
#if SANITYCHECKS
	USE(newph, newph->written = 0;);
#endif
	
	return 1;
}

/*===========================================================================*
 *				copy_abs2region			     	*
 *===========================================================================*/
int copy_abs2region(phys_bytes absaddr, struct vir_region *destregion,
	phys_bytes offset, phys_bytes len)
{
	assert(destregion);
	assert(destregion->physblocks);
	
	while(len > 0) {
		phys_bytes sublen = copy_chunk_to_region(absaddr, destregion, offset, len);
		if(sublen == 0) {
			return EFAULT;
		}
		absaddr += sublen;
		offset += sublen;
		len -= sublen;
	}

	return OK;
}

static phys_bytes copy_chunk_to_region(phys_bytes absaddr, struct vir_region *destregion,
	phys_bytes offset, phys_bytes len)
{
	struct phys_region *ph = validate_phys_region(destregion, offset);
	if(!ph) {
		return 0;
	}

	phys_bytes suboffset = offset - ph->offset;
	phys_bytes sublen = calculate_copy_length(len, suboffset);
	
	if(!perform_copy(absaddr, ph, suboffset, sublen)) {
		return 0;
	}
	
	return sublen;
}

static struct phys_region* validate_phys_region(struct vir_region *destregion, phys_bytes offset)
{
	assert(destregion);
	assert(destregion->physblocks);
	
	struct phys_region *ph = physblock_get(destregion, offset);
	if(!ph) {
		printf("VM: copy_abs2region: no phys region found (1).\n");
		return NULL;
	}
	
	assert(ph->offset <= offset);
	if(ph->offset + VM_PAGE_SIZE <= offset) {
		printf("VM: copy_abs2region: no phys region found (2).\n");
		return NULL;
	}
	
	return ph;
}

static phys_bytes calculate_copy_length(phys_bytes len, phys_bytes suboffset)
{
	assert(suboffset < VM_PAGE_SIZE);
	phys_bytes sublen = len;
	phys_bytes remaining = VM_PAGE_SIZE - suboffset;
	
	if(sublen > remaining) {
		sublen = remaining;
	}
	
	assert(suboffset + sublen <= VM_PAGE_SIZE);
	return sublen;
}

static int perform_copy(phys_bytes absaddr, struct phys_region *ph, 
	phys_bytes suboffset, phys_bytes sublen)
{
	if(ph->ph->refcount != 1) {
		printf("VM: copy_abs2region: refcount not 1.\n");
		return 0;
	}

	if(sys_abscopy(absaddr, ph->ph->phys + suboffset, sublen) != OK) {
		printf("VM: copy_abs2region: abscopy failed.\n");
		return 0;
	}
	
	return 1;
}

/*=========================================================================*
 *				map_writept				*
 *=========================================================================*/
int map_writept(struct vmproc *vmp)
{
	struct vir_region *vr;
	region_iter v_iter;
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);

	while((vr = region_get_iter(&v_iter))) {
		int r = process_region_pages(vmp, vr);
		if(r != OK) {
			printf("VM: map_writept: failed\n");
			return r;
		}
		region_incr_iter(&v_iter);
	}

	return OK;
}

static int process_region_pages(struct vmproc *vmp, struct vir_region *vr)
{
	vir_bytes p;
	for(p = 0; p < vr->length; p += VM_PAGE_SIZE) {
		int r = process_single_page(vmp, vr, p);
		if(r != OK) {
			return r;
		}
	}
	return OK;
}

static int process_single_page(struct vmproc *vmp, struct vir_region *vr, vir_bytes offset)
{
	struct phys_region *ph = physblock_get(vr, offset);
	if(!ph) {
		return OK;
	}
	return map_ph_writept(vmp, vr, ph);
}

/*========================================================================*
 *			       map_proc_copy			     	  *
 *========================================================================*/
int map_proc_copy(struct vmproc *dst, struct vmproc *src)
{
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

	if(!start_src_vr)
		start_src_vr = region_search_least(&src->vm_regions_avl);
	if(!end_src_vr)
		end_src_vr = region_search_greatest(&src->vm_regions_avl);

	assert(start_src_vr && end_src_vr);
	assert(start_src_vr->parent == src);
	region_start_iter(&src->vm_regions_avl, &v_iter,
		start_src_vr->vaddr, AVL_EQUAL);
	assert(region_get_iter(&v_iter) == start_src_vr);

	SANITYCHECK(SCL_FUNCTIONS);

	while((vr = region_get_iter(&v_iter))) {
		if(copy_single_region(dst, vr) != OK) {
			map_free_proc(dst);
			return ENOMEM;
		}
		
		if(vr == end_src_vr)
			break;
		
		region_incr_iter(&v_iter);
	}

	map_writept(src);
	map_writept(dst);

	SANITYCHECK(SCL_FUNCTIONS);
	return OK;
}

static int copy_single_region(struct vmproc *dst, struct vir_region *vr)
{
	struct vir_region *newvr = map_copy_region(dst, vr);
	if(!newvr)
		return ENOMEM;
	
	region_insert(&dst->vm_regions_avl, newvr);
	assert(vr->length == newvr->length);
	
#if SANITYCHECKS
	verify_region_copy(vr, newvr);
#endif
	
	return OK;
}

#if SANITYCHECKS
static void verify_region_copy(struct vir_region *vr, struct vir_region *newvr)
{
	vir_bytes vaddr;
	struct phys_region *orig_ph, *new_ph;
	
	assert(vr->physblocks != newvr->physblocks);
	
	for(vaddr = 0; vaddr < vr->length; vaddr += VM_PAGE_SIZE) {
		orig_ph = physblock_get(vr, vaddr);
		new_ph = physblock_get(newvr, vaddr);
		
		if(!orig_ph) {
			assert(!new_ph);
			continue;
		}
		
		assert(new_ph);
		assert(orig_ph != new_ph);
		assert(orig_ph->ph == new_ph->ph);
	}
}
#endif

int map_region_extend_upto_v(struct vmproc *vmp, vir_bytes v)
{
	vir_bytes offset = roundup(v, VM_PAGE_SIZE);
	struct vir_region *vr = region_search(&vmp->vm_regions_avl, offset, AVL_LESS);
	
	if (!vr) {
		printf("VM: nothing to extend\n");
		return ENOMEM;
	}

	if (vr->vaddr + vr->length >= v) {
		return OK;
	}

	vir_bytes limit = vr->vaddr + vr->length;
	vir_bytes extralen = offset - limit;
	
	assert(vr->vaddr <= offset);
	assert(extralen > 0);

	struct vir_region *nextvr = getnextvr(vr);
	if (nextvr) {
		assert(offset <= nextvr->vaddr);
		if (nextvr->vaddr < offset) {
			printf("VM: can't grow into next region\n");
			return ENOMEM;
		}
	}

	if (!vr->def_memtype->ev_resize) {
		return extend_with_anon_memory(vmp, limit, extralen);
	}

	return resize_existing_region(vmp, vr, offset);
}

static int extend_with_anon_memory(struct vmproc *vmp, vir_bytes limit, vir_bytes extralen)
{
	if (!map_page_region(vmp, limit, 0, extralen, VR_WRITABLE | VR_ANON, 0, &mem_type_anon)) {
		printf("resize: couldn't put anon memory there\n");
		return ENOMEM;
	}
	return OK;
}

static int resize_existing_region(struct vmproc *vmp, struct vir_region *vr, vir_bytes offset)
{
	int newslots = phys_slot(offset - vr->vaddr);
	int prevslots = phys_slot(vr->length);
	
	assert(newslots >= prevslots);
	
	int addedslots = newslots - prevslots;
	
	struct phys_region **newpr = realloc(vr->physblocks, newslots * sizeof(struct phys_region *));
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
	int freeslots = phys_slot(len);

	SANITYCHECK(SCL_FUNCTIONS);

	if(offset+len > r->length || (len % VM_PAGE_SIZE)) {
		printf("VM: bogus length 0x%lx\n", len);
		return EINVAL;
	}

	regionstart = r->vaddr + offset;

	map_subfree(r, offset, len);

	if(r->length == len) {
		return handle_region_removal(vmp, r);
	} 
	
	if(offset == 0) {
		return handle_low_shrink(vmp, r, len, freeslots);
	}
	
	if(offset + len == r->length) {
		assert(len <= r->length);
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

static int handle_region_removal(struct vmproc *vmp, struct vir_region *r)
{
	region_remove(&vmp->vm_regions_avl, r->vaddr);
	map_free(r);
	return OK;
}

static int handle_low_shrink(struct vmproc *vmp, struct vir_region *r, 
	vir_bytes len, int freeslots)
{
	if(!r->def_memtype->ev_lowshrink) {
		printf("VM: low-shrinking not implemented for %s\n",
			r->def_memtype->name);
		return EINVAL;
	}

	if(r->def_memtype->ev_lowshrink(r, len) != OK) {
		printf("VM: low-shrinking failed for %s\n",
			r->def_memtype->name);
		return EINVAL;
	}

	region_remove(&vmp->vm_regions_avl, r->vaddr);

	USE(r, r->vaddr += len;);

	int remslots = phys_slot(r->length);

	region_insert(&vmp->vm_regions_avl, r);

	adjust_phys_regions(r, len);

	if(remslots)
		memmove(r->physblocks, r->physblocks + freeslots,
			remslots * sizeof(struct phys_region *));
	
	USE(r, r->length -= len;);

	return OK;
}

static void adjust_phys_regions(struct vir_region *r, vir_bytes len)
{
	struct phys_region *pr;
	vir_bytes voffset;

	for(voffset = len; voffset < r->length; voffset += VM_PAGE_SIZE) {
		if(!(pr = physblock_get(r, voffset))) 
			continue;
		assert(pr->offset >= len);
		USE(pr, pr->offset -= len;);
	}
}

static int validate_split_parameters(struct vir_region *vr, vir_bytes split_len, vir_bytes rem_len)
{
	assert(!(split_len % VM_PAGE_SIZE));
	assert(!(rem_len % VM_PAGE_SIZE));
	assert(!(vr->vaddr % VM_PAGE_SIZE));
	assert(!(vr->length % VM_PAGE_SIZE));
	
	if(!vr->def_memtype->ev_split) {
		printf("VM: split region not implemented for %s\n",
			vr->def_memtype->name);
		return EINVAL;
	}
	return OK;
}

static struct vir_region* create_split_region(struct vmproc *vmp, vir_bytes addr, 
	vir_bytes len, int flags, struct mem_type *memtype)
{
	return region_new(vmp, addr, len, flags, memtype);
}

static void cleanup_regions(struct vir_region *r1, struct vir_region *r2)
{
	if(r1) map_free(r1);
	if(r2) map_free(r2);
}

static int copy_physblocks(struct vir_region *src, struct vir_region *dst, 
	vir_bytes src_offset, int *count)
{
	vir_bytes voffset;
	
	for(voffset = 0; voffset < dst->length; voffset += VM_PAGE_SIZE) {
		struct phys_region *ph, *phn;
		if(!(ph = physblock_get(src, src_offset + voffset))) continue;
		if(!(phn = pb_reference(ph->ph, voffset, dst, ph->memtype)))
			return ENOMEM;
		(*count)++;
	}
	return OK;
}

static void finalize_split(struct vmproc *vmp, struct vir_region *vr,
	struct vir_region *r1, struct vir_region *r2)
{
	vr->def_memtype->ev_split(vmp, vr, r1, r2);
	region_remove(&vmp->vm_regions_avl, vr->vaddr);
	map_free(vr);
	region_insert(&vmp->vm_regions_avl, r1);
	region_insert(&vmp->vm_regions_avl, r2);
}

static int split_region(struct vmproc *vmp, struct vir_region *vr,
	struct vir_region **vr1, struct vir_region **vr2, vir_bytes split_len)
{
	struct vir_region *r1 = NULL, *r2 = NULL;
	vir_bytes rem_len = vr->length - split_len;
	int n1 = 0, n2 = 0;
	int result;

	result = validate_split_parameters(vr, split_len, rem_len);
	if(result != OK) {
		sys_diagctl_stacktrace(vmp->vm_endpoint);
		return result;
	}

	r1 = create_split_region(vmp, vr->vaddr, split_len, vr->flags, vr->def_memtype);
	if(!r1) {
		printf("split_region: failed\n");
		return ENOMEM;
	}

	r2 = create_split_region(vmp, vr->vaddr + split_len, rem_len, vr->flags, vr->def_memtype);
	if(!r2) {
		cleanup_regions(r1, NULL);
		printf("split_region: failed\n");
		return ENOMEM;
	}

	if(copy_physblocks(vr, r1, 0, &n1) != OK) {
		cleanup_regions(r1, r2);
		printf("split_region: failed\n");
		return ENOMEM;
	}

	if(copy_physblocks(vr, r2, split_len, &n2) != OK) {
		cleanup_regions(r1, r2);
		printf("split_region: failed\n");
		return ENOMEM;
	}

	finalize_split(vmp, vr, r1, r2);

	*vr1 = r1;
	*vr2 = r2;

	return OK;
}

int map_unmap_range(struct vmproc *vmp, vir_bytes unmap_start, vir_bytes length)
{
	vir_bytes o = unmap_start % VM_PAGE_SIZE;
	vir_bytes unmap_limit;
	region_iter v_iter;
	struct vir_region *vr;

	unmap_start -= o;
	length += o;
	length = roundup(length, VM_PAGE_SIZE);
	unmap_limit = length + unmap_start;

	if(length < VM_PAGE_SIZE) return EINVAL;
	if(unmap_limit <= unmap_start) return EINVAL;

	vr = find_first_region(vmp, unmap_start, &v_iter);
	if(!vr) return OK;

	return process_regions(vmp, vr, &v_iter, unmap_start, unmap_limit);
}

static struct vir_region *find_first_region(struct vmproc *vmp, vir_bytes unmap_start, region_iter *v_iter)
{
	struct vir_region *vr;
	
	region_start_iter(&vmp->vm_regions_avl, v_iter, unmap_start, AVL_LESS_EQUAL);
	vr = region_get_iter(v_iter);
	
	if(!vr) {
		region_start_iter(&vmp->vm_regions_avl, v_iter, unmap_start, AVL_GREATER);
		vr = region_get_iter(v_iter);
	}
	
	return vr;
}

static int process_regions(struct vmproc *vmp, struct vir_region *vr, region_iter *v_iter, vir_bytes unmap_start, vir_bytes unmap_limit)
{
	struct vir_region *nextvr;
	
	for(; vr && vr->vaddr < unmap_limit; vr = nextvr) {
		region_incr_iter(v_iter);
		nextvr = region_get_iter(v_iter);
		
		int r = process_single_region(vmp, vr, unmap_start, unmap_limit);
		if(r != OK) return r;
		
		reset_iterator_if_needed(vmp, nextvr, v_iter);
	}
	
	return OK;
}

static int process_single_region(struct vmproc *vmp, struct vir_region *vr, vir_bytes unmap_start, vir_bytes unmap_limit)
{
	vir_bytes thislimit = vr->vaddr + vr->length;
	vir_bytes this_unmap_start = MAX(unmap_start, vr->vaddr);
	vir_bytes this_unmap_limit = MIN(unmap_limit, thislimit);
	
	assert(thislimit > vr->vaddr);
	
	if(this_unmap_start >= this_unmap_limit) return OK;
	
	if(needs_splitting(vr, this_unmap_start, this_unmap_limit, thislimit)) {
		int r = perform_split(vmp, &vr, this_unmap_limit);
		if(r != OK) return r;
		thislimit = vr->vaddr + vr->length;
	}
	
	return perform_unmap(vmp, vr, this_unmap_start, this_unmap_limit);
}

static int needs_splitting(struct vir_region *vr, vir_bytes this_unmap_start, vir_bytes this_unmap_limit, vir_bytes thislimit)
{
	return this_unmap_start > vr->vaddr && this_unmap_limit < thislimit;
}

static int perform_split(struct vmproc *vmp, struct vir_region **vr, vir_bytes this_unmap_limit)
{
	struct vir_region *vr1, *vr2;
	vir_bytes split_len = this_unmap_limit - (*vr)->vaddr;
	
	assert(split_len > 0);
	assert(split_len < (*vr)->length);
	
	int r = split_region(vmp, *vr, &vr1, &vr2, split_len);
	if(r != OK) {
		printf("VM: unmap split failed\n");
		return r;
	}
	
	*vr = vr1;
	return OK;
}

static int perform_unmap(struct vmproc *vmp, struct vir_region *vr, vir_bytes this_unmap_start, vir_bytes this_unmap_limit)
{
	vir_bytes thislimit = vr->vaddr + vr->length;
	vir_bytes remainlen = this_unmap_limit - vr->vaddr;
	
	assert(this_unmap_start >= vr->vaddr);
	assert(this_unmap_limit <= thislimit);
	assert(remainlen > 0);
	
	int r = map_unmap_region(vmp, vr, this_unmap_start - vr->vaddr,
		this_unmap_limit - this_unmap_start);
	
	if(r != OK) {
		printf("map_unmap_range: map_unmap_region failed\n");
	}
	
	return r;
}

static void reset_iterator_if_needed(struct vmproc *vmp, struct vir_region *nextvr, region_iter *v_iter)
{
	if(nextvr) {
		region_start_iter(&vmp->vm_regions_avl, v_iter, nextvr->vaddr, AVL_EQUAL);
		assert(region_get_iter(v_iter) == nextvr);
	}
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
	struct vir_region *vr = map_lookup(vmp, addr, NULL);
	
	if (!vr || vr->vaddr != addr)
		return EINVAL;

	if (!vr->def_memtype->regionid)
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
	
	if (!vr || vr->vaddr != addr || !vr->def_memtype->refcount)
		return EINVAL;

	if (cnt)
		*cnt = vr->def_memtype->refcount(vr);

	return OK;
}

void get_usage_info_kernel(struct vm_usage_info *vui)
{
	memset(vui, 0, sizeof(*vui));
	vui->vui_total = kernel_boot_info.kernel_allocated_bytes +
		kernel_boot_info.kernel_allocated_bytes_dynamic;
	vui->vui_virtual = vui->vui_total;
	vui->vui_mvirtual = vui->vui_total;
}

static void get_usage_info_vm(struct vm_usage_info *vui)
{
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
static int is_stack_region(struct vir_region *vr)
{
    const vir_bytes STACK_START = VM_STACKTOP - DEFAULT_STACK_LIMIT;
    const size_t STACK_SIZE = DEFAULT_STACK_LIMIT;
    
    return (vr->vaddr == STACK_START && vr->length == STACK_SIZE);
}

/*========================================================================*
 *				get_usage_info				  *
 *========================================================================*/
void get_usage_info(struct vmproc *vmp, struct vm_usage_info *vui)
{
	memset(vui, 0, sizeof(*vui));

	if(vmp->vm_endpoint == VM_PROC_NR) {
		get_usage_info_vm(vui);
		return;
	}

	if(vmp->vm_endpoint < 0) {
		get_usage_info_kernel(vui);
		return;
	}

	calculate_region_usage(vmp, vui);
	add_resource_info(vmp, vui);
}

static void calculate_region_usage(struct vmproc *vmp, struct vm_usage_info *vui)
{
	struct vir_region *vr;
	region_iter v_iter;
	
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);
	
	while((vr = region_get_iter(&v_iter))) {
		process_region(vr, vui);
		region_incr_iter(&v_iter);
	}
}

static void process_region(struct vir_region *vr, struct vm_usage_info *vui)
{
	vir_bytes voffset;
	
	vui->vui_virtual += vr->length;
	vui->vui_mvirtual += vr->length;
	
	for(voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
		process_page(vr, voffset, vui);
	}
}

static void process_page(struct vir_region *vr, vir_bytes voffset, struct vm_usage_info *vui)
{
	struct phys_region *ph = physblock_get(vr, voffset);
	
	if(!ph) {
		handle_unmapped_page(vr, vui);
		return;
	}
	
	vui->vui_total += VM_PAGE_SIZE;
	
	if (ph->ph->refcount > 1) {
		handle_common_page(vr, vui);
	}
}

static void handle_unmapped_page(struct vir_region *vr, struct vm_usage_info *vui)
{
	if (is_stack_region(vr)) {
		vui->vui_mvirtual -= VM_PAGE_SIZE;
	}
}

static void handle_common_page(struct vir_region *vr, struct vm_usage_info *vui)
{
	vui->vui_common += VM_PAGE_SIZE;
	
	if (vr->flags & VR_SHARED) {
		vui->vui_shared += VM_PAGE_SIZE;
	}
}

static void add_resource_info(struct vmproc *vmp, struct vm_usage_info *vui)
{
	#define KB_DIVISOR 1024L
	
	vui->vui_maxrss = vmp->vm_total_max / KB_DIVISOR;
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

	next = *nextp;

	if (!max) return 0;

	region_start_iter(&vmp->vm_regions_avl, &v_iter, next, AVL_GREATER_EQUAL);
	if(!(vr = region_get_iter(&v_iter))) return 0;

	for(count = 0; (vr = region_get_iter(&v_iter)) && count < max;
	   region_incr_iter(&v_iter)) {
		next = vr->vaddr + vr->length;
		
		if (process_region(vr, vri)) {
			count++;
			vri++;
		}
	}

	*nextp = next;
	return count;
}

static void find_phys_region_bounds(struct vir_region *vr, 
	struct phys_region **first, struct phys_region **last)
{
	vir_bytes voffset;
	
	*first = NULL;
	*last = NULL;
	
	for(voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
		struct phys_region *ph;
		if(!(ph = physblock_get(vr, voffset))) continue;
		if(!*first) *first = ph;
		*last = ph;
	}
}

static int process_region(struct vir_region *vr, struct vm_region_info *vri)
{
	struct phys_region *ph1 = NULL, *ph2 = NULL;
	
	find_phys_region_bounds(vr, &ph1, &ph2);
	
	if(!ph1 || !ph2) {
		printf("skipping empty region 0x%lx-0x%lx\n",
			vr->vaddr, vr->vaddr+vr->length);
		return 0;
	}
	
	set_region_info(vri, vr, ph1, ph2);
	return 1;
}

static void set_region_info(struct vm_region_info *vri, struct vir_region *vr,
	struct phys_region *ph1, struct phys_region *ph2)
{
	vri->vri_addr = vr->vaddr + ph1->offset;
	vri->vri_prot = PROT_READ;
	vri->vri_length = ph2->offset + VM_PAGE_SIZE - ph1->offset;
	
	if (vr->flags & VR_WRITABLE)
		vri->vri_prot |= PROT_WRITE;
}

/*========================================================================*
 *				regionprintstats			  *
 *========================================================================*/
void printregionstats(struct vmproc *vmp)
{
	vir_bytes used = 0, weighted = 0;
	region_iter v_iter;
	
	region_start_iter_least(&vmp->vm_regions_avl, &v_iter);
	
	struct vir_region *vr;
	while((vr = region_get_iter(&v_iter))) {
		region_incr_iter(&v_iter);
		
		if(!(vr->flags & VR_DIRECT)) {
			calculate_region_usage(vr, &used, &weighted);
		}
	}
	
	print_usage_stats(used, weighted);
}

static void calculate_region_usage(struct vir_region *vr, vir_bytes *used, vir_bytes *weighted)
{
	for(vir_bytes voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
		struct phys_region *pr = physblock_get(vr, voffset);
		if(pr) {
			update_usage_counters(pr, used, weighted);
		}
	}
}

static void update_usage_counters(struct phys_region *pr, vir_bytes *used, vir_bytes *weighted)
{
	*used += VM_PAGE_SIZE;
	*weighted += VM_PAGE_SIZE / pr->ph->refcount;
}

static void print_usage_stats(vir_bytes used, vir_bytes weighted)
{
	#define BYTES_PER_KB 1024
	printf("%6lukB  %6lukB\n", used/BYTES_PER_KB, weighted/BYTES_PER_KB);
}

void map_setparent(struct vmproc *vmp)
{
	region_iter iter;
	struct vir_region *vr;
	region_start_iter_least(&vmp->vm_regions_avl, &iter);
	while((vr = region_get_iter(&iter))) {
		USE(vr, vr->parent = vmp;);
		region_incr_iter(&iter);
	}
}

unsigned int physregions(struct vir_region *vr)
{
	unsigned int n = 0;
	vir_bytes voffset;
	
	for(voffset = 0; voffset < vr->length; voffset += VM_PAGE_SIZE) {
		if(physblock_get(vr, voffset))
			n++;
	}
	
	return n;
}
