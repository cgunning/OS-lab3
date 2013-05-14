/*
    Description:
    An implementation of malloc, realloc and free which can be used instead of the predefined functions in the standard library libc.
    
    Takes use of MMAP(3) for memory mapping if it exists on the system, else uses sbrk(2).

    Authors:
    Christoffer Gunning, cgunning@kth.se
    Daniel Forslund, dforsl@kth.se
*/

#include "brk.h"
#include <stdio.h>
#include <unistd.h>
#include <string.h> 
#include <errno.h> 
#include <sys/mman.h>

#define NALLOC 1024                                     /* minimum #units to request */
#define MAP_ANONYMOUS 32

#define STRATEGY_FIRST 1
#define STRATEGY_BEST 2

int getpagesize(void);

typedef long Align;                                     /* for alignment to long boundary */

/*
    Header for each memory block that contains the size of block and a pointer to the next free block.
*/
union header {                                          /* block header */
    struct {
        union header *ptr;                                  /* next block if on free list */
        unsigned size;                                      /* size of this block  - what unit? */ 
    } s;
    Align x;                                              /* force alignment of blocks */
};

typedef union header Header;

static Header base;                                     /* empty list to get started */
static Header *freep = NULL;                            /* start of free list, implemented as a circular linked list */

/*
    Used to free memory allocated for the given pointer ap. If possible, it merges the memory with a nearby
    block container in the list of free blocks. Else 
*/
void free(void * ap)
{
    Header *bp, *p;

    if(ap == NULL) return;                                /* Nothing to do */

    bp = (Header *) ap - 1;                               /* point to block header */
    for(p = freep; !(bp > p && bp < p->s.ptr); p = p->s.ptr)
        if(p >= p->s.ptr && (bp > p || bp < p->s.ptr))
            break;                                            /* freed block at atrt or end of arena */

    if(bp + bp->s.size == p->s.ptr) {                     /* join to upper nb */
        bp->s.size += p->s.ptr->s.size;
        bp->s.ptr = p->s.ptr->s.ptr;
    }
    else
        bp->s.ptr = p->s.ptr;

    if(p + p->s.size == bp) {                             /* join to lower nbr */
        p->s.size += bp->s.size;
        p->s.ptr = bp->s.ptr;
    } else
        p->s.ptr = bp;
    
    freep = p;
}

/* 
    if MMAP is defined, this defines end of the heap and provides a function endHeap(0) returning the heap's current end address.
 */

#ifdef MMAP
    static void * __endHeap = 0;

    void * endHeap(void)
    {
        if(__endHeap == 0) __endHeap = sbrk(0);
            return __endHeap;
    }
#endif

/*
    Ask the system for more memory. If MMAP is defined, the MMAP function is used for this, else it takes use of sbrk. Uses
    the free function to merge the new memory with the list of free blocks. Returns a pointer to the free list, or NULL if
    it failed to get more memory.
*/ 
static Header *morecore(unsigned nu)
{
    void *cp;
    Header *up;

    #ifdef MMAP
        unsigned noPages;
        if(__endHeap == 0) __endHeap = sbrk(0);
    #endif

    if(nu < NALLOC)
        nu = NALLOC;

    #ifdef MMAP
        noPages = ((nu*sizeof(Header))-1)/getpagesize() + 1;
        cp = mmap(__endHeap, noPages*getpagesize(), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
        nu = (noPages*getpagesize())/sizeof(Header);
        __endHeap += noPages*getpagesize();
    #else
        cp = sbrk(nu*sizeof(Header));
    #endif

    if(cp == (void *) -1){                                 /* no space at all */
        perror("failed to get more memory");
        return NULL;
    }

    up = (Header *) cp;
    up->s.size = nu;
    free((void *)(up+1));
    return freep;
}

/*
    Used to dynamically allocate memory. Does either use the first-fit algorithm or the best-fit algorithm, depending which strategy
    was set during compilation.

    First-fit:
    iterates the list of free memory blocks, choosing the first which fits the requested size. If the size of the block is the same size
    as the memory to be allocated, the block is removed from the list of free blocks. If the size of the block is greater than the size
    of memory to be allocated, the block size is decreased by the allocated size. A pointer to the allocated memory is returned.

    if no match is found, morecore is called to request more memory.

    Best-fit:
    works the same way as first-fit except it iterates the list of free memory blocks and chooses the one closest in size to the size of
    the memory to be allocated.
*/
void * malloc(size_t nbytes)
{
    Header *p, *prevp;

    Header * morecore(unsigned);
    unsigned nunits;

    if(nbytes == 0) return NULL;

    nunits = (nbytes+sizeof(Header)-1)/sizeof(Header) +1;

    if((prevp = freep) == NULL) {
        base.s.ptr = freep = prevp = &base;
        base.s.size = 0;
    }

    #if STRATEGY == STRATEGY_FIRST
        for(p = prevp->s.ptr;  ; prevp = p, p = p->s.ptr) {
            if(p->s.size >= nunits) {                           /* big enough */
                if (p->s.size == nunits)                          /* exactly */
                    prevp->s.ptr = p->s.ptr;
                else {                                            /* allocate tail end */
                    p->s.size -= nunits;
                    p += p->s.size;
                    p->s.size = nunits;
                }

                freep = prevp;
                return (void *)(p+1);
            }
            if(p == freep)                                      /* wrapped around free list */
                if((p = morecore(nunits)) == NULL)
                    return NULL;                                    /* none left */
        }
    #endif
    
    #if STRATEGY == STRATEGY_BEST
        Header *p_best = NULL, *prevp_best;
        for(p = prevp->s.ptr; ; prevp = p, p = p->s.ptr) {
            if(p->s.size == nunits) {
                prevp->s.ptr = p->s.ptr;
                freep = prevp;
                return (void *)(p+1);
            }

            if(p_best == NULL || p->s.size < p_best->s.size) {
                if(p->s.size > nunits) {
                    p_best = p;
                    prevp_best = prevp;
                }
            }

            if(p == freep) {
                if(p_best != NULL)
                    break;

                if((p = morecore(nunits)) == NULL)
                    return NULL;
            }                          
        }

        p_best->s.size -= nunits;
        p_best += p_best->s.size;
        p_best->s.size = nunits;
        freep = prevp_best;
        return (void *)(p_best+1);

    #endif
}

/*
    Used to change the size of an already allocated memory block. It allocates memory of the requested size by calling malloc,
    copies the contents of the previous memory block and then frees the previous memory block by calling free on that block.

    If the parameter for the ponter is NULL, malloc is called and the address is returned. If the size is 0, a call to free with a return value being NULL.
*/
void * realloc(void *ptr, size_t size) {
    void *new_ptr;
    Header *ptr_h;
    size_t min_size, ptr_size;

    if(ptr == NULL) {
        return malloc(size);
    } else if(size == 0) {
        free(ptr);
        return NULL;
    } 

    new_ptr = malloc(size);
    if(new_ptr == NULL) 
        return NULL;

    ptr_h = (Header *) ptr - 1;
    ptr_size = sizeof(Header) * (ptr_h->s.size - 1);
    min_size = size < ptr_size ? size : ptr_size;

    memcpy(new_ptr, ptr, min_size);
    free(ptr);

    return (void *) new_ptr;
}