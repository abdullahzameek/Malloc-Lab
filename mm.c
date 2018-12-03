/*
 *  
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Our Lord and Savior, the SegFault", 
    /* First member's full name */
    "Lukas Zapolskas",
    /* First member's email address */
    "lz1477@nyu.edu",
    /* Second member's full name (leave blank if none) */
    "Abdullah Zameek",
    /* Second member's email address (leave blank if none) */
    "arz268@nyu.edu"};

/* Macros start here */

// We are leaving constants as macros, to make sure the interface
// to the library remains unchanged, and will be using static inline
// functions to make sure this remains the way it is.
#define ALIGNMENT (2 * sizeof(void *))
#define WSIZE sizeof(void *)
#define CHUNKSIZE (1 << 12)

// The number of size classes was chosen by enumerating the number of
// size classes: {{1}, {2}, {5-8}, {9-16}, ..., {4097, +oo}}
#define CLASSES 14

// Overhead from initializing a lookup table in memory, not taking
// into account the header and the footer size, each of which
// should be another word. This only needs to be used when calculating
// offsets.
#define CLASS_OVERHEAD (14 * WSIZE)

/* 
 * get_class - Returns the size class in which the current chunk
 * would fit. Does so with clever bit manipulation, borrowed from
 * Hacker's Delight (2rd edition), saving us from branching and
 * optimizing precious cycles.
 */
inline size_t get_class(size_t size) {
    size = size | (size >> 1);
    size = size | (size >> 2);
    size = size | (size >> 4);
    size = size | (size >> 8);
    size = size | (size >> 16);
    return size - (size >> 1) + 1;
}

// TODO Figure out what the best way to convert these functions is
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(p) ((char *)(bp)-WSIZE)
#define FTRP(p) ((char *)(bp) + GET_SIZE(HDRP(p)) - DSIZE)

#define NEXT_BLKP(bp) ((char *) (bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *) (bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


// Support function forward declaration
static void *extend_heap(size_t words);
static void *coalesce(void* bp);
static void mm_checker(void* bp);
static void check_block(void* bp);
static void best_fit(size_t size);      


static char *heap_list = NULL;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_list = mem_sbrk(4 * WSIZE + CLASS_OVERHEAD)) < 0) {
        return -1;
    }

    for (int i = 0; i < CLASSES; i++) {
        PUT(heap_list + i * WSIZE, NULL);
    }
    heap_list += CLASSES * WSIZE;

    PUT(heap_list + WSIZE, PACK(WSIZE, 1));     // Prologue header
    PUT(heap_list + (1*WSIZE), PACK(WSIZE, 1)); // Prologue footer
    PUT(heap_list + (2*WSIZE), PACK(0, 1));     // Epilogue header
    PUT(heap_list + (3*WSIZE), PACK(0, 1));     // Epilogue footer - can be optimized out
    heap_list+= 2 * WSIZE;

    // Extend heap

}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{

}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{

}

static void *extend_heap(size_t words)
{

}

static void *coalesce(void *bp) 
{
    

}