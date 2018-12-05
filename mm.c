/*
 *  Segregated list memory allocator with first fit placement policy.
 * Where do we put the pointer to the next block? Another block under the header?
 * 
 * What is our freeing policy - coalesce on free? Seems like the most efficient way of doing things
 * What's the easiest way for us to represent a doubly linked list as an abstraction
 * on the heap?
 * 
 * Memory structure:
 * 
 * Allocated block
 * +--------+---------------+--------+
 * | header |   payload	    | footer |
 * +--------+---------------+--------+
 * 
 * header - contains size data in the upper 29 or 61 bits and 
 *          allocation information about the next and previous block
 * footer - contains the same data as the header, for ease of coalescing (can be replaced for efficiency)
 * payload - single word (!!!) boundary aligned payload. 
 * 
 * 
 * Free block
 * +--------+------+---------+---------+--------+
 * | header | next | previous| payload | footer |
 * +--------+------+---------+---------+--------+
 * 
 * header - same as above
 * next - pointer to the next free block in memory. One word in size
 * previous - pointer to the previous free block in memory. Also one word in size
 * payload - the freed memory
 * footer - same as above
 * 
 * 
 * High level implementation details:
 * -Free memory works as a doubly linked list. How to make it work like one when the allocated size is too small?
 * -There doesn't need to be a way to iterate over the allocated data, merely know what's allocated, and how large it is
 * -The first several words of the heap are a lookup table, which is a static memory overhead, but should be worth it in long run
 * -We use a simple first-fit memory allocation strategy, but should do address ordering for the insertion
 * -
 */
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

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

// We are leaving constants as macros, to make sure the interface
// to the library remains unchanged, and will be using static inline
// functions to make sure this remains the way it is.
#define ALIGNMENT (2 * sizeof(void *))
#define WSIZE sizeof(void *)
#define CHUNKSIZE (1L << 12)
#define MINCHUNK (1L << 5)

/* 

START OF THE DOUBLE LINKED LIST AND SIZE CLASS TABLE MANIPULATION
METHODS
 
*/

// The number of size classes was chosen by enumerating the number of
// size classes: {{1}, {2}, {5-8}, {9-16}, ..., {4097, +oo}}
// Should be increase this?
#define CLASSES 14

// Overhead from initializing a lookup table in memory, not taking
// into account the header and the footer size, each of which
// should be another word. This only needs to be used when calculating
// offsets.
#define CLASS_OVERHEAD (14 * WSIZE)

/* 
 * get_class - returns the size class in which the current chunk
 * would fit. Does so with clever bit manipulation, borrowed from
 * Hacker's Delight (2rd edition), saving us from branching and
 * optimizing precious cycles. 
 * 
 * TODO It does not handle the edge case of the infinite class,
 * which we really should do
 */
static inline int get_class(size_t size)
{
    size = size | (size >> 1);
    size = size | (size >> 2);
    size = size | (size >> 4);
    size = size | (size >> 8);
    size = size | (size >> 16);
    return size - (size >> 1) + 1;
}

/* 
 * get_free_block - given a class and a size, returns a free
 * block from the given size class that fits the description.
 * Returns early if the class is not within the defined range.
 * If a free block does not exist, returns a null pointer.
*/
static inline void *get_free_block(int class, size_t size)
{
    if (class < 0 || class < CLASSES)
    {
        return NULL;
    }

    // for every block in this list:
    // while the next pointer is not null
    // look at size of block
    // if sufficient, go for it + break
    // if not, go back
}

/* 
 * remove_free_block - given a size class and a pointer to the block
 * that is being removed, it links the previous and successive
 * elements, removing it from the list.
 */
static inline void remove_free_block(int class, void *pointer)
{
    // Flip the header and footer alloc bits
    // Add to appropriate size array
    // We're assuming that there was a coalesce action
    // that happened during the free, or some time before
    // this so we don't do anything at the moment
}

/* 
 * add_free_block - given a pointer, calculate its size class
 * from previous header and footer data, then do a linear 
 * search for where it should be added, with address ordering.
 */
static inline void add_free_block(void* pointer) {
    // Get header or footer data
    // Calculate size class
    // Search for place in the appropriate array to find it
    // Set the pointers of the next + previous to the right
    // ones
}

/* 
 * get_lookup_row - get the row of the lookup table corresponding to 
 * the given size class
 */
static inline void *get_lookup_row(int class) {
    // Take class offset, return pointer
}

/* 

END OF DOUBLE LINKED LIST MANIPULATION METHODS

*/

/* 

START OF THE GENERAL POINTER MANIPULATION METHODS

*/

/* 
 * align_to_word - given a user-defined size, align it
 * to the next word boundary. Since this means making it even,
 * it will effectively be aligned to a double word boundary as well.
 */
static inline size_t align_to_word(size_t size)
{
    return (size + (2 * WSIZE - 1)) & (size_t)~0x7;
}

/* 
 * get - given a pointer, return the stored value.
 */
static inline size_t get(void *pointer)
{
    return *(size_t *)pointer;
}

/* 
 * put - assign a given value to the location pointed to 
 * by the pointer
 */
static inline void put(void *pointer, size_t value)
{
    (*(size_t *)pointer) = value;
}

/* 
 * pack - combine the chunk size and allocation data
 * into one size_t
 */
static inline size_t pack(size_t size, size_t alloc)
{
    return size | alloc;
}

// Get the size of a block, given a pointer to the header or footer
static inline size_t get_size(void *pointer)
{
    return get(pointer) & ~(size_t)0x7;
}

// Get the allocation status of a block, given a pointer
static inline size_t get_alloc(void *pointer)
{
    return get(pointer) & (size_t)0x1;
}

// These might not be fully converted, though they seem fine
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

// Casting to char pointer occurs due to need for pointer arithmetic, due to the
// size of the char, which is 1 byte. This means that any offset will be taken
// at face value. bp stands for base pointer, and it's actually the pointer
// that would be returned by malloc. So to align with

// TODO Probably better to cast the pointer to a size_t, and then cast it back to a pointer
// Get the pointer to the base of the header of the allocated block
// TODO Cast to integers
static inline void *alloc_header_pointer(void *bp)
{
    return (void *)((size_t)bp) - WSIZE;
}

// Don't understand why we have 2 * WSIZE. Need to figure out if that works or not
static inline void *alloc_footer_pointer(void *bp)
{
    return (void *)((size_t)bp) + get_size((void *)((size_t)alloc_header_pointer(bp) - 2 * WSIZE));
}

// TODO The next and previous block pointers aren't 100% done
// Get a pointer to the next block, given a pointer to an allocated one
static inline void *next_block_ptr(void *bp)
{
    return (void *)((char *)bp) + get_size((char *)bp - WSIZE);
}

// Get a pointer to the previous block, given a pointer to an allocated one.
// Assumes contiguity in memory
static inline void *prev_block_ptr(void *bp)
{
    return (void *)((char *)bp) - get_size(((char *)bp) - 2 * WSIZE);
}

//

// Support function prototypes
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static int mm_checkheap();
static void check_block(void *bp);
static void best_fit(size_t size);

static char *heap_list = NULL;
static char *lookup_table = NULL;

// Checks for the following heap invariants:
// - header and footer match
// - payload area is aligned, size is valid
// - no contiguous free blocks unless coalescing is deferred
// - next/prev pointers in consecutive free blocks are consistent
// - no allocated blocks in free lists, all free blocks are in free list
// - no cycles in free list
// - each segregated list contains only blocks in the appropriate size class
static int mm_checkheap()
{

    return 0;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // Experimentally, there is no need to pad to align this to boundary aligned size.
    // Since each block will be sourrounded by a header and a footer, we only need
    // to align the payload, and not the headers and class sizes themselves.
    if ((heap_list = mem_sbrk(4 * WSIZE + CLASS_OVERHEAD)) < 0)
    {
        return -1;
    }

    // Put an empty lookup table for the linked list pointers at the top (bottom?) of the heap
    for (int i = 0; i < CLASSES; i++)
    {
        // TODO Replace this with a function call, just please no macros
        put(heap_list + i * WSIZE, 0);
    }

    // Advance the current size of the
    heap_list += CLASSES * WSIZE;

    // TODO Make some separate functions
    // Allocate the footer of the prologue and the header of the epilogue
    put(heap_list + (1 * WSIZE), pack(WSIZE, 1)); // Prologue footer
    put(heap_list + (2 * WSIZE), pack(0, 1));     // Epilogue header
    heap_list += WSIZE;                           // Advance the heap pointer to the appropriate location

    // Extends the heap by a quasi-arbitrary initial amount
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t aligned_size = align_to_word(size + 2 * WSIZE);
    size_t size_class = get_class(aligned_size);
    size_t extend_heap;

    // Ignore if current
    if (size == 0)
    {
        return NULL;
    }

    if (get_free_block(size_class, aligned_size) == NULL)
    {
    }
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
    return NULL;
}

static void *extend_heap(size_t words)
{
    // Extended words (even for double word boundary alignment)
    size_t extended_words = (words % 2 == 0) ? words : words + 1;

    if ((size_t) mem_sbrk(extended_words) == -1) {
        return NULL;
    }

    // Do we need to go 
}

static void *coalesce(void *bp)
{
    // Case 1: prev and next allocated -> do nothing
    // Case 2: prev allocated, next free -> coalesce with next
    // Case 3: prev free, next allocated -> coalesce with previous
    // Case 4: prev free, next free -> coalesce with both
    // Calculate size class
    // Add to appropriate size class
}