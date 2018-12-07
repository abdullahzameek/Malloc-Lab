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
 * Free block:
 * +--------+------+----------+---------+--------+
 * | header | next | previous | payload | footer |
 * +--------+------+----------+---------+--------+
 * 
 * header - same as above
 * next - pointer to the next free block in memory. One word in size
 * previous - pointer to the previous free block in memory. Also one word in size
 * payload - the freed memory
 * footer - same as above
 * 
 * Overall memory:
 * +--------+
 * |        |
 * |used    |
 * |memory  |
 * |        |
 * |        |
 * +--------+
 * |        |
 * |        |
 * | lookup |
 * | table  |
 * |        |
 * +--------+
 * 
 * lookup table - at the very bottom of the heap, a static 
 *  memory overhead we're using to manage the list of 
 *  pointers to linked lists, which may be anywhere in
 *  allocated memory
 * used memory - this is where the diagrams above would be 
 *  placed, both free and non-free in (most probably) non-contiguous blocks
 * High level implementation details:
 * -Free memory works as a doubly linked list. How to make it work like one when the allocated size is too small?
 * -There doesn't need to be a way to iterate over the allocated data, merely know what's allocated, and how large it is
 * -The first several words of the heap are a lookup table, which is a static memory overhead, but should be worth it in long run
 * -We use a simple first-fit memory allocation strategy, but should do address ordering for the insertion
 * -
 */
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

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
// The minimum possible free chunk size. If we add this restriction, then
// there should be no problems with allocation in the lower size classes.
// Technically the minimum would be 4 * WSIZE + 1, but that would not
// be aligned to the word boundary
#define MINCHUNK (4 * WSIZE) + WSIZE
// The number of size classes was chosen by enumerating the number of
// size classes: {{1}, {2}, {5-8}, {9-16}, ..., {4097, +oo}}
// Should be increase this?
#define CLASSES 14

#define VOID (size_t *)0

// Overhead from initializing a lookup table in memory, not taking
// into account the header and the footer size, each of which
// should be another word. This only needs to be used when calculating
// offsets.
#define CLASS_OVERHEAD ((CLASSES) * (WSIZE))

// The pointers to the locations in memory we will be using
// for reference for the rest of the file
static size_t *heap_list = NULL;
static size_t *lookup_table = NULL;

// Function prototypes for all of the independently implemented functions.

// These functions were adapted from code provided by the
// textbook and are useful for coalescing
static inline size_t align_to_word(size_t size);
static inline size_t get(void *pointer);
static inline void put(void *pointer, size_t value);
static inline size_t pack(size_t size, size_t alloc);
static inline size_t get_size(void *pointer);
static inline size_t get_alloc(void *pointer);
static inline void *header_pointer(void *bp);
static inline void *footer_pointer(void *bp);
static inline void *next_block_ptr(void *bp);
static inline void *prev_block_ptr(void *bp);

// Functions to help us manipulate the free memory
// doubly linked lists
static inline int get_class(size_t size);
static void *get_free_block(int class, size_t size);
static void remove_free_block(void *pointer);
static void add_free_block(int class, void *pointer);
static inline void *get_lookup_row(int class);
static inline size_t *get_next_free(void *base);
static inline size_t *get_prev_free(void *base);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static int mm_checkheap();
static void check_block(void *bp);
static void best_fit(size_t size);

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
static inline void *header_pointer(void *bp)
{
    return (void *)((size_t)bp) - WSIZE;
}

// Don't understand why we have 2 * WSIZE. Need to figure out if that works or not
static inline void *footer_pointer(void *bp)
{
    return (void *)((size_t)bp) + get_size((void *)((size_t)header_pointer(bp) - 2 * WSIZE));
}

// Get a pointer to the next block, given a pointer to an allocated one
// Useful for coalescing
static inline void *next_block_ptr(void *bp)
{
    return (void *)((size_t *)bp) + get_size((size_t *)bp - WSIZE);
}

// Get a pointer to the previous block, given a pointer to an allocated one.
// Assumes contiguity in memory
static inline void *prev_block_ptr(void *bp)
{
    return (void *)((size_t *)bp) - get_size(((size_t *)bp) - 2 * WSIZE);
}

/* 

START OF THE DOUBLE LINKED LIST AND SIZE CLASS TABLE MANIPULATION
METHODS
 
*/

/* 
 * get_class - returns the size class in which the current chunk
 * would fit. Does so with clever bit manipulation, borrowed from
 * Hacker's Delight (2rd edition), saving us from branching and
 * optimizing precious cycles. 
 */
static inline int get_class(size_t size)
{
    size = size | (size >> 1);
    size = size | (size >> 2);
    size = size | (size >> 4);
    size = size | (size >> 8);
    size = size | (size >> 16);
    // If within a predefined class size, return that size, otherwise return the
    // largest
    return (size - (size >> 1) + 1) % CLASSES ? (size - (size >> 1) + 1) : CLASSES - 1;
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

    // Get the location of the pointer, then get what the pointer is linking to
    void *size_class_base = get_lookup_row(class);
    // This is currently pointing to the base of the next free block
    size_t *current = get(size_class_base);

    // Simple iteration over a linked list
    while (current != NULL)
    {
        size_t block_size = get_size(current);
        // First-fit based implementation
        if (block_size >= size)
        {
            // Removes a block from the free block list
            remove_free_block(current);
            return current;
        }

        current = *get_next_free(current);
    }

    return NULL;
}

/* 
 * remove_free_block - given a size class and a pointer to the block
 * that is being removed, it links the previous and successive
 * elements, removing it from the list.
 */
static inline void remove_free_block(void *pointer)
{
    // Getting header and footer.
    void *header = header_pointer(pointer);
    void *footer = footer_pointer(pointer);

    size_t block_size = get_size(header);
    // Set the header and footer status to allocated
    put(header, pack(block_size, 1));
    put(footer, pack(block_size, 1));

    // Get the previous and blocks in the array - we need
    // some special logic for the previous one to make sure
    // not to overwrite anything in the lookup table
    size_t *next = get(get_next_free(pointer)); // Address of the next block
    size_t *prev = get(get_prev_free(pointer)); // Address of the previous block

    if (next != NULL) {
        put(next + 2 * WSIZE, prev);
    }

    // Doesn't actually matter if the next is null or not for this particular
    // case, but we need need to know what to overwrite 
    put(prev + WSIZE * (prev > lookup_table + CLASS_OVERHEAD), next);


    // Zero out the next and previous pointers
    put(header + WSIZE, pack(0, 0));
    put(header + 2 * WSIZE, pack(0, 0));
}

/* 
 * add_free_block - given a pointer, calculate its size class
 * from previous header and footer data, then do a linear 
 * search for where it should be added, with address ordering.
 */
static inline void add_free_block(int class, void *pointer)
{
    // We use two word sizes to
    size_t current_size = get_size(pointer);
    
    void *lookup_row = get_lookup_row(class);
    size_t *current = get(lookup_row);

    // This is essentially sorting the list in terms of address.
    // Not quite sure why this is all that good at current time,
    // but it will have to do.
    while (current != NULL && current < get_next_free(current)) {

    }

    
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
static inline void *get_lookup_row(int class)
{
    if (class < 0 || class > CLASSES)
    {
        return NULL;
    }
    return (void *)(lookup_table + class * WSIZE);
}

/* 
 * get_next_free - retrieves the pointer to the next free block
 * given a pointer to the base of the payload. For the exact
 * alignment information, refer to the diagrams above.
 */
static inline size_t *get_next_free(void *base)
{
    return (size_t *)((*(size_t *)base) + WSIZE);
}

/* 
 * get_prev_free - retrieves the pointer to the previous free block
 * given a pointer to the base of the payload.
 */
static inline size_t *get_prev_free(void *base)
{
    return (size_t *)((*(size_t *)base) + 2 * WSIZE);
}

/* 

END OF DOUBLE LINKED LIST MANIPULATION METHODS

*/

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
    if ((lookup_table = mem_sbrk(4 * WSIZE + CLASS_OVERHEAD)) < 0)
    {
        return -1;
    }

    // Put an empty lookup table for the linked list pointers at the top (bottom?) of the heap
    for (int i = 0; i < CLASSES; i++)
    {
        // TODO Replace this with a function call, just please no macros
        put(heap_list + i * WSIZE, 0);
    }

    // The heap starts directly after the lookup table
    heap_list = lookup_table + CLASS_OVERHEAD;

    // Allocate the footer of the prologue and the header of the epilogue
    put(heap_list + (1 * WSIZE), pack(WSIZE, 1)); // Prologue footer
    put(heap_list + (2 * WSIZE), pack(0, 1));     // Epilogue header
    // The heap will be growing from between the prologue and the epilogue, so that we could
    // make sure that all is well
    heap_list += WSIZE;

    // Extends the heap by a quasi-arbitrary initial amount
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }

    // Initiation was successful
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
        // Here we need to extend the heap
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

    if ((size_t) mem_sbrk(extended_words) == -1)
    {
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