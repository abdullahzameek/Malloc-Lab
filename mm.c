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
#define ALIGNMENT 8
#define WSIZE 4

// System page size
#define CHUNKSIZE (1L << 12)

// The minimum possible free chunk size. If we add this restriction, then
// there should be no problems with allocation in the lower size classes.
// Technically the minimum would be 4 * WSIZE + 1, but that would not
// be aligned to the word boundary

#define MINCHUNK (4 * WSIZE)
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

// Useful several times down the line when evaluating allocation sizes
#define MAX(a, b) (((a) > (b)) ? (a) : (b))

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
static inline size_t *header_pointer(void *bp);
static inline size_t *footer_pointer(void *bp);
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
static void split_block(void *ptr, size_t newsize);
static inline size_t *shift(size_t *pointer, size_t shft);
static int mm_checkheap();

/* 

START OF THE GENERAL POINTER MANIPULATION METHODS

*/

/* 
 * align_to_word - given a user-defined size, align it
 * to the next word boundary. Since this means making it even.
 */
static inline size_t align_to_word(size_t size)
{
    return (size + (ALIGNMENT - 1)) & (size_t)~0x7;
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
// that would be returned by malloc.

// This should work, given a normal pointer
static inline size_t *header_pointer(void *bp)
{
    return (size_t *)(((size_t)bp) - WSIZE);
}

static inline size_t *footer_pointer(void *bp)
{
    return (size_t *)(((size_t)bp) + get_size((void *)header_pointer(bp)));
}

// Get a pointer to base of the next block, given a pointer to an allocated one
static inline void *next_block_ptr(void *bp)
{
    return (void *)(((size_t)footer_pointer(bp)) + 2 * WSIZE);
}

// Get a pointer to the previous block, given a pointer to an allocated one.
// Assumes contiguity in memory
static inline void *prev_block_ptr(void *bp)
{
    // Note that this is calculated from the PAYLOAD, not the base
    // of the chunk, and all of the manipulations take that into
    // account
    return (void *)(((size_t)bp) - get_size((void *)(((size_t)bp) - 2 * WSIZE)) - 2 * WSIZE);
}

/* 

START OF THE DOUBLE LINKED LIST AND SIZE CLASS TABLE MANIPULATION
METHODS
 
*/

/* 
 * get_class - returns the size class in which the current chunk
 * would fit. This was the easiest way of calculating the required
 * values, and has been verified experimentally to work on the 
 * entire range of values that are expected.
 * 
 * ASSUMPTION: the min value for size is 16
 * 
 */
static inline int get_class(size_t size)
{
    for (int i = 0; i < CLASSES; i++)
    {
        if (size < (1 << (4 + i)))
        {
            return i - 1;
        }
    }

    return CLASSES - 1;
}

/* 
 * get_free_block - given a class and a size, returns a free
 * block from the given size class that fits the description.
 * Returns early if the class is not within the defined range.
 * If a free block does not exist, returns a null pointer.
*/
static inline void *get_free_block(int class, size_t size)
{
    if (class < 0 || class > CLASSES)
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

    // Get the previous and blocks in the array - we need
    // some special logic for the previous one to make sure
    // not to overwrite anything in the lookup table
    size_t *next = get(get_next_free(pointer)); // Address of the next block
    size_t *prev = get(get_prev_free(pointer)); // Address of the previous block

    if (next != NULL)
    {
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
 * 
 * To add the free blocks, there are 4 possible cases. 
 * 
 * 1) The new free block is the first element after the sentinel node i.e the lookup table itself.
 * 2) The new free block has to be inserted in between the sentinel and another free block
 * 3) The new free block has to be inserted in between two existing nodes 
 * 4) The new free block has to be inserted at the end of the free list
 *
 */

static inline void add_free_block(int class, void *pointer)
{
    // We use two word sizes to
    size_t current_size = get_size(pointer);
    void *lookup_row = get_lookup_row(class);
    size_t *current = get(lookup_row);

    size_t *prevNode;
    size_t *nextNode;

    // This is essentially sorting the list in terms of address.
    // Not quite sure why this is all that good at current time,
    // but it will have to do.
    while (current != NULL && current < get_next_free(current))
    {
        current = get(get_next_free(current));
    }

    if (current == NULL)
    {
        put((void *)lookup_row, pointer);
    }
    else
    {
        nextNode = get(get_next_free(current));
        prevNode = current;

        // Set the previous ptr of the next block
        put(shift(nextNode, 2 * WSIZE), pointer);
        // Set the next ptr of the previous block
        put(shift(prevNode, WSIZE), pointer);
    }

    // Set the current and next pointers
    put(shift(pointer, WSIZE), nextNode);
    put(shift(pointer, 2 * WSIZE), prevNode);

    return;
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
    return (void *)(((size_t)lookup_table) + class * WSIZE);
}

/* 
 * get_next_free - retrieves the pointer to the next free block
 * given a pointer to the base of the payload. For the exact
 * alignment information, refer to the diagrams above.
 */
static inline size_t *get_next_free(void *base)
{
    return shift(base, WSIZE);
}

/* 
 * get_prev_free - retrieves the pointer to the previous free block
 * given a pointer to the base of the payload.
 */
static inline size_t *get_prev_free(void *base)
{
    return shift(base, 2 * WSIZE);
}

// Helps us do a lot of pointer manipulation
static inline size_t *shift(size_t *pointer, size_t shft)
{
    return (size_t *)(((size_t) pointer) + shft);
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
    void *iterator = lookup_table;
    void *heap_top = mem_heap_hi();

    while (iterator < heap_top)
    {
        if (iterator < lookup_table + CLASS_OVERHEAD)
        {
            printf("Lookup table %x has the value %d\n", iterator, get(iterator));
            iterator = (void *)((size_t)iterator + WSIZE);
        }
        else
        {
            size_t *header = (size_t *)get(iterator);
            // This is allocated
            if (get_alloc(header))
            {
                // 1. Are the footer and header the same?
                if (get_size(header) != get_size(header + get_size(header) + WSIZE))
                {
                    printf("Heap block %x has a header/footer mismatch!", iterator);
                }

                // Checks block alignment
                if (get_size(header) != align_to_word(get_size(header)))
                {
                    printf("Heap block %x has an unaligned payload", iterator);
                }
            }
        }
    }
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    void *top;
    // Experimentally, there is no need to pad to align this to boundary aligned size.
    // Since each block will be sourrounded by a header and a footer, we only need
    // to align the payload, and not the headers and class sizes themselves.
    if ((lookup_table = extend_heap(2 + CLASSES)) == NULL)
    {
        return -1;
    }

    // Put an empty lookup table for the linked list pointers at the top (bottom?) of the heap
    for (int i = 0; i < CLASSES; i++)
    {
        // TODO Replace this with a function call, just please no macros
        put(lookup_table + i * WSIZE, 0);
    }

    // The heap starts directly after the lookup table
    heap_list = lookup_table + CLASS_OVERHEAD;

    // Allocate the footer of the prologue and the header of the epilogue
    put(heap_list + (0 * WSIZE), pack(WSIZE, 1)); // Prologue footer
    put(heap_list + (1 * WSIZE), pack(0, 1));     // Epilogue header
    // The heap will be growing from between the prologue and the epilogue, so that we could
    // make sure that all is well
    heap_list += WSIZE;

    // Initially extend the heap by a page
    if ((top = extend_heap((CHUNKSIZE / WSIZE) + 2)) == NULL)
    {
        return -1;
    }

    // Add the page to the free list
    size_t initial_sc = get_class(CHUNKSIZE + 2 * WSIZE);
    put(top, pack(CHUNKSIZE, 0));
    put(top + CHUNKSIZE, pack(CHUNKSIZE, 0));

    add_free_block(initial_sc, top);

    // Initiation was successful
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t aligned_size = align_to_word(size) + 2 * WSIZE;
    size_t sc = get_class(aligned_size);
    void *final;

    // Ignore if current
    if (size <= 0)
        return NULL;

    // Ensures that we never get a block smaller than a certain size, which
    // would be problematic when freeing
    aligned_size = MAX(aligned_size, MINCHUNK);

    // If we don't get the free block, then just extend it, otherwise we're fine
    // Could potentially do it so that we allocate a lot more at once, and add
    // additional data to the free list, but that doesn't seem good
    if ((final = get_free_block(sc, aligned_size)) == NULL)
    {
        final = extend_heap(aligned_size / WSIZE);
    }

    put(final, pack(aligned_size - 2 * WSIZE, 1));
    put(final + aligned_size, pack(aligned_size - 2 * WSIZE, 1));

    final += WSIZE;
    return final;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (ptr == NULL)
    {
        return;
    }

    // Get size class and size of the block
    size_t size = get_size(header_pointer(ptr));
    size_t size_class = get_class(size); //the function should be get_class() right? It read size_class()

    // Change allocation status in the header and footer pointers
    put(header_pointer(ptr), pack(size, 0));
    put(footer_pointer(ptr), pack(size, 0));

    // Add the free block to size class linked list
    add_free_block(size_class, ptr);
    coalesce(ptr);
    
    return;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // If pointer is zero, pretend to be malloc
    if (ptr == NULL && size > 0)
    {
        return mm_malloc(size);
    }

    // If size is zero, and pointer isn't, pretend to be free
    if (ptr != NULL && size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    // Resize pointer
    if (ptr != NULL && size > 0)
    {
        size_t block_size = get_size(get(ptr));

        if (block_size < size)
        {
            // This is what we need to work on quite extensively
        }
        else if (block_size > size)
        {
            // Split it
        }
        else if (block_size == size)
        {
            return ptr; // Nothing needs to be done if we're resizing
        }               //scanf
    }
}

static void *extend_heap(size_t words)
{
    void *final;
    // Extended words (even for double word boundary alignment)
    size_t extended_words = (words % 2 == 0) ? words : words + 1;

    if ((final = mem_sbrk(extended_words)) == -1)
    {
        return NULL;
    }

    return final;
}

static void *coalesce(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    size_t size = get_size(header_pointer(bp));
    // Since these return pointers to the base of the payload, they
    // need to be shifted back to the header for reads and writes
    size_t *next = header_pointer(bp);
    size_t *prev = header_pointer(bp);

    // Without loss of generality, we will not be coalescing more than
    // three blocks at a time, due to the overheads incurred in seeking
    if (get_alloc(next) && get_alloc(prev))
    {
        // Case 1: prev and next allocated -> do nothing
        return;
    }
    else if (!get_alloc(next) && get_alloc(prev))
    {
        // Case 2: prev free, next allocated -> coalesce with previous
        size += get_size(header_pointer(next));
        remove_free_block(next);
        put(header_pointer(bp), pack(size,0));
        put(footer_pointer(bp), pack(size,0));


    }
    else if (get_alloc(next) && !get_alloc(prev))
    {
        // Case 3: prev allocated, next free -> coalesce with next
        size += get_size(header_pointer(prev));
        remove_free_block(prev);
        put(footer_pointer(bp), pack(size,0));
        put(header_pointer(prev), pack(size,0));
        bp = prev;

    }
    else if (!get_alloc(next) && !get_alloc(prev))
    {
        // Case 4: prev free, next free -> coalesce with both
        size += get_size(header_pointer(prev)) + get_size(header_pointer(next));
        remove_free_block(prev);
        remove_free_block(next);
        put(header_pointer(prev), pack(size,0));
        put(footer_pointer(next), pack(size,0));
        bp  = prev;    
    }

    // Calculate size class
    // Add to appropriate size class
    // NB For every free block, we need to remove it from the array
    // and we need to make sure we know how large it is beforehand
}