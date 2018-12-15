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
 * | used   |
 * | memory |
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
 *  High level implementation details:
 * -Free memory works as a doubly linked list. How to make it work like one when the allocated size is too small?
 * -There doesn't need to be a way to iterate over the allocated data, merely know what's allocated, and how large it is
 * -The first several words of the heap are a lookup table, which is a static memory overhead, but should be worth it in long run
 * -We use a simple first-fit memory allocation strategy, but should do address ordering for the insertion
 * 
 * VERY IMPORTANT DETAILS TO KEEP IN MIND BECAUSE THEY'RE NOT TRIVIAL AND TOOK US A LONG TIME TO FIGURE OUT:
 * -there is a distinction between user space pointers and pointers we use internally (henceforth dubbed 'malloc space'):
 * user space pointers are aligned TO THE START OF THE PAYLOAD, and malloc space pointers are aligned TO THE START OF THE HEADER.
 * This took us a while to figure out (seems pretty obvious in retrospect) and it effectively means that any pointer that comes
 * from user space needs to have a transform applied to have it work properly, otherwise resulting in numerous segfaults.
 * - 
 * 
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
// size classes: {{16-31}, {32-63}, ..., {131072, +oo}}
// Should be increase this?
#define CLASSES 14

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
static inline int valid_heap_address(void *bp);

// Functions to help us manipulate the free memory
// doubly linked lists
static inline int get_class(size_t size);
static void *get_free_block(int class, size_t size);
static void remove_free_block(void *pointer);
static void add_free_block(int class, void *pointer);
static inline void *get_lookup_row(int class);
static inline size_t *get_next_free(void *base);
static inline size_t *get_prev_free(void *base);
static void *extend_heap(size_t bytes);
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
    if(!valid_heap_address(pointer))
    {
        return NULL;
    }
    else
    {
        return *(size_t *)pointer;
    }
}

/* 
 * put - assign a given value to the location pointed to 
 * by the pointer
 */
static inline void put(void *pointer, size_t value)
{
    if (!valid_heap_address(pointer))
    {
        return NULL;
    }
    else 
    {
        (*(size_t *)pointer) = value;
    }
}

static inline int valid_heap_address(void *bp) {
    return bp < mem_heap_lo() && bp > mem_heap_hi();
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

// Casting to char pointer occurs due to need for pointer arithmetic, due to the
// size of the char, which is 1 byte. This means that any offset will be taken
// at face value. bp stands for base pointer, and it's actually the pointer
// that would be returned by malloc.

// This should work, given a normal pointer
static inline size_t *header_pointer(void *bp)
{
    if (!(valid_heap_address(bp)))
    {
        return NULL;
    }
    else
    {
        return (size_t *)(((size_t)bp) - WSIZE);
    }
}

static inline size_t *footer_pointer(void *bp)
{
    if (!(valid_heap_address(bp)))
    {
        return NULL;
    }
    else
    {
        return (size_t *)(((size_t)bp) + get_size((void *)header_pointer(bp)));
    }
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
        if (valid_heap_address(current)) {
            current = NULL;
        }

    }

    return NULL;
}

/* 
 * remove_free_block - given a size class and a pointer to the base of the block
 * that is being removed, it links the previous and successive
 * elements, removing it from the list.
 */
static inline void remove_free_block(void *pointer)
{
    // Assume malloc space - pointer to base of payload
    size_t *next = (size_t *)header_pointer(get_next_free(pointer));
    size_t *prev = (size_t *)header_pointer(get_prev_free(pointer));
 
    if (!valid_heap_address(next)) {
        next = NULL;
    }
    if (!valid_heap_address(prev)) {
        prev = NULL;
    }



    // While there are four possible combinations of null and not null
    // values for `next` and `prev`, only three of them can occur, since
    // previous has to point either to the lookup table
    if (next != NULL)
    {
        put(shift(next, 2 * WSIZE), prev);
    }

    // Need to check if in lookup table
    if (prev < shift(lookup_table, CLASS_OVERHEAD))
    {
        put(prev, next);
    }
    else
    {
        put(shift(prev, WSIZE), next);
    }

    // // Zero out the next and previous pointers
    put(shift(pointer, WSIZE), pack(0, 0));
    put(shift(pointer, 2 * WSIZE), pack(0, 0));
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
    size_t current_size = get_size(pointer);
    void *lookup_row = get_lookup_row(class);
    size_t *current = get(lookup_row);

    // If lookup table is empty
    if (current == NULL)
    {
        put((void *)lookup_row, pointer);
        put(shift(pointer, WSIZE), 0);
        put(shift(pointer, 2 * WSIZE), 0);
        return;
    }

    // If the lookup table is not empty, there must be at least
    // one element it points to, hence we need to go over the list
    // and figure out where the entry fits address-wise.

    // This is essentially sorting the list in terms of address.
    // Not quite sure why this is all that good at current time,
    // but it will have to do. Note that this also weeds out false
    // positives by explicitly checking for garbage being read
    // and taken as a
    while (current != NULL && current > lookup_table)
    {
        if (!valid_heap_address(get(get_next_free(current)))) {
            break;
        }
        
        current = get(get_next_free(current));
        
    }

    size_t *nextNode = get(get_next_free(current));
    if (!valid_heap_address(nextNode)) {
        nextNode = NULL;
    }

    // We're assuming that the previous is always valid
    size_t *prevNode = current;

    // Set the previous ptr of the next block
    if (nextNode != NULL) {
        put(shift(nextNode, 2 * WSIZE), pointer);
    }

    // Set the next ptr of the previous block
    put(shift(prevNode, WSIZE), pointer);

    // Set the prev and next pointers
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
    return (size_t *)(((size_t)pointer) + shft);
}

/* 

END OF DOUBLE LINKED LIST MANIPULATION METHODS

*/
/*
Checks for the following heap invariants:
- header and footer match
- payload area is aligned, size is valid
- no contiguous free blocks unless coalescing is deferred
- next/prev pointers in consecutive free blocks are consistent
- no allocated blocks in free lists, all free blocks are in free list
- no cycles in free list
- each segregated list contains only blocks in the appropriate size class
*/
static int mm_checkheap()
{
    void *iterator = lookup_table;
    void *heap_top = mem_heap_hi();
    void *lookup_top = shift(lookup_table, CLASS_OVERHEAD);
    puts("\nStart of consistency check");

    while (iterator < lookup_top)
    {
        printf("Lookup table entry 0x%x has the value 0x%x\n", iterator, get(iterator));
        iterator = shift(iterator, WSIZE);
    }
    puts("End of heap consistency checker");
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
    if ((lookup_table = extend_heap((CLASSES + 3) * WSIZE)) == NULL)
    {
        return -1;
    }

    // Put an empty lookup table for the linked list pointers at the top (bottom?) of the heap
    for (int i = 0; i < CLASSES; i++)
    {
        // TODO Replace this with a function call, just please no macros
        put(shift(lookup_table, i * WSIZE), 0);
    }

    // The heap starts directly after the lookup table
    heap_list = shift(lookup_table, CLASS_OVERHEAD);

    // Allocate the footer of the prologue and the header of the epilogue
    put(shift(heap_list, (0 * WSIZE)), 0);
    put(shift(heap_list, (1 * WSIZE)), pack(2 * WSIZE, 1)); // Prologue footer
    put(shift(heap_list, (3 * WSIZE)), pack(0, 1));         // Epilogue header

    // The heap will be growing from between the prologue and the epilogue, so that we could
    // make sure that all is well
    heap_list = shift(heap_list, 2 * WSIZE);

    size_t aligned_page = align_to_word(CHUNKSIZE + 2 * WSIZE);

    if ((top = extend_heap(aligned_page)) == NULL)
    {
        return -1;
    }

    // Add the page to the free list
    size_t sc = get_class(CHUNKSIZE + 2 * WSIZE);
    put(top, pack(CHUNKSIZE, 0));
    put(top + CHUNKSIZE, pack(CHUNKSIZE, 0));

    add_free_block(sc, top);

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
        final = extend_heap(aligned_size);
    }

    put(final, pack(aligned_size - 2 * WSIZE, 1));
    put(shift(final, aligned_size), pack(aligned_size - 2 * WSIZE, 1));

    final = shift(final, WSIZE);
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

    // Zero out the chunk, just in case, to make sure that there are no random values floating around
    // in the heap
    memset(ptr, 0, size);

    // Add the free block to size class linked list
    return coalesce(ptr);
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

static void *extend_heap(size_t bytes)
{
    // ASSUME THAT ALIGNED
    void *final;

    if ((final = mem_sbrk(bytes)) == -1)
    {
        return NULL;
    }

    return final;
}

static void *coalesce(void *bp)
{
    // Simple check to see if
    if (bp == NULL)
    {
        return;
    }

    size_t size = get_size(header_pointer(bp));
    // Since these return pointers to the base of the payload, they
    // need to be shifted back to the header for reads and writes
    size_t *next = next_block_ptr(bp);
    size_t *prev = prev_block_ptr(bp);

    // Checking if either of the conditions is NULL, and barring that, checking if there is any undefined
    // behavior. For that reason, we can't assume that there is in fact a previous or a next, so
    // those pointers effectively become useless. Need some sort of way of handling that

    // There's no next, then coalescing can happen to the left only
    if (next == NULL || next > mem_heap_hi())
    {
        return;
    }

    // There's no previous entry, then coalescing happens to the right only
    if (prev == NULL || prev < shift(lookup_table, CLASS_OVERHEAD))
    {
    }

    // Without loss of generality, we will not be coalescing more than
    // three blocks at a time, due to the overheads incurred in seeking
    if (get_alloc(header_pointer(next)) && get_alloc(header_pointer(prev)))
    {
        // Case 1: prev and next allocated -> do nothing
        return;
    }
    else if (!get_alloc(header_pointer(next)) && get_alloc(header_pointer(prev)))
    {
        // Case 2: prev free, next allocated -> coalesce with previous
        size += get_size(header_pointer(next));
        remove_free_block(next);
        put(header_pointer(bp), pack(size, 0));
        put(footer_pointer(bp), pack(size, 0));
    }
    else if (get_alloc(header_pointer(next)) && !get_alloc(header_pointer(prev)))
    {
        // Case 3: prev allocated, next free -> coalesce with next
        size += get_size(header_pointer(prev));
        remove_free_block(prev);
        put(footer_pointer(bp), pack(size, 0));
        put(header_pointer(prev), pack(size, 0));
        bp = prev;
    }
    else if (!get_alloc(header_pointer(next)) && !get_alloc(header_pointer(prev)))
    {
        // Case 4: prev free, next free -> coalesce with both
        size = size + get_size(header_pointer(prev)) + get_size(header_pointer(next));
        remove_free_block(prev);
        remove_free_block(next);
        put(header_pointer(prev), pack(size, 0));
        put(footer_pointer(next), pack(size, 0));
        bp = prev;
    }

    int sc = get_class(size);
    add_free_block(sc, bp);
}