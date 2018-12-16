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
 * 
 * High level implementation details:
 * -Free memory works as a doubly linked list.
 * -There doesn't need to be a way to iterate over the allocated data, merely know what's allocated, and how large it is
 * -The first several words of the heap are a lookup table, which is a static memory overhead, but should be worth it in long run
 * -We use a simple first-fit memory allocation strategy, and use address ordering for the insertion
 * 
 * VERY IMPORTANT DETAILS TO KEEP IN MIND BECAUSE THEY'RE NOT TRIVIAL AND TOOK US A LONG TIME TO FIGURE OUT:
 * -there is a distinction between user space pointers and pointers we use internally (henceforth dubbed 'malloc space'):
 * user space pointers are aligned TO THE START OF THE PAYLOAD, and malloc space pointers are aligned TO THE START OF THE HEADER.
 * This took us a while to figure out (seems pretty obvious in retrospect) and it effectively means that any pointer that comes
 * from user space needs to have a transform applied to have it work properly, otherwise resulting in numerous segfaults.
 * -alignment is very sensitive to the initial values of the heap. Since we need to align the payload to a dword, the bottom of 
 * the heap needs to be aligned in such a way that this is the case for every payload henceforth.
 * -existing solutions often cast the pointer to a char pointer, in order to simplify the pointer arithmetic (since a char is 
 * 1 byte in size, regardless of platform). We weren't the greatest fans of the approach, so we opted to cast them to size_t, which
 * is a type directly meant to be able to address any location in the address space, do the arithmetic on it as though it were a  
 * regular number and then cast it back to a pointer
 * -the movement between void* and size_t* is quite arbitrary, and we could convert everything to size_t, since we really could use * as much help as the compiler could offer us, which is the reason we ditched macros in the first place (no type checking, and O0 * does not optimize away inline functions, meaning that we could actually debug them, and then use higher optimization levels to
 * do away with function call overhead) 
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
    "QuackerDucky",
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
#define CHUNKSIZE (1 << 12)

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

/* 
 * These functions were adapted from the textbook, but are commented more 
 * liberally, to ensure we don't lose information about them between context
 * switches, and to make them more transparent (the original macros certainly aren't)
*/
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
static inline size_t *shift(size_t *pointer, size_t shft);

/*
 * Functions that will help us manipulate the in-memory free linked lists 
 */
static inline int get_class(size_t size);
static void *get_free_block(int class, size_t size);
static void remove_free_block(void *pointer);
static void add_free_block(int class, void *pointer);
static inline void *get_lookup_row(int class);
static inline size_t *get_next_free(void *base);
static inline size_t *get_prev_free(void *base);

/* 
 * Auxiliary functions that allow us to manipulate the heap, coalesce and split
 * existing blocks, in addition to the heap checker. 
 */
static void *extend_heap(size_t bytes);
static void *coalesce(void *bp);
static void split_block(void *ptr, size_t newsize);
static int mm_checkheap();

/* 
START OF THE GENERAL POINTER MANIPULATION METHODS
*/

/* 
 * align_to_word - given a user-defined size, align it to the next word boundary. 
 * Taking the logical AND with any value greater than a multiple of eight and 
 * ~0x7 will result in a multiple of eight every single time (have confirmed it
 * numerically).
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
    // Since we were running into the problem of noise in subsequent memory
    // manipulations, where the memory was not zeroed properly after use,
    // we got a lot of false positives, which we are now rooting out
    // by checking if an address is on the heap or not
    if (valid_heap_address(pointer))
    {
        return *(size_t *)pointer;
    }
    return NULL;
}

/* 
 * put - assign a given value to the location pointed to 
 * by the pointer.
 */
static inline void put(void *pointer, size_t value)
{
    // Only really need to write to relevant locations in memory.
    if (valid_heap_address(pointer))
    {
        (*(size_t *)pointer) = value;
    }
}

/* 
 * valid_heap_address - check if a given address is valid or not,
 * given the bounds of the heap.
 */
static inline int valid_heap_address(void *bp)
{
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

/* 
 * get_size - get the size of a block, given a malloc space pointer to the header 
 * or the footer of an existing block.
 */
static inline size_t get_size(void *pointer)
{
    return get(pointer) & ~(size_t)0x7;
}

/*
 * get_alloc - get the allocation status of a block, given a malloc space pointer
 * to the header or the footer of an existing block.
 *  
 */
static inline size_t get_alloc(void *pointer)
{
    return get(pointer) & (size_t)0x1;
}

/*
 * header_pointer - given a user space pointer, return the address of its 
 * header.
 */
static inline size_t *header_pointer(void *bp)
{
    if (valid_heap_address(bp))
    {
        return (size_t *)(((size_t)bp) - WSIZE);
    }
    return NULL;
}

/*
 * footer_pointer - given a user space pointer, return the address of its
 * footer.
 */
static inline size_t *footer_pointer(void *bp)
{
    if (valid_heap_address(bp))
    {
        return (size_t *)(((size_t)bp) + get_size((void *)header_pointer(bp)));
    }
    return NULL;
}

/*
 * next_block_ptr - given a user space pointer, return a valid pointer 
 * to the next block, if the block exists.  
 */
static inline void *next_block_ptr(void *bp)
{
    if (valid_heap_address(bp))
    {
        return (void *)(((size_t)footer_pointer(bp)) + 2 * WSIZE);
    }
    return NULL;
}

/* 
 * prev_block_ptr - given a user space pointer, return a valid 
 * pointer to the previous block, if such a block should exist.
 * 
 */
static inline void *prev_block_ptr(void *bp)
{
    if (valid_heap_address(bp))
    {
        return (void *)(((size_t)bp) - get_size((void *)(((size_t)bp) - 2 * WSIZE)) - 2 * WSIZE);
    }
    return NULL;
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
 * ASSUMPTION: the min value for size is 16, which is the 
 * MINCHUNK
 * 
 */
static inline int get_class(size_t size)
{
    for (int i = 0; i < CLASSES; i++)
    {
        // Offset by four to start counting from the MINCHUNK
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

        current = get(get_next_free(current));
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
        // Stopping before current = NULL
        if (!valid_heap_address(get(get_next_free(current))))
        {
            break;
        }
        current = get(get_next_free(current));
    }

    size_t *nextNode = get(get_next_free(current));

    // We're assuming that the previous is always valid
    size_t *prevNode = current;

    // Set the previous ptr of the next block
    if (nextNode != NULL)
    {
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

/* 
 * shift - having noticed that we do a lot of casting between pointer and value, 
 * we decided to make a simple function that abstracts this rather nasty pointer 
 * manipulation
 */
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

    int count = 0;
    // We start by showing the values encoded in the lookup table, and seeing
    // if they all correspond to valid addresses
    while (iterator < lookup_top)
    {
        printf("Lookup table entry 0x%x has the value 0x%x\n", iterator, get(iterator));
        iterator = shift(iterator, WSIZE);
        count++;
    }
    // Checking the size of the lookup_table,
    if (count != CLASSES - 1)
    {
        puts("The lookup table is incorrectly sized!");
    }

    // TODO Check the free lists
    // TODO Check the heap itself

    puts("End of heap consistency checker");
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    void *top;

    // We include one block of padding to ensure that subsequent blocks are aligned
    if ((lookup_table = extend_heap((CLASSES + 3) * WSIZE)) == NULL)
    {
        return -1;
    }

    // Put an empty lookup table for the linked list pointers at the top (bottom?) of the heap
    for (int i = 0; i < CLASSES; i++)
    {
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

    // Just in case, we align it to dword, as an additional precaution
    size_t aligned_page = align_to_word(CHUNKSIZE + 2 * WSIZE);

    if ((top = extend_heap(aligned_page)) == NULL)
    {
        return -1;
    }

    // Add the new free block to the corresponding free list
    size_t sc = get_class(CHUNKSIZE + 2 * WSIZE);
    put(top, pack(CHUNKSIZE, 0));
    put(shift(top, CHUNKSIZE), pack(CHUNKSIZE, 0));

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
    aligned_size = align_to_word(MAX(aligned_size, MINCHUNK));

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
        return;

    // Get size class and size of the block
    size_t size = get_size(header_pointer(ptr));

    // Change allocation status in the header and footer pointers
    put(header_pointer(ptr), pack(size, 0));
    put(footer_pointer(ptr), pack(size, 0));

    // Zero out the chunk, just in case, to make sure that there are no random values floating around
    // in the heap
    memset(ptr, 0, size);

    // Add the free block to size class linked list
    coalesce(ptr);
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

/*
 * extend_heap - a wrapper around mem_sbrk that double checks whether 
 * sbrk can extend heap.
 */
static void *extend_heap(size_t bytes)
{
    void *final;

    if ((final = mem_sbrk(bytes)) == -1)
    {
        return NULL;
    }

    return final;
}

/* 
 * coalesce - merge the previous and next blocks, if they're free, otherwise do nothing.
 */
static void *coalesce(void *bp)
{
    if (valid_heap_address(bp)){
    // Simple check to see if
    if (bp == NULL)
        return;

    size_t size = get_size(header_pointer(bp));
    // Since these return pointers to the base of the payload, they
    // need to be shifted back to the header for reads and writes
    size_t *next = next_block_ptr(bp);
    size_t *prev = prev_block_ptr(bp);

    //decided to create two pointers for the headers of next and previous to cut down number of function calls.
    //seems to improve the Kops even without the -O2 flag
    size_t* nextNode = header_pointer(next);
    size_t* prevNode = header_pointer(prev);
     
    // Checking if either of the conditions is NULL, and barring that, checking if there is any undefined
    // behavior. For that reason, we can't assume that there is in fact a previous or a next, so
    // those pointers effectively become useless. Need some sort of way of handling that

    if (prev == NULL && next == NULL)
        return bp;

    // Without loss of generality, we will not be coalescing more than
    // three blocks at a time, due to the overheads incurred in seeking
    if (get_alloc(nextNode) && get_alloc(prevNode))
    {
        // Case 1: prev and next allocated -> do nothing
        return bp;
    }
    else if (!get_alloc(nextNode) && get_alloc(prevNode))
    {
        // Case 2: prev free, next allocated -> coalesce with previous
        size += align_to_word(get_size(nextNode) + 2 * WSIZE);
        remove_free_block(next);
        put(header_pointer(bp), pack(size, 0));
        put(footer_pointer(next), pack(size, 0));
        memset(bp, 0,size);
        add_free_block(get_class(size), bp);
        return bp;
    }
    else if (get_alloc(nextNode) && !get_alloc(prevNode))
    {
        // Case 3: prev allocated, next free -> coalesce with next
        size += align_to_word(get_size(prevNode) + 2 * WSIZE);
        remove_free_block(prev);
        put(prevNode, pack(size, 0));
        put(footer_pointer(bp), pack(size, 0));
        memset(prev, 0, size);
        bp = prev;
        add_free_block(get_class(size), bp);
        return bp;
    }
    else if (!get_alloc(nextNode) && !get_alloc(prevNode))
    {
        // Case 4: prev free, next free -> coalesce with both
        size = align_to_word(size + get_size(prevNode) + get_size(nextNode) + 4 * WSIZE);
        remove_free_block(prev);
        remove_free_block(next);
        put(prevNode, pack(size, 0));
        put(footer_pointer(next), pack(size, 0));   
        memset(prev, 0, size);
        memset(next,0, size); //added next as well because I think it belongs here too? 
        bp = prev;
        add_free_block(get_class(size), bp);
        return bp;
    }
    }
}

/* 
 * split_block - given a malloc space pointer to a block not on a free list, break it apart,
 * add the fragment to a free list. The original pointer now points to a smaller chunk.
 * 
 * ASSUMPTIONS: newsize includes both header and footer and is already aligned
 */
static void split_block(void *ptr, size_t newsize)
{
    // Get the size and then figure out how large the payload is
    size_t size = get_size(ptr);
    size_t payload = newsize - 2 * WSIZE;

    // Write the header and footer blocks
    put(ptr, pack(payload, 1));
    put(shift(ptr, payload), pack(payload, 1));

    // Then handle the new chunk
    size_t chunksize = size - newsize;
    size_t *new_chunk = shift(ptr, newsize);

    put(new_chunk, pack(chunksize - 2 * WSIZE, 0));
    put(shift(new_chunk, chunksize - 2 * WSIZE), pack(chunksize - 2 * WSIZE, 0));

    // Finally, add the new chunk to the appropriate free list
    add_free_block(get_class(chunksize), new_chunk);
}
