/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
  * Overview of my allocator:
- both allocated and free blocks share the same data structure block_t, only
  that the second part of the block varies by accessing different elements in
  a union. allocated blocks have payload while free blocks have a struct that
  contains both a pointer to the previous free block and a pointer to the next
  free block.
- free list: a block_t* array storing different size of free blocks in different
  elements (segment lists). A total of 14 segment lists.
- Only free blocks that aren't minimum size block have footers, all other blocks
  only have headers.
- The free blocks are added to the free list according to their size.
- The fit function is a mix one (better fit)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Yuqiao Hu <yuqiaohu@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * the targeted block size (max)
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

static const size_t searchtime = 0x10;

/**
 * to AND with the word to obtain the allocation status
 * change from 0x1 to 0x7 to include 3 allocation status bits
 * first bit for last block and second bit for current block
 * third bit for indicating whether it's a min block
 */
static const word_t alloc_mask = 0x7;

/**
 * to get the last bit (current block's alloc status)
 */
static const word_t alloc_mask_curr = 0x1;

/**
 * to get the status of whether it's a min block
 */
static const word_t min_mask = 0x4;

/**
 * to AND with word to obtain the size of the block
 */
static const word_t size_mask = ~(word_t)0xF;

static const size_t free_16 = 0x10;

static const size_t free_32 = 0x20;

static const size_t free_48 = 0x30;

static const size_t free_64 = 0x40;

static const size_t free_128 = 0x80;

static const size_t free_256 = 0x100;

static const size_t free_512 = 0x200;

static const size_t free_1024 = 0x400;

static const size_t free_2048 = 0x800;

static const size_t free_4096 = 0x1000;

static const size_t free_8192 = 0x2000;

static const size_t free_16384 = 0x4000;

static const size_t free_32768 = 0x8000;

static const size_t free_size = 0x0E;

typedef struct block block_t;

/** Represents the header and payload of one block in the heap */
struct block {
    /** Header contains size + allocation flag */
    word_t header;

    union {
        struct {
            block_t *next;
            block_t *prev;
        };
        char payload[0];
    };
};

/* Global variables */

/** an arrary storing all free list starter pointers
 *  index 0: 0-16 byte free list
 *  index 1: 16-32 byte free list
 *  index 2: 32-48 byte free list
 *  index 3: 48-64 byte free list
 *  index 4: 64-128 byte free list
 *  index 5: 128-256 byte free list
 *  index 6: 256-512 byte free list
 *  index 7: 512-1024 byte free list
 *  index 8: 1024-2048 byte free list
 *  index 9: 2048-4096 byte free list
 *  index 10: 4096-8192 byte free list
 *  index 11: 8192-16384 byte free list
 *  index 12: 16384-32768 byte free list
 *  index 13: 32768-inf byte free list
 */
static block_t *free_list_start[free_size];

/** Pointer to first block in the heap */
static block_t *heap_start = NULL;

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * Returns the maximum of two integers.
 * param[in] x
 * param[in] y
 * return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * Rounds `size` up to next multiple of n
 * param[in] size
 * param[in] n
 * return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * param[in] size The size of the block being represented
 * param[in] alloc True if the block is allocated
 * return The packed value
 */
static word_t pack(size_t size, bool alloc_prev, bool alloc_curr,
                   bool min_block) {
    word_t word = size;
    word_t alloc_status = (((word_t)alloc_prev << 1) | (word_t)alloc_curr);
    if (min_block) {
        // set the min block status to 1
        alloc_status |= min_mask;
    }
    word |= alloc_status;
    return word;
}

/**
 * Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * param[in] word
 * return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * Extracts the size of a block from its header.
 * param[in] block
 * return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * param[in] bp A pointer to a block's payload
 * return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * param[in] block
 * return A pointer to the block's payload
 * pre The block must be a valid block, not a boundary tag.
 *
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * param[in] block
 * return A pointer to the block's footer
 * pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * Given a block footer, returns a pointer to the corresponding
 *        header.
 * param[in] footer A pointer to the block's footer
 * return A pointer to the start of the block
 * pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * param[in] word
 * return The allocation status correpsonding to the word
 */
static size_t extract_alloc(word_t word) {
    return (word & alloc_mask);
}

/**
 * Returns the allocation status of a block, based on its header.
 * param[in] block
 * return The allocation status of the block
 */
static bool get_alloc(block_t *block, bool prev) {
    size_t alloc_status = extract_alloc(block->header);
    if (prev) {
        // get the alloc status of previous block
        return (bool)((alloc_status >> 1) & alloc_mask_curr);
    }
    // get the alloc status of current block
    return (bool)(alloc_status & alloc_mask_curr);
}

/**
 * Returns whether previous block is a min block
 * param[in] block
 * return true if it is a min block and false otherwise
 */
static bool is_minblock(block_t *block) {
    size_t alloc_status = extract_alloc(block->header);
    return (bool)(alloc_status >> 2);
}

/**
 * check whether previous block is free
 *
 * param[in] block
 * return true if prev block is free and false otherwise
 */
static bool get_prev_alloc(block_t *block) {
    return get_alloc(block, true);
}

/**
 * Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * param[in] block
 * return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    if (asize == min_block_size) {
        return wsize;
    }
    if (get_alloc(block, false)) {
        return asize - wsize;
    }
    return asize - dsize;
}

/**
 * Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block, bool prev) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, prev, true, false);
}

/**
 * get the free list a particular size belongs to
 *
 *
 * param[in] size The size of a free block
 * return the free list start pointer that the block size should stay
 */
int get_free_list(size_t size) {
    if (size <= free_16) {
        return 0;
    } else if (size <= free_32) {
        return 1;
    } else if (size <= free_48) {
        return 2;
    } else if (size <= free_64) {
        return 3;
    } else if (size <= free_128) {
        return 4;
    } else if (size <= free_256) {
        return 5;
    } else if (size <= free_512) {
        return 6;
    } else if (size <= free_1024) {
        return 7;
    } else if (size <= free_2048) {
        return 8;
    } else if (size <= free_4096) {
        return 9;
    } else if (size <= free_8192) {
        return 10;
    } else if (size <= free_16384) {
        return 11;
    } else if (size <= free_32768) {
        return 12;
    } else {
        return 13;
    }
}

/**
 * the fundamental function of insert_free
 *
 *
 * param[in] block The free block waiting to be inserted
 * param[in] free_list_start The free list this block is going to use
 * pre block is not NULL
 * return the free list start pointer being changed
 */
block_t *insert_free_basic(block_t *block, int i) {
    dbg_requires(block != NULL);

    if (free_list_start[i] == NULL) {
        block->prev = block;
        block->next = block;
        free_list_start[i] = block;
    } else {
        // LIFO
        block_t *old_start = free_list_start[i];
        block_t *old_end = old_start->prev;
        block->prev = old_end;
        old_end->next = block;
        block->next = old_start;
        old_start->prev = block;
        free_list_start[i] = block;
    }
    return free_list_start[i];
}

/**
 * the fundamental function of insert_free (for mini block only)
 *
 *
 * param[in] block The free block waiting to be inserted
 * param[in] free_list_start The free list this block is going to use
 * pre block is not NULL
 * return the free list start pointer being changed
 */
block_t *insert_free_mini(block_t *block, int i) {
    dbg_requires(block != NULL);

    if (free_list_start[i] == NULL) {
        block->next = block;
        free_list_start[i] = block;
    } else {
        // LIFO
        block_t *old_start = free_list_start[i];
        block->next = old_start;
        free_list_start[i] = block;
    }
    return free_list_start[i];
}

/**
 * Use First in First out rule to insert a free block to free list
 *
 *
 * param[in] block The free block waiting to be inserted
 * pre block is not NULL
 */
static void insert_free(block_t *block) {
    dbg_requires(block != NULL);

    size_t size = get_size(block);
    int i = get_free_list(size);
    if (i == 0) {
        insert_free_mini(block, i);
    } else {
        insert_free_basic(block, i);
    }
}

/**
 * the fundamental function of clear_free
 *
 * param[in] block The free block has been used
 * param[in] free_list_start The free list the block is in
 * pre block is not NULL
 * return the free list start pointer being changed
 */
block_t *clear_free_basic(block_t *block, int i) {
    dbg_requires(block != NULL);

    if (free_list_start[i] == NULL) {
        return NULL;
    }

    block_t *prev_block = block->prev;
    block_t *next_block = block->next;

    if (prev_block == next_block) {
        // one block
        if (prev_block == block) {
            free_list_start[i] = NULL;
        } else {
            // two blocks
            prev_block->prev = prev_block;
            prev_block->next = prev_block;
            free_list_start[i] = prev_block;
        }
    }

    // multple blocks
    prev_block->next = next_block;
    next_block->prev = prev_block;
    if (block == free_list_start[i]) {
        free_list_start[i] = next_block;
    }

    return free_list_start[i];
}

/**
 * the fundamental function of clear_free (only for mini block)
 *
 * param[in] block The free block has been used
 * param[in] free_list_start The free list the block is in
 * pre block is not NULL
 * return the free list start pointer being changed
 */
block_t *clear_free_mini(block_t *block, int i) {
    dbg_requires(block != NULL);

    if (free_list_start[i] == NULL) {
        return NULL;
    }

    block_t *next_block = block->next;

    if (block == next_block) {
        // one block
        free_list_start[i] = NULL;
        return free_list_start[i];
    }

    // multple blocks
    if (block == free_list_start[i]) {
        free_list_start[i] = next_block;
    } else {
        // find where the block stays
        for (block_t *bl = free_list_start[i]; bl != bl->next; bl = bl->next) {
            if (bl->next == block) {
                bl->next = next_block;
                break;
            }
        }
    }

    return free_list_start[i];
}

/**
 * pull the free block used out of the free list
 *
 * param[in] block The free block that has been used
 * pre block is not NULL
 */
static void clear_free(block_t *block) {
    dbg_requires(block != NULL);

    size_t size = get_size(block);
    int i = get_free_list(size);
    if (i == 0) {
        clear_free_mini(block, i);
    } else {
        clear_free_basic(block, i);
    }
}

/**
 * Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * param[in] block A block in the heap
 * return The next consecutive block on the heap
 * pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * Finds the next consecutive free block in the freelist.
 *
 * This function accesses the next block in the "explicit free list"
 *
 * param[in] block A block in the heap
 * return The next consecutive free block
 * pre The block is not the epilogue
 */
static block_t *find_next_free(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return block->next;
}

/**
 * Writes from an allocated block to become a free one
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * param[out] block The location to begin writing the block header
 * param[in] size The size of the new block
 * param[in] prev The allocation status of the previous block
 * param[in] alloc The allocation status of the new block
 */
static void alloc2free(block_t *block, size_t size, bool prev, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);

    bool min = (size == min_block_size);
    bool prev_min = is_minblock(block);

    if (!prev) {
        // prev block is free
        block->header = pack(size, false, alloc, prev_min);
        if (!min) {
            word_t *footerp = header_to_footer(block);
            *footerp = pack(size, false, alloc, prev_min);
        }
    } else {
        // prev block is allocated
        block->header = pack(size, true, alloc, prev_min);
        if (!min) {
            word_t *footerp = header_to_footer(block);
            *footerp = pack(size, true, alloc, prev_min);
        }
    }
    insert_free(block);
}

/**
 * Writes from a free block to become an allocated one.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * param[out] block The location to begin writing the block header
 * param[in] size The size of the new block
 * param[in] prev The allocation status of the previous block
 * param[in] alloc The allocation status of the new block
 */
static void free2alloc(block_t *block, size_t size, bool prev, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);

    clear_free(block);
    bool is_min = is_minblock(block);
    if (!prev) {
        // prev block is free
        block->header = pack(size, false, alloc, is_min);
    } else {
        // prev block is allocated
        block->header = pack(size, true, alloc, is_min);
    }
}

static void modify_next(block_t *next, bool prev, bool is_min) {
    size_t size = get_size(next);
    bool alloc = get_alloc(next, false);
    if (size != 0) {
        next->header = pack(size, prev, alloc, is_min);
        if ((!alloc) && (size != min_block_size)) {
            word_t *footerp = header_to_footer(next);
            *footerp = pack(size, prev, alloc, is_min);
        }
    } else {
        next->header = pack(size, prev, alloc, is_min);
    }
}

/**
 * Finds the footer of the previous block on the heap.
 * param[in] block A block in the heap
 * pre previous block has to be free and not min block
 * return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    dbg_requires(!is_minblock(block));
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * param[in] block A block in the heap
 * pre the previous block is a free block and not a min block
 * return The previous consecutive free block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(!is_minblock(block));
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/**
 * Finds the previous free block in th freelist.
 *
 * param[in] block A block in the heap
 * return The previous consecutive free block in the freelist.
 */
static block_t *find_prev_free(block_t *block) {
    dbg_requires(block != NULL);

    return block->prev;
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * coalesce consecutive empty blocks to make a big one
 *
 * param[in] block
 * pre block is empty & not prelogue or epilogue
 * post result != NULL, no consecutive empty blocks within area
 * return the coalesced block
 */
static block_t *coalesce_block(block_t *block) {

    size_t size;
    bool prev_alloc;
    bool prev_min = false;

    block_t *next = find_next(block);
    if (!get_prev_alloc(block)) {
        // prev block is a free block
        block_t *prev;
        if (is_minblock(block)) {
            prev = (block_t *)((char *)block - dsize);
        } else {
            prev = find_prev(block);
        }
        // case 1: prev + next both free
        if (!get_alloc(next, false)) {
            prev_alloc = get_prev_alloc(prev);
            dbg_assert(prev_alloc == 1);
            size = get_size(prev) + get_size(block) + get_size(next);
            clear_free(block);
            clear_free(prev);
            clear_free(next);
            block = prev;
            alloc2free(block, size, prev_alloc, false);
            if (size == min_block_size) {
                prev_min = true;
            }
            modify_next(find_next(block), false, prev_min);
        }
        // case 2: only prev free
        else {
            prev_alloc = get_prev_alloc(prev);
            dbg_assert(prev_alloc == 1);
            size = get_size(prev) + get_size(block);
            clear_free(block);
            clear_free(prev);
            block = prev;
            alloc2free(block, size, prev_alloc, false);
            if (size == min_block_size) {
                prev_min = true;
            }
            modify_next(find_next(block), false, prev_min);
        }
    } else {
        // prev is not a free block
        // case 3: only next free
        if (!get_alloc(next, false)) {
            prev_alloc = get_prev_alloc(block);
            size = get_size(block) + get_size(next);
            clear_free(block);
            clear_free(next);
            alloc2free(block, size, prev_alloc, false);
            if (size == min_block_size) {
                prev_min = true;
            }
            modify_next(find_next(block), false, prev_min);
        }
        // case 4: prev + next both not free -> just return
    }
    return block;
}

/**
 * enlarge heap as blocks require more memory
 *
 * param[in] size
 * post block is NULL or is right after the previous epilogue
 * return the new block that is added after the heap is extended (NULL if
 * failed)
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    bool prev_alloc = get_prev_alloc(block);
    alloc2free(block, size, prev_alloc, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next, false);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * split a block into 2 to satisfy smaller size requirements
 *
 *
 * param[in] block
 * param[in] asize
 * return None
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block, false));

    size_t block_size = get_size(block);
    bool prev_alloc = get_prev_alloc(block);
    bool prev_min = false;
    bool next_min = false;

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        free2alloc(block, asize, prev_alloc, true);
        if (asize == min_block_size) {
            prev_min = true;
        }

        block_next = find_next(block);
        size_t size = block_size - asize;
        if (size == min_block_size) {
            next_min = true;
        }
        alloc2free(block_next, size, true, false);
        modify_next(block_next, true, prev_min);
        modify_next(find_next(block_next), false, next_min);
    }

    dbg_ensures(get_alloc(block, false));
}

/**
 * the fundamental function of find_fit
 *
 * param[in] asize the desired size of the block wanna allocate
 * param[in] free_list_start the free list it should look at according to
 *                            the block's size
 * return the block or NULL
 */
static block_t *find_fit_basic(size_t asize, block_t *free_list_starter) {
    block_t *block;

    if (free_list_starter == NULL) {
        return NULL;
    }
    size_t sizeb;
    block = free_list_starter;
    sizeb = get_size(block);

    if (asize <= sizeb && (sizeb - asize <= free_16)) {
        return block;
    }
    block = find_next_free(block);

    size_t mindiff;
    block_t *best = free_list_starter;
    // whether mindiff has been initialzed
    bool init = false;
    size_t times = 0;
    if (asize <= sizeb) {
        // first block can be used
        mindiff = sizeb - asize;
        init = true;
    }

    for (; block != free_list_starter; block = find_next_free(block)) {
        sizeb = get_size(block);
        if (asize <= sizeb && (sizeb - asize) <= free_16) {
            return block;
        } else if (times == searchtime) {
            if (init) {
                return best;
            } else if (!init && (asize <= get_size(free_list_starter))) {
                return free_list_starter;
            }
        } else {
            if ((sizeb - asize) >= 0) {
                if (!init || (sizeb - asize < mindiff)) {
                    mindiff = sizeb - asize;
                    best = block;
                }
            }
        }
        times += 1;
    }
    if (init) {
        return best;
    } else if (!init && (asize <= get_size(free_list_starter))) {
        return free_list_starter;
    }
    return NULL; // no fit found
}

/**
 * find am empty space to put in a block of asize [First Fit]
 *
 * param[in] asize the desired size of the block wanna allocate
 * return the block or NULL
 */
static block_t *find_fit(size_t asize) {
    block_t *block;

    if (asize <= free_16) {
        size_t times = 0;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_32) {
        size_t times = 1;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_48) {
        size_t times = 2;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_64) {
        size_t times = 3;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_128) {
        size_t times = 4;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_256) {
        size_t times = 5;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_512) {
        size_t times = 6;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_1024) {
        size_t times = 7;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_2048) {
        size_t times = 8;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_4096) {
        size_t times = 9;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_8192) {
        size_t times = 10;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_16384) {
        size_t times = 11;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else if (asize <= free_32768) {
        size_t times = 12;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    } else {
        size_t times = 13;
        while (times < free_size) {
            block = find_fit_basic(asize, free_list_start[times]);
            if (block != NULL) {
                return block;
            }
            times += 1;
        }
    }
    return block;
}

/**
 * check if all free lists are empty
 *
 * return true if all are empty and false otherwise
 */
bool check_freenull() {
    for (size_t i = 0; i < free_size; i++) {
        if (free_list_start[i] != NULL) {
            return false;
        }
    }
    return true;
}

size_t check_minimatch(block_t *free_list_start, size_t size, size_t prevsize,
                       int line, void *low, void *high) {
    block_t *freeblock;
    size_t count_free = 0;

    if (free_list_start == NULL) {
        return count_free;
    }

    freeblock = free_list_start;
    // all free list pointers are between heap_lo and heap_hi
    if ((void *)freeblock <= low) {
        dbg_printf("line %d: free block exceeds lower limit of heap.\n", line);
        return false;
    }
    if ((void *)freeblock >= (high - 7)) {
        dbg_printf("line %d: free block exceeds upper limit of heap.\n", line);
        return false;
    }

    // check first free block has the correct bucket size
    if (((get_size(freeblock) > size) && (size != 0)) ||
        get_size(freeblock) <= prevsize) {
        dbg_printf("line %d: free block size doesn't match bucket size.\n",
                   line);
        return false;
    }

    freeblock = freeblock->next;
    count_free += 1;

    for (; freeblock != freeblock->next; freeblock = freeblock->next) {
        // all free list pointers are between heap_lo and heap_hi
        if ((void *)freeblock <= low) {
            dbg_printf("line %d: free block exceeds lower limit of heap.\n",
                       line);
            return false;
        }
        if ((void *)freeblock >= (high - 7)) {
            dbg_printf("line %d: free block exceeds upper limit of heap.\n",
                       line);
            return false;
        }

        // check free block has the correct bucket size
        if (((get_size(freeblock) > size) && (size != 0)) ||
            get_size(freeblock) <= prevsize) {
            dbg_printf("line %d: free block size doesn't match bucket size.\n",
                       line);
            return false;
        }

        // count num of blocks in free list
        count_free += 1;
    }

    return count_free;
}

size_t check_freematch(block_t *free_list_start, size_t size, size_t prevsize,
                       int line, void *low, void *high) {
    block_t *freeblock;
    block_t *prev;
    block_t *next;
    size_t count_free = 0;

    if (free_list_start == NULL) {
        return count_free;
    }
    // next, prev are consistent
    freeblock = free_list_start;
    next = find_next_free(freeblock);
    if (next->prev != freeblock) {
        dbg_printf("line %d: next free block's prev != current free block.\n",
                   line);
        return false;
    }
    prev = freeblock->prev;
    if (prev->next != freeblock) {
        dbg_printf("line %d: prev free block's next != current free block.\n",
                   line);
        return false;
    }

    // all free list pointers are between heap_lo and heap_hi
    if ((void *)freeblock <= low) {
        dbg_printf("line %d: free block exceeds lower limit of heap.\n", line);
        return false;
    }
    if ((void *)freeblock >= (high - 7)) {
        dbg_printf("line %d: free block exceeds upper limit of heap.\n", line);
        return false;
    }

    // check first free block has the correct bucket size
    if (((get_size(freeblock) > size) && (size != 0)) ||
        get_size(freeblock) <= prevsize) {
        dbg_printf("line %d: free block size doesn't match bucket size.\n",
                   line);
        return false;
    }

    freeblock = find_next_free(freeblock);
    count_free += 1;

    for (; freeblock != free_list_start;
         freeblock = find_next_free(freeblock)) {
        // next, prev are consistent
        next = find_next_free(freeblock);
        if (next->prev != freeblock) {
            dbg_printf(
                "line %d: next free block's prev != current free block.\n",
                line);
            return false;
        }
        prev = freeblock->prev;
        if (prev->next != freeblock) {
            dbg_printf(
                "line %d: prev free block's next != current free block.\n",
                line);
            return false;
        }

        // all free list pointers are between heap_lo and heap_hi
        if ((void *)freeblock <= low) {
            dbg_printf("line %d: free block exceeds lower limit of heap.\n",
                       line);
            return false;
        }
        if ((void *)freeblock >= (high - 7)) {
            dbg_printf("line %d: free block exceeds upper limit of heap.\n",
                       line);
            return false;
        }

        // check free block has the correct bucket size
        if (((get_size(freeblock) > size) && (size != 0)) ||
            get_size(freeblock) <= prevsize) {
            dbg_printf("line %d: free block size doesn't match bucket size.\n",
                       line);
            return false;
        }

        // count num of blocks in free list
        count_free += 1;
    }

    return count_free;
}

/**
 *
 * param[in] line
 * return
 */
bool mm_checkheap(int line) {

    // prologue and epilogue
    // prologue
    word_t *prologue = (word_t *)mem_heap_lo();
    if (prologue == NULL) {
        dbg_printf("line %d: prologue is NULL.\n", line);
        return false;
    }
    if (extract_size(*prologue) != 0) {
        dbg_printf("line %d: prologue size != 0.\n", line);
        return false;
    }
    if (!extract_alloc(*prologue)) {
        dbg_printf("line %d: prologue not allocated.\n", line);
        return false;
    }
    // epilogue
    block_t *epilogue = mem_heap_hi() - 7;
    if (epilogue == NULL) {
        dbg_printf("line %d: epilogue is NULL.\n", line);
        return false;
    }
    if (get_size(epilogue) != 0) {
        dbg_printf("line %d: epilogue size != 0.\n", line);
        return false;
    }
    if (!get_alloc(epilogue, false)) {
        dbg_printf("line %d: epilogue not allocated.\n", line);
        return false;
    }

    block_t *block;
    void *low = mem_heap_lo();
    void *high = mem_heap_hi();
    bool is_empty = false;
    size_t count = 0;

    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {

        // blocks lie within heap boundarie
        if ((void *)block <= low) {
            dbg_printf("line %d: block exceeds lower limit of heap.\n", line);
            return false;
        }
        if ((void *)block >= (high - 7)) {
            dbg_printf("line %d: block exceeds upper limit of heap.\n", line);
            return false;
        }

        // block's header and footer
        word_t header = block->header;
        if ((!get_alloc(block, false)) && (get_size(block) != min_block_size)) {
            word_t footer = *header_to_footer(block);
            // test if header & footer match
            if (extract_size(header) != extract_size(footer)) {
                dbg_printf("line %d: header size != footer size.\n", line);
                return false;
            }
            if (extract_alloc(header) != extract_alloc(footer)) {
                dbg_printf("line %d: header alloc != footer alloc.\n", line);
                return false;
            }
        }
        // if content correct
        block_t *next = find_next(block);
        if ((unsigned long)block + get_size(block) != (unsigned long)next) {
            dbg_printf("line %d: block size incorrect.\n", line);
            return false;
        }

        size_t size = get_size(block);
        // if payload double-word aligned
        if (size % dsize != 0) {
            dbg_printf("line %d: payload size not double-word aligned.\n",
                       line);
            return false;
        }

        if (size == min_block_size) {
            block_t *next = find_next(block);
            if (block != NULL) {
                if (!is_minblock(next)) {
                    dbg_printf("line %d: next block doesn't show min block.\n",
                               line);
                }
            }
        }

        // coalescing: check no consecutive free blocks
        if (!get_alloc(block, false)) {
            if (is_empty) {
                dbg_printf("line %d: consecutive free blocks appear.\n", line);
                return false;
            } else {
                is_empty = true;
            }
        } else {
            is_empty = false;
        }

        // count actual number of free blocks in heap
        if (!get_alloc(block, false)) {
            count += 1;
        }
    }

    // ---- check the free list below ----
    size_t count_free = 0;

    if (count == 0 && (!check_freenull())) {
        dbg_printf("line %d: heap has no free blocks but free list has.\n",
                   line);
        return false;
    }

    if (count != 0 && check_freenull()) {
        dbg_printf("line %d: heap has free blocks but free list doesn't.\n",
                   line);
        return false;
    }

    if (!check_freenull()) {
        count_free +=
            check_minimatch(free_list_start[0], free_16, 0, line, low, high);
        count_free += check_freematch(free_list_start[1], free_32, free_16,
                                      line, low, high);
        count_free += check_freematch(free_list_start[2], free_48, free_32,
                                      line, low, high);
        count_free += check_freematch(free_list_start[3], free_64, free_48,
                                      line, low, high);
        count_free += check_freematch(free_list_start[4], free_128, free_64,
                                      line, low, high);
        count_free += check_freematch(free_list_start[5], free_256, free_128,
                                      line, low, high);
        count_free += check_freematch(free_list_start[6], free_512, free_256,
                                      line, low, high);
        count_free += check_freematch(free_list_start[7], free_1024, free_512,
                                      line, low, high);
        count_free += check_freematch(free_list_start[8], free_2048, free_1024,
                                      line, low, high);
        count_free += check_freematch(free_list_start[9], free_4096, free_2048,
                                      line, low, high);
        count_free += check_freematch(free_list_start[10], free_8192, free_4096,
                                      line, low, high);
        count_free += check_freematch(free_list_start[11], free_16384,
                                      free_8192, line, low, high);
        count_free += check_freematch(free_list_start[12], free_32768,
                                      free_16384, line, low, high);
        count_free += check_freematch(free_list_start[13], 0, free_32768, line,
                                      low, high);

        if (count != count_free) {
            dbg_printf("actual number : %d\n", (int)count);
            dbg_printf("free list number : %d\n", (int)count_free);
            dbg_printf("line %d: the number of free blocks doesn't match.\n",
                       line);
            return false;
        }
    }
    return true;
}

/**
 * initialize the heap to have prologue & epilogue
 *
 * post return true then a valid empty heap
 * return true if succeed and false otherwise
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, false, true, true); // Heap prologue (block footer)
    start[1] = pack(0, true, true, true);  // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // initailize all free list pointers
    for (size_t i = 0; i < free_size; i++) {
        free_list_start[i] = NULL;
    }

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * allocate a block with size in heap
 *
 * param[in] size
 * post if not enough memory return NULL
 *       allocated block should be previously free
 * return the payload of the allocated block
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;
    bool prev_min = false;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);
    if (asize == min_block_size) {
        prev_min = true;
    }

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block, false));

    // Mark block as allocated
    size_t block_size = get_size(block);
    bool prev_alloc = get_prev_alloc(block);
    free2alloc(block, block_size, prev_alloc, true);
    modify_next(find_next(block), true, prev_min);

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 *
 * function: free the current block and coalesce
 * argument: the block intended to free
 * postcondition: the block is freed
 *
 * param[in] bp
 * return NONE
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    bool prev_min = false;
    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    if (size == min_block_size) {
        prev_min = true;
    }

    // The block should be marked as allocated
    dbg_assert(get_alloc(block, false));

    // Mark the block as free
    bool prev_alloc = get_prev_alloc(block);
    alloc2free(block, size, prev_alloc, false);
    modify_next(find_next(block), false, prev_min);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 *
 * function: reallocate a block to targeted size
 * arguments: the payload to be reallocated, the desired size
 * postcondition: if size == 0, fun equals free ptr
 *                if ptr == NULL, fun equals malloc(size)
 *                other: malloc new block and free old one
 *
 * param[in] ptr
 * param[in] size
 * return new reallocated block (void*)
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 *
 * function: allocate block with all elements initialized to 0
 * arguments: size of one element, size of total elements
 * postcondition: allocated block is initialized
 *
 * param[in] elements
 * param[in] size
 * return the allocated & intialized block or NULL
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */