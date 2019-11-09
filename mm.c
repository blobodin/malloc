/* Explicit free list malloc implementation:
 *
 * This implementation of malloc uses an explict free list to iterate
 * through free allocated memory effectively. First fit is utilized when
 * searching for a ptr to return, and FIFO is utilized when adding to the
 * free list itself.
 *
 * Headers and footers are used to effectively coalesce and split blocks
 * when necessary. Splitting will occur if possible upon finding a valid
 * block to return in malloc. If possible, coalescing occurs during free
 * when it is called.
 *
 * The notion of size in free nodes and blocks is the entire size of the block
 * (i.e. the size of the header, the size of the footer, the size of the
 * payload). Size_t is used in header and footer so that the allocator works
 * for heaps up to 2^64 byets.
 *
 * Free nodes contain the size of the unallocated block in memory, a prev
 * pointer, and a next pointer. Blocks have a header and payload. A separate
 * footer struct ends each block.
 *
 * This implementation has a good balance of utilization and throughput.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include <math.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
/* #define DEBUG */
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

#define ALIGNMENT (2 * sizeof(size_t))
#define HEAPBOUND ((size_t) pow(2, 64))

/*
 * This struct is the basis for the implicit list. The payload is the
 * memory to be used by the user. The header is used to keep the size of the
 * entire block (including its footer).
 */
typedef struct {
    size_t header;
    /*
     * We don't know what the size of the payload will be, so we will
     * declare it as a zero-length array.  This allow us to obtain a
     * pointer to the start of the payload.
     */
    uint8_t payload[];
} block_t;

/*
 * This struct is an extension of the block structure. The footer is
 * used to keep the size of the entire block (including its header).
 */
typedef struct {
    size_t footer;
} footer_t;

/*
 * This struct is the basis for the free list. Freed blocks are cast to
 * this type. In this way, free nodes are in the same memory space as it
 * freed block counterpart. The space previously used for the payload is
 * instead used for prev and next pointers.
 */
typedef struct list_node_t{
    size_t header;
    struct list_node_t *prev;
    struct list_node_t *next;
} list_node_t;

/* Global variable for the free list. */
list_node_t *head_node = NULL;

/* Takes a freed block and adds its node counterpart to the beginning
 * of the freed list. */
static void add_to_free(block_t *block) {
    list_node_t *new_node = (list_node_t *) ((void *) block);
    new_node->prev = NULL;

    new_node->next = head_node;

    /* This is the case where the list is empty. */
    if (head_node != NULL) {
        head_node->prev = new_node;
    }
    head_node = new_node;
}

/* Takes a used block and removes its node counterpart from the free list.*/
static void remove_from_free(block_t *block) {
    list_node_t *remove_block= (list_node_t *) ((void *) block);

    list_node_t *prev_node = remove_block->prev;
    list_node_t *next_node = remove_block->next;

    /* This checks if its the first node. */
    if (prev_node != NULL) {
        prev_node->next = next_node;
    } else {
        head_node = next_node;
    }

    /* This checks if its the last node. */
    if (next_node != NULL) {
        next_node->prev = prev_node;
    }

}

/* Rounds the requested paylaod size to a multiple of 16 so as to keep
 * the payload addresses 16 byte aligned. Because the notion of
 * size in the header and footer is the size of the entire block
 * (i.e. header, payload, and footer) these are added to the payload size
 * before returning.*/
static size_t round_up(size_t size, size_t n) {
    if (size % n == 0) {
        return size + sizeof(block_t) + sizeof(footer_t);
    }
    return ((size + n - 1) / n * n) + sizeof(block_t) + sizeof(footer_t);
}

/* Helper function to get size of block from header. */
static size_t get_size(block_t *block) {
    return block->header & ~0x1;
}

/* Helper function to get size of block from footer. */
static size_t get_size_footer(footer_t *footer) {
    return footer->footer & ~0x1;
}

/* Helper function to get size of block from node type. */
static size_t get_size_node(list_node_t *node) {
    return node->header & ~0x1;
}

/* Helper function to check if a block is allocated via its header. */
static bool check_allocated(block_t *block) {
    return (block->header & 0x1) == 1;
}

/* Helper function to check if a block is allocated via its footer. */
static bool check_allocated_footer(footer_t *footer) {
    return (footer->footer & 0x1) == 1;
}

/*
* Returns footer of current block.
*/
static inline footer_t *get_next_footer(block_t *block) {
    uint8_t *next_footer =  (uint8_t *) block + get_size(block)
                                - sizeof(footer_t);
    return (footer_t *) next_footer;
}

/* Sets header and footer of block. */
static void set_block(block_t* block, size_t size, bool is_allocated) {
    block->header = size | is_allocated;
    footer_t *footer = get_next_footer(block);
    footer->footer = size | is_allocated;
}

/*
* Checks if current block is the bottom of the heap (since no prologue is used)
* Returns footer of previous block if exists.
*/
static inline footer_t *get_prev_footer(block_t *block) {
    uint8_t *curr_block = (uint8_t *) block;
    if (curr_block == mem_heap_lo() + offsetof(block_t, payload)) {
        return NULL;
    }
    uint8_t *prev_footer = curr_block - sizeof(footer_t);
    return (footer_t *) prev_footer;
}

/*
* Checks if current block is the top of the heap (since no epilogue is used)
* Returns header of next block if exists.
*/
static inline block_t *get_next_header(block_t *block) {
    uint8_t *next_block = (uint8_t *) block + get_size(block);
    if (next_block - 1 == mem_heap_hi()) {
        return NULL;
    }
    return (block_t *) next_block;
}

/*
* Returns header of previous block.
*/
static inline block_t *get_prev_header(block_t *block, footer_t *footer) {
    size_t prev_block_size = get_size_footer(footer);
    uint8_t *prev_header = (uint8_t *)block - prev_block_size;
    return (block_t *) prev_header;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
    /* Re-initializes free list global variable. */
    head_node = NULL;

    /* Pad heap start so first payload is at ALIGNMENT. */
    if ((long) mem_sbrk(ALIGNMENT - offsetof(block_t, payload)) < 0) {
        return -1;
    }

    return 0;
}

/*
 * Split a free block into two blocks, one with the requested size and
 * one with the leftover memory. The first block is set to allocated since
 * it will be used.
 */
static void split(block_t *curr_block, size_t requested_size) {
    /* Forms a new block out of the memory leftover. */
    uint8_t *second_new_block = ((uint8_t *) curr_block) + requested_size;
    size_t leftover_size = get_size(curr_block) - requested_size;
    set_block((block_t *) second_new_block, leftover_size, false);

    /* Forms a new block of the requested memory size. */
    add_to_free((block_t *) second_new_block);
    block_t *first_new_block = curr_block;
    set_block(first_new_block, requested_size, true);
}

/*
 * Searches for first block in the free list that has a size greater than or
 * equal to the requested size. A split is done if possible, and the
 * resulting payload is returned.
 */
static void *search_fit(size_t size){
    size_t block_size = size;
    list_node_t *curr_node = head_node;
    while (curr_node != NULL) {
        size_t curr_size = get_size_node(curr_node);
        /* Checks if curr free node fits the requested size. */
        if (curr_size >= block_size) {
            block_t *curr_block = (block_t *) ((void *) curr_node);
            /*
             * Checks if leftover memory is big enough for another
             * block (i.e checks if a split can occur).
             */
            if (curr_size - block_size >= ALIGNMENT * 2) {
                split(curr_block, block_size);
            } else {
                set_block(curr_block, curr_size, true);
            }
            remove_from_free(curr_block);
            return curr_block->payload;
        } else {
            curr_node = curr_node->next;
        }
    }

    return curr_node;
}

/*
 * malloc - Search for a block in the free list meets the requested size.
 *      Always allocate a block whose size is a multiple of the alignment.
 *      Allocates a new block with mem_sbrk if no valid block is found in the
 *      free list.
 */
void *malloc(size_t size) {
    size_t block_size = round_up(size, ALIGNMENT);
    void *first_fit = search_fit(block_size);

    /* If a valid block is found in the free list, return it. */
    if (first_fit != NULL) {
        return first_fit;
    }

    /* If a valid block is not found in the free list, make a new one. */
    block_t *block = mem_sbrk(block_size);
    if ((long) block < 0) {
        return NULL;
    }

    set_block(block, block_size, true);

    return block->payload;
}

/* Coalesces a block with the next block in memory. Blocks are all multiples of
 * 16 so we know that the resulting block will be valid. */
static void coalesc(block_t *block1, block_t *block2) {
    size_t new_size = get_size(block1) + get_size(block2);
    set_block(block1, new_size, false);
}

/*
 * Frees the requested payload, adding the memory to the free list in the
 * process. The blocks to the left and right are coalesced with the
 * original block if possible.
 */
void free(void *ptr) {
    if (ptr != NULL) {
        block_t *curr_block = ptr - offsetof(block_t, payload);
        size_t size = get_size(curr_block);
        set_block(curr_block, size, false);

        footer_t *prev_footer = get_prev_footer(curr_block);
        block_t *next_block = get_next_header(curr_block);

        /* Keeps track of final free block address to return. This variable
         * may change if coalescing occurs. */
        block_t *free_block = curr_block;

        /* Checks if coalescing can occur between the left and middle blocks.*/
        if (prev_footer && !check_allocated_footer(prev_footer)) {
            block_t *prev_block = get_prev_header(curr_block, prev_footer);
            remove_from_free(prev_block);
            coalesc(prev_block, curr_block);
            free_block = prev_block;
        }

        /* Checks if coalescing can occur between the right and middle blocks.*/
        if (next_block && !check_allocated(next_block)) {
            remove_from_free(next_block);
            coalesc(free_block, next_block);
        }

        /* Adds resulting free block to free list. */
        add_to_free(free_block);
    }
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        free(old_ptr);
        return NULL;
    }

    /* If old_ptr is NULL, then this is just malloc. */
    if (!old_ptr) {
        return malloc(size);
    }

    void *new_ptr = malloc(size);

    /* If malloc() fails, the original block is left untouched. */
    if (!new_ptr) {
        return NULL;
    }

    /* Copy the old data. */
    block_t *block = old_ptr - offsetof(block_t, payload);

    size_t old_size = get_size(block);
    if (size < old_size) {
        old_size = size;
    }
    memcpy(new_ptr, old_ptr, old_size);

    /* Free the old block. */
    free(old_ptr);

    return new_ptr;
}


/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *new_ptr = malloc(bytes);

    /* If malloc() fails, skip zeroing out the memory. */
    if (new_ptr) {
        memset(new_ptr, 0, bytes);
    }

    return new_ptr;
}

/* Prints the relevant information of a memory block stucture (for debugging)*/
static inline void print_block(block_t *block) {
    printf("BlockAdd:%p\n", block);
    printf("Header:%zu\n", block->header);
    printf("PayloadAdd:%p\n", block->payload);
    printf("Footer:%zu\n", get_next_footer(block)->footer);
    printf("FooterAdd:%p\n\n", get_next_footer(block));
}

/*
 * A debugging tool for checking the status of the heap and free list.
 *
 * Current Functionality:
 *     Checks each block's address alignment.
 *     Checks header/footer equality, alignment, and size
 *     Checks coalescing
 *     Checks consistency of prev/next pointers
 *     Checks that free list pointers are within the heap
 *     Checks that num free blocks matches size of free list
 *
 * (Note: Epilogues and prologues are not used, so they do not need to be
 * checked)
 */
void mm_checkheap(int verbose) {
    block_t *curr_block = mem_heap_lo() + offsetof(block_t, payload);

    /* Free counter is used to keep track of consecutive free blocks. */
    size_t free_counter = 0;

    /* Free block counter counts the total num of unallocated blocks. */
    size_t free_block_counter = 0;

    /* Iterates through all blocks in heap. */
    while (curr_block != NULL) {
        /* Checks each block's address alignment. */
        if (((uint8_t) curr_block->payload) % 16 != 0) {
            printf("Alignment Off :%i\n", verbose);
            print_block(curr_block);
            exit(0);
        }

        /* Checks that header and footers of a block match. */
        size_t curr_header = curr_block->header;
        size_t curr_footer = get_next_footer(curr_block)->footer;
        if (curr_header != curr_footer) {
            printf("Header/Footer Don't Match %i\n", verbose);
            print_block((block_t *) curr_block);
            exit(0);
        }

        if (curr_header < ALIGNMENT * 2) {
            printf("Block below minimum size %i\n", verbose);
            exit(0);
        }

        /* Checks coalescing (no two consecutive free blocks) and counts total
         * free nodes in list. */
        if (check_allocated(curr_block) == false) {
            free_counter++;
            free_block_counter++;
            if (free_counter == 2) {
                printf("Two Consecutive Free Blocks %i\n", verbose);
                exit(0);
            }
        } else {
            free_counter = 0;
        }

        curr_block = get_next_header(curr_block);
    }

    /* Free node counter counts the total num of nodes in free list. */
    size_t free_node_counter = 0;
    list_node_t *curr_node = head_node;

    /* Iterates through all nodes in free list. */
    while (curr_node != NULL) {
        /* Checks that prev and next pointers are consistent. */
        list_node_t *prev_node = curr_node->prev;
        list_node_t *next_node = curr_node->next;
        if (next_node != NULL) {
            if (next_node->prev != curr_node) {
                printf("Prev pointer of next wrong %i\n", verbose);
                exit(0);
            }
        }
        if (prev_node != NULL) {
            if (prev_node->next != curr_node) {
                printf("Next pointer of prev wrong %i\n", verbose);
                exit(0);
            }
        }

        /* Checks that free list pointers are within the heap. */
        if ((uint8_t *) curr_node <= (uint8_t *) mem_heap_lo() + 7) {
            printf("Node below bottom of heap %i\n", verbose);
            if ((uint8_t *) curr_node + get_size((block_t *) curr_node)
                > (uint8_t *) mem_heap_hi() - 1){
                printf("Node above top of heap %i\n", verbose);
                exit(0);
            }
            exit(0);
        }
        curr_node = curr_node->next;
        free_node_counter++;
    }

    /* Checks that all unallocated blocks are in the free list. */
    if (free_block_counter != free_node_counter) {
        printf("Free mismatch %i\n", verbose);
        printf("BLOCK: %zu\n", free_block_counter);
        printf("NODE: %zu\n", free_node_counter);
        exit(0);
    }

}
