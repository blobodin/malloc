/*
 * mm-bump.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
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

typedef struct {
    size_t header;
    /*
     * We don't know what the size of the payload will be, so we will
     * declare it as a zero-length array.  This allow us to obtain a
     * pointer to the start of the payload.
     */
    uint8_t payload[];
} block_t;

typedef struct {
    size_t footer;
} footer_t;


typedef struct list_node_t{
    size_t header;
    struct list_node_t *prev;
    struct list_node_t *next;
} list_node_t;

list_node_t *head_node = NULL;

static void add_to_free(block_t *block) {
    list_node_t *new_node = (list_node_t *) ((void *) block);
    new_node->prev = NULL;

    new_node->next = head_node;
    if (head_node != NULL) {
        head_node->prev = new_node;
    }
    head_node = new_node;
}

static void remove_from_free(block_t *block) {
    list_node_t *remove_block= (list_node_t *) ((void *) block);

    list_node_t *prev_node = remove_block->prev;
    list_node_t *next_node = remove_block->next;

    if (prev_node != NULL) {
        prev_node->next = next_node;
    } else {
        head_node = next_node;
    }
    if (next_node != NULL) {
        next_node->prev = prev_node;
    }

}

static size_t round_up(size_t size, size_t n) {
    if (size % n == 0) {
        return size + sizeof(block_t) + sizeof(footer_t);
    }
    return ((size + n - 1) / n * n) + sizeof(block_t) + sizeof(footer_t);
}

static size_t get_size(block_t *block) {
    return block->header & ~0x1;
}

static size_t get_size_node(list_node_t *node) {
    return node->header & ~0x1;
}

static size_t get_size_footer(footer_t *footer) {
    return footer->footer & ~0x1;
}

static bool check_allocated(block_t *block) {
    return (block->header & 0x1) == 1;
}

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

static void set_block(block_t* block, size_t size, bool is_allocated) {
    block->header = size | is_allocated;
    footer_t *footer = get_next_footer(block);
    footer->footer = size | is_allocated;
}
/*
* Checks if current block is the bottom of the heap.
* Returns footer of previous block if exists.
*/
static inline footer_t *get_prev_footer(block_t *block) {
    uint8_t *curr_block = (uint8_t *) block;
    if (curr_block == mem_heap_lo() + (ALIGNMENT - offsetof(block_t, payload))) {
        return NULL;
    }
    uint8_t *prev_footer = curr_block - sizeof(footer_t);
    return (footer_t *) prev_footer;
}

/*
* Checks if current block is the top of the heap.
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
* Checks if current block is the bottom of the heap.
* Returns header of previous block if exists.
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
    /* Pad heap start so first payload is at ALIGNMENT. */

    head_node = NULL;

    if ((long) mem_sbrk(ALIGNMENT - offsetof(block_t, payload)) < 0) {
        return -1;
    }

    return 0;
}

static inline void print_block(block_t *block) {
    printf("BLOCk:%p\n", block);
    printf("Header:%zu\n", block->header);
    printf("PayloadAdd:%p\n", block->payload);
    printf("Footer:%zu\n", get_next_footer(block)->footer);
    printf("FooterAdd:%p\n\n", get_next_footer(block));
}

static void split(block_t *curr_block, size_t requested_size) {
    uint8_t *second_new_block = ((uint8_t *) curr_block) + requested_size;
    set_block((block_t *) second_new_block, get_size(curr_block) - requested_size, false);
    add_to_free((block_t *) second_new_block);
    block_t *first_new_block = curr_block;
    set_block(first_new_block, requested_size, true);

}

static void *search_fit(size_t size){
    size_t block_size = size;
    list_node_t *curr_node = head_node;
    while (curr_node != NULL) {
        size_t curr_size = get_size_node(curr_node);
        if (curr_size >= block_size) {
            block_t *curr_block = (block_t *) ((void *) curr_node);
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
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size) {
    size_t block_size = round_up(size, ALIGNMENT);
    void *first_fit = search_fit(block_size);
    if (first_fit != NULL) {
        return first_fit;
    }

    block_t *block = mem_sbrk(block_size);
    if ((long) block < 0) {
        return NULL;
    }

    set_block(block, block_size, true);

    return block->payload;
}

static void coalesc(block_t *block1, block_t *block2) {
    size_t new_size = get_size(block1) + get_size(block2);
    set_block(block1, new_size, false);
}
/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr) {
    if (ptr != NULL) {
        block_t *curr_block = ptr - offsetof(block_t, payload);
        size_t size = get_size(curr_block);
        set_block(curr_block, size, false);

        footer_t *prev_footer = get_prev_footer(curr_block);
        block_t *next_block = get_next_header(curr_block);

        block_t *free_block = curr_block;
        if (prev_footer && !check_allocated_footer(prev_footer)) {
            block_t *prev_block = get_prev_header(curr_block, prev_footer);
            remove_from_free(prev_block);
            coalesc(prev_block, curr_block);
            free_block = prev_block;
        }
        if (next_block && !check_allocated(next_block)) {
            remove_from_free(next_block);
            coalesc(free_block, next_block);
        }
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

/*
 * mm_checkheap - So simple, it doesn't need a checker!
 */
void mm_checkheap(int verbose) {
    block_t *curr_block = mem_heap_lo() + offsetof(block_t, payload);
    size_t free_counter = 0;
    size_t counter = 0;
    size_t total_free_counter = 0;
    while (curr_block != NULL) {
        if (((uint8_t) curr_block->payload) % 16 != 0) {
            printf("Alignment Off :%i\n", verbose);
            print_block(curr_block);
            printf("%zu\n", counter);
        }
        size_t curr_header = curr_block->header;
        size_t curr_footer = get_next_footer(curr_block)->footer;
        if (curr_header != curr_footer) {
            printf("Header/Footer Don't Match %i\n", verbose);
            print_block((block_t *) curr_block);
            printf("%zu\n", counter);
        }
        if (check_allocated(curr_block) == false) {
            free_counter++;
            total_free_counter++;

            if (free_counter == 2) {
                printf("Two Consecutive Free Blocks %i\n", verbose);
                free_counter = 1;
            }
        } else {
            free_counter = 0;
        }

        curr_block = get_next_header(curr_block);
        counter++;
    }

    size_t other_free_counter = 0;
    list_node_t *curr_node = head_node;
    while (curr_node != NULL) {
        list_node_t *prev_node = curr_node->prev;
        list_node_t *next_node = curr_node->next;
        if (next_node != NULL) {
            if (next_node->prev != curr_node) {
                printf("Prev pointer of next wrong %i\n", verbose);
            }
        }
        if (prev_node != NULL) {
            if (prev_node->next != curr_node) {
                printf("Next pointer of prev wrong %i\n", verbose);
            }
        }
        if ((void *) curr_node <= mem_heap_lo() + 7) {
            printf("Node below bottom of heap %i\n", verbose);
            printf("Node below bottom of heap %p\n", curr_node);
            if ((uint8_t *) curr_node + get_size((block_t *) curr_node) > (uint8_t *) mem_heap_hi() - 1){
                printf("Node above top of heap %i\n", verbose);
                printf("Node above top of heap %p\n", curr_node);
            }
        }
        curr_node = curr_node->next;
        other_free_counter++;
    }

    /*if (total_free_counter != other_free_counter) {
        printf("Free mismatch %i\n", verbose);
        printf("NODE %zu\n", other_free_counter);
        printf("IMPLICIT %zu\n", total_free_counter);
    }*/

}
