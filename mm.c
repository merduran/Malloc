#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "./mm.h"
#include "./memlib.h"
#include "./mminline.h"
#define max(a, b)(a > b? a : b)
#define min(a, b)(a < b? a : b)
block_t* _epilogue;
block_t* _prologue;
size_t _chunksize = 1024;

// rounds up to the nearest multiple of WORD_SIZE
static inline size_t align(size_t size) {
    return (((size) + (WORD_SIZE - 1)) & ~(WORD_SIZE - 1));
}

int mm_check_heap(void);
/*
 * Function takes in a block and coalesces
 * it with its free neighbors, if there are any.
 * 
 * returns: void.
 */
void mm_coalesce(block_t* block){
	block_t* next = block_next(block);
	block_t* prev = block_prev(block);
	pull_free_block(block);		
	// Check if next block is free.
	if (!block_allocated(next)){
		pull_free_block(next);
		block_set_size(block, block_size(block) + block_size(next));
	}
	// Check if previous is free.
	if (!block_allocated(prev)){
		pull_free_block(prev);
		block_set_size(prev, block_size(prev) + block_size(block));
		block = prev;
	}
	// Insert potentially coalesced block back into
	// free list.
	insert_free_block(block);
}
/*
 * Function takes in a block and a size, 
 * and shrinks block to that size. I make sure
 * to check the difference of the original block size and 
 * the new block size is great enough to fit a minimally sized
 * block before whenever I call this function.
 * 
 * returns: void.
 */
void mm_break(block_t* block, size_t size){
	size_t block_size_init = block_size(block);
	pull_free_block(block);
	block_set_size_and_allocated(block, size, 1);
	block_t* new_free_block = block_next(block);
	block_set_size_and_allocated(new_free_block, block_size_init - size, 0);
	insert_free_block(new_free_block);
}
/*
 * Creates a free block of size size
 * which it adds to the end of the heap and moves the epilogue
 * after it.
 * 
 * returns: pointer to the newly inserted block, or -1 upon failure.
 */
block_t* mm_extend_heap(size_t size){
	// Size must be at least zero.
	assert((int) size >= 0);
	if (size < MINBLOCKSIZE){
		size = MINBLOCKSIZE;
	}
	size = align(size);
	block_t* ext;
	// Error checking mem_sbrk.
	if ((ext = (block_t*) mem_sbrk(size)) == (void*) -1){
		perror("error 1:\n");
		return (block_t*) -1;
	}
	// Move ext to epilogue's initial position.
	ext = _epilogue;
	block_set_size_and_allocated(ext, size, 0);
	insert_free_block(ext);
	// Move epilogue to right after ext.
	_epilogue =  block_next(ext);
	block_set_size_and_allocated(_epilogue, TAGS_SIZE, 1);
	return ext;
}
/*
 * initializes the dynamic storage allocator (allocate initial heap space)
 * arguments: none
 * returns: 0, if successful
 *         -1, if an error occurs
 */
int mm_init(void) {
	// Have to reset global variable flist_first every time user initiliazes
	// dynamic storage allocator.
	flist_first = NULL;
	if ((_prologue = (block_t*) mem_sbrk(MINBLOCKSIZE)) == (void*) -1){
		perror("error 2:\n");
		return -1;
	}
	// Initiliaze epilogue and prologue for bounds checking in
	// coalesce and traversing heap in mm_check_heap.
	block_set_size_and_allocated(_prologue, TAGS_SIZE, 1);
	block_set_size_and_allocated((_epilogue = block_next(_prologue)), TAGS_SIZE, 1);
	return 0;
}

/*
 * allocates a block of memory and returns a pointer to that block's payload
 * arguments: size: the desired payload size for the block
 * returns: a pointer to the newly-allocated block's payload (whose size
 *          is a multiple of ALIGNMENT), or NULL if an error occurred
 */
void *mm_malloc(size_t size) {
	// Size cannot be negative.
	if ((int) size < 0){
		return NULL;
	}
	// Strategy to find fit is first-fit.
	block_t* first = flist_first;
	if (size < MINBLOCKSIZE){
		size = MINBLOCKSIZE;
	}
	size = align(size);
	size_t block_size_req = size + TAGS_SIZE;
	block_t* curr = flist_first;
	// To reduce calls to extend heap, I extend heap by the maximum of chunksize (1024)
	// and the requested block size.
	size_t max = max(block_size_req, _chunksize);
	if (curr == NULL){
		// If no free blocks...
		if ((curr = mm_extend_heap(max)) == (void*) -1){
			perror("Extend heap failure\n");
			return NULL;
		}
	} else {
		// Traverses heap till a free, sufficiently-sized block
		// is found.
		while (block_size(curr) < block_size_req){
			curr = block_next_free(curr);
			if (curr == first){
				// None of the free blocks can fit the requested size.
				// Must extend heap.
				if ((curr = mm_extend_heap(max)) == (void*) -1){
					perror("Extend heap failure\n");
					return NULL;
				}
			}
		}
	}
	// If our block's (extended our found from the free list) size
	// is greater than the requested size by minblocksize, we can 
	// add that difference as a free block to the list. However,
	// to avoid fragmentation and therefore unnecessarily frequent 
	// calls to mm_extend_heap, I only break my original block, if its 
	// greater than the requested size by 8 minblocksizes.
	if (block_size(curr) - block_size_req >= 8 * MINBLOCKSIZE){
		mm_break(curr, block_size_req);
	} else {
		// If the difference is not as big as a minimally sized block,
		// just pull the block out of the free list and return it as allocated.
		pull_free_block(curr);
		block_set_allocated(curr, 1);
	}
	return curr->payload;
}
/*                             
 * frees a block of memory, enabling it to be reused later
 * arguments: ptr: pointer to the block's payload
 * returns: nothing
 */
void mm_free(void *ptr) {
	block_t* block = payload_to_block(ptr);
	// Must first be allocated to be freed.
	assert(block_allocated(block));
	block_set_allocated(block, 0);
	insert_free_block(block);
	// Might have free neighbors, in which case must coalesce
	// to avoid fragmentation.
	mm_coalesce(block);
}
/*
 * reallocates a memory block to update it with a new given size
 * arguments: ptr: a pointer to the memory block's payload
 *            size: the desired new block size
 * returns: a pointer to the new memory block's payload, NULL upon failure.
 */
void *mm_realloc(void *ptr, size_t size) {
	if ((int) size < 0){
		return NULL;
	}
	if (ptr == NULL){
		if (!size){
			return NULL;
		}
		// If size is positive and ptr null,
		// must malloc.
		if (mm_malloc(size) == NULL){
			perror("Malloc failure!\n");
			return NULL;
		}
	}
	if (!size){
		// If ptr is not null and size 0,
		// equivalent to freeing block.
		mm_free(ptr);
		return NULL;			
	}
	size = align(size);
	size += TAGS_SIZE;
	block_t* block = payload_to_block(ptr);
	size_t original_size = block_size(block);
	// If requested size is smaller than the size of the block,
	// simply returns a pointer to the block's payload.
	if (original_size >= size){
		return block->payload;
	} else {
		// If requested size is greater than the block's size,
		// first tries to "coalesce" with its neigbor/s to attain sufficient
		// size. First tries the next neighbor.
		size_t cpy_size;
		block_t* next = block_next(block);
		// Might have to copy the block's payload if we move it.
		cpy_size = original_size - TAGS_SIZE;
		if (!block_allocated(next)){
			pull_free_block(next);
			block_set_size_and_allocated(block, block_size(block) + block_size(next), 1);
			original_size = block_size(block);
			if (size <= original_size){
				return block->payload;
			}
		}
		// If here, either did not coalesce with the next block,
		// or could not attain sufficient size after having coalesced with the next block.
		// In either case, must check if we can coalesce with the previous block.
		if (original_size < size){
			block_t* prev = block_prev(block);
			if (!block_allocated(prev)){
				pull_free_block(prev);
				block_set_size_and_allocated(prev, block_size(block) + block_size(prev), 1);
				block = prev;
				original_size = block_size(block);
				if (size <= original_size){
					// Must shift block's cpy_size-bytes data into its new location.					
					memmove(block->payload, ptr, cpy_size);
					return block->payload;
				}
				ptr = block->payload;
			}
		}
		// If here, still could not attain sufficient size. Must malloc as a last resort.
		block_t* payload;
		if ((payload = mm_malloc(size)) == NULL){
			perror("Malloc failure!\n");
			return NULL;
		}
		block_t* new_block = payload_to_block(payload);
		// Having copied its data into the new region, we have effectively moved our original block.
		memcpy(new_block->payload, ptr, cpy_size);
		// Must free the old block to avoid running out of memory.
		mm_free(ptr);
		return new_block->payload;
	}
	//Split if only remaining is a big size, experiment to find this size.
	return block->payload;

}

/*
 * checks the state of the heap for internal consistency and prints informative
 * error messages
 * arguments: none
 * returns: 0, if successful
 *          nonzero, if the heap is not consistent
 */
int mm_check_heap(void) {
	block_t* curr = flist_first;
	if (curr == NULL){
		return 0;
	}
	// Check if flist_first is allocated.
	if (block_allocated(curr)){
		printf("Block address = %p, block size = %d, heap error: %s\n", (void*) curr, (int) block_size(curr), "found an allocated block in the free list!\n");
		exit(1);
	}
	curr = block_next_free(curr);
	while (curr != flist_first){
		// If there are more blocks in the free list, checks if they are allocated.
		if (block_allocated(curr)){
			printf("Block address = %p, block size = %d, heap error: %s\n", (void*) curr, (int) block_size(curr), "found an allocated block in the free list!\n");
			exit(1);
		}
		// Checks if the block's next pointer points to a valid free block.
		if (block_allocated(block_next_free(curr))){
			printf("Block address = %p, block size = %d, heap error: %s\n", (void*) curr, (int) block_size(curr), "next free block is not free!\n");
			exit(1);
		}
		// Checks if the block's previous pointer points to a valid free block.
		if (block_allocated(block_prev_free(curr))){
			printf("Block address = %p, block size = %d, heap error: %s\n", (void*) curr, (int) block_size(curr), "next free block is not free!\n");
			exit(1);
		}
		// The two conditionals below check if there are any free neighbors that have not been coalesced as they should be.		
		if (!block_allocated(block_next(curr))){
			printf("Block address = %p, block size = %d, heap error: %s\n", (void*) curr, (int) block_size(curr), "has not coalesced with next block!\n");
			exit(1);
		}
		if (!block_allocated(block_prev(curr))){
			printf("Block address = %p, block size = %d, heap error: %s\n", (void*) curr, (int) block_size(curr), "has not coalesced with previous block!\n");
			exit(1);
		}
		curr = block_next_free(curr);
	}
	block_t* heap_lo = mem_heap_lo();
	block_t* heap_hi = mem_heap_hi();
	// Checks if the first block in the heap is the prologue.
	if ((curr = heap_lo) != _prologue){
		printf("prologue address = %p, prologue size = %d, heap error: %s\n", (void*) _prologue, (int) block_size(_prologue), "prologue is not the first block in the heap!\n");
		exit(1);
	}
	if ((void*) ((long) heap_hi - (long)(TAGS_SIZE - 1)) != _epilogue){
		printf("epilogue address = %p, epilogue size = %d, heap error: %s\n", (void*) _epilogue, (int) block_size(_epilogue), "epilogue is not the last block in the heap!\n");
		exit(1);
	}
	while (curr != _epilogue){
		// Checks if every block in the heap except the epilogue is in bounds.
		if (curr < heap_lo || curr > heap_hi){
			printf("Block address = %p, block size = %d, heap error: %s\n", (void*) curr, (int) block_size(curr), "block out of heap's bounds!\n");
			exit(1);
		}
		// Checks if headers and footers match for every block.
		if (block_size(curr) != block_end_size(curr) || block_allocated(curr) != block_end_allocated(curr)){
			printf("Block address = %p, block size = %d, heap error: %s\n", (void*) curr, (int) block_size(curr), "header and footer of block do not match!\n");
			exit(1);
		}
		curr = block_next(curr);
	}
	// Checks if epilogue is in bounds.
	if (_epilogue < heap_lo || _epilogue > heap_hi){
			printf("Block address = %p, block size = %d, heap error: %s\n", (void*) curr, (int) block_size(curr), "block out of heap's bounds!\n");
			exit(1);
	}
    return 0;
}
