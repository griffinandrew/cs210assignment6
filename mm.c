/*
This approach maximizes the utliity and throughput of a implicit list memory allocation structure. A block has a payload as well as a header and footer to designate size and allocation status
A block is allocated by first traversing the list using the best fit technique then changing the allocation status of the header and footer tags. 
If a fit is found the heap is extended to the appropraite size and the allocation tags are adjusted.
This implementation utlizes a coalesce function that is used to ensure that no free blocks are adjacent to eachother minimizing the wasted space.
In realloc blocks can be resized and reused according to the requested size and what category that size request follows into. This way a new block is not created each time but rather reused, only calling a new block if completely necessary
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
    /* bu username : eg. jappavoo */
    "gheyrich",
    /* full name : eg. jonathan appavoo */
    "Griffin Heyrich",
    /* email address : jappavoo@bu.edu */
    "gheyrich@bu.edu",
    "",
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */ 
#define	WSIZE	4 /* Word and header/footer size (bytes) */ 
#define DSIZE	8 /* Double word size (bytes) */ 
#define CHUNKSIZE (1<<2) /* Extend heap by this amount (bytes) */ //6 with best gives 56 gives higher score //8 with best gives 57
//changing chunk size increases utility

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */ 
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */ 
#define GET(p)		(*(unsigned int *) (p)) 
#define PUT(p, val)	(*(unsigned int *) (p) = (val))

/* Read the size and allocated fields from address p */ 
#define GET_SIZE(p)	(GET (p) & ~0x7) 
#define GET_ALLOC(p)	(GET (p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */ 
#define HDRP(bp)	((char *) (bp) - WSIZE) 
#define FTRP(bp)	((char *) (bp) + GET_SIZE (HDRP (bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */ 
#define NEXT_BLKP(bp)	((char *) (bp) + GET_SIZE(((char *) (bp) - WSIZE))) 
#define PREV_BLKP(bp)	((char *) (bp) - GET_SIZE(((char *) (bp) - DSIZE)))

void *heap_listp;

int mm_init(void);
static void *extend_heap(size_t words);
void mm_free(void *bp);
static void *coalesce(void *bp);
void *mm_malloc(size_t size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
int mm_check(void);
int check_blk(void *bp);
void show_block(void *bp);
int heap_check(void *bp);


//the role of this function is to intialize the heap
//first the function creeates an a block of given size then sets the attributes accordingly
//here a block of d size is intialized and allocated
int mm_init(void)
{
	/* Create the initial empty heap */ 
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return -1; 
	PUT(heap_listp, 0);				/* Alignment padding */ 
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));	/* Prologue header */ 
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));	/* Prologue footer */ 
	PUT(heap_listp + (3*WSIZE), PACK(0, 1));	/* Epilogue header */ 
	heap_listp += (2*WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes */ 
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1; 
	return 0;
}


//this function is used to extend the heap with an additional free block 
//it first ensures that the size is aligned properly then intializes a free block of that size
//if the previous block is also free these blocks will need to be coalesced
static void *extend_heap(size_t words)
{
	char *bp; 
	size_t size;

	/* Allocate an even number of words to maintain alignment */ 
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
	if ((long) (bp = mem_sbrk(size)) == -1)
		return NULL;

	/* Initialize free block header/footer and the epilogue header */ 
	PUT(HDRP (bp), PACK(size, 0));			/* Free block header */ 
	PUT(FTRP (bp), PACK(size, 0));			/* Free block footer */ 
	PUT(HDRP (NEXT_BLKP(bp)), PACK(0, 1));		/* New epilogue header */

	/* Coalesce if the previous block was free */ 
	return coalesce(bp);
}

//this function simply frees an allocated block from the heap and coalesces it if that is appropriate
void mm_free(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp)); //get size of current pointer

	PUT(HDRP(bp), PACK(size, 0)); //set allocation of header and footer to 0 to free it
	PUT(FTRP(bp), PACK(size, 0)); 
	coalesce(bp); //coalesce the newly freed block
}


//this function is used to ensure that no adjacent blocks are free there are 4 cases as seen below 
//if appropraite the new size of the coalsesced block is calcuated, formed and returned to with the proper pointer
static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
	size_t size = GET_SIZE(HDRP(bp));

	if(prev_alloc && next_alloc) {			/* Case 1 */ //if they are both allocated no coalescing to be done
		return bp;
	}

	else if (prev_alloc && !next_alloc) {		/* Case 2 */ //if prev is allocated but next is free expand block to take up next space
		size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
		PUT(HDRP(bp), PACK(size, 0)); 
		PUT(FTRP(bp), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc) {		/* Case 3 */ //if prev is not allocated but next is expand block to take up prev space
		size += GET_SIZE(HDRP(PREV_BLKP(bp))); 
		PUT(FTRP(bp), PACK(size, 0)); 
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
		bp = PREV_BLKP(bp);
	}

	else {						/* Case 4 */ 
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); //if both are not allocated expand free block to occupy both spots
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp); 
	} 
	return bp;
}

//this fucntion is used to intially allocate space for a block of said size
//it ensures the size is proper and aligned, finds an approate size free block for the request if found places that block as allocated 
//if not found a new free block must be created, then place the request on that block
void *mm_malloc(size_t size)
{
	size_t asize;		/* Adjusted block size */ 
	size_t extendsize;	/* Amount to extend heap if no fit */ 
	char *bp;

	//mm_check();

	/* Ignore spurious requests */ 
	if(size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */ 
	if(size <= DSIZE)
		asize = 2*DSIZE; 
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

	/* Search the free list for a fit */ 
	if((bp = find_fit(asize)) != NULL) {
		place (bp, asize); 
		return bp;
	}

	/* No fit found. Get more memory and place the block */ 
	extendsize = MAX(asize, CHUNKSIZE); 
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL; 
	place (bp, asize);
	
//	if (mm_check() != 0){ //check 
//		printf("ERROR\n");
//	}
	return bp;
}


//the role of this function is to get an appropraite size block tht can be allocated
//the function returns that block if it can be or returns null if no fit was found
static void *find_fit(size_t asize){ 
void *bp;
for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this is firsts fit, traverse blocks in the list until a free block that fits the size requirement is found
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp; //return non-allocated block with proper size
        }
    }
    return NULL; //not fit 
}
/*
void *bp;
int counter;
void *next_in_heap = heap_listp +count;
for (bp = next_in_heap; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this is next
	counter++;
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ //this implementation of next is incomplete I could not figure out how to do it witho
			next_in_heap = heap_listp + counter;
            return bp;
        }
    }
	return NULL;
}
*/
/*
void *bp;
void *worst = NULL;
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this is worst fit 
		if(!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp))) >= asize){
			if(worst == NULL){
				worst = bp; 
				//if(asize == GET_SIZE(HDRP(best))){
				//	return best;
				//}
			}
			if((worst != NULL) && (GET_SIZE(HDRP(bp))) < GET_SIZE(HDRP(worst))){
				worst = bp;
				//if(asize == GET_SIZE(HDRP(best))){
				//	return best;
				//}
			}

		}
	}
	if(worst!=NULL){
		return worst;
	}
	return NULL;
}
*/
/*
    void *bp;
	void *best = NULL;
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this is best fit 
		if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
			if(best == NULL){
				best = bp;
				if(asize == GET_SIZE(HDRP(best))){
					return best;
				}
			}
			if((best != NULL) && (GET_SIZE(HDRP(bp))) > GET_SIZE(HDRP(best))){
				best = bp;
				if(asize == GET_SIZE(HDRP(best))){
					return best;
				}
			}

		}
	}
	if(best!=NULL){
		return best;
	}
return NULL;
}

*/
    /*for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this is firsts fit
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL; //not fit 
	*/


//this function has 2 different cases one for when the request is larger then the intialized block size 
//the space must be split it places the correct size block as allocated and the rest as not
//if splitting is not required the block is just allocated 
static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)){ //if difference in size of block vs requested size is greater than or equal to min size split
        PUT(HDRP(bp), PACK(asize, 1)); //allocate requested size block / header and footer
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0)); //the leftover space is then freed
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }

    else{
        PUT(HDRP(bp),PACK(csize, 1)); //otherwise just place the size of the block given in the header
        PUT(FTRP(bp),PACK(csize, 1));
    }
}

//this function resizes the block to a given size
//there are three basic cases relating to the size when we call realloc
	//1. If new < old -> shrink it
	//2. If new > old and next block is free and old + next >= new, expand it
	//3. If new > old and next block is free but old + next < new, or next block is not free -> malloc another block, copy the content to the new block, free the current block
//each of these is dealt with appropraitely based on what the size asked for is, either shrinking, expanding or allocating another if necessary
//shirnking is commented out due to shrinking the block not being able to maintain the payload which resulted in error
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
	size_t old_size; //size is payload and header and footer
	size_t aligned_size, next_size;
    

	if(ptr == NULL){
		return mm_malloc(size); //if no location of block to be reallocated is given just allocate space for it
	}

	if(size == 0){ //if size asked for is 0 just free that space and return null
		mm_free(ptr);
		return NULL;
	}
	
	old_size = GET_SIZE(HDRP(oldptr)); //get size of block and surroundings to be used for the cases of realloc
	next_size = GET_SIZE(HDRP(NEXT_BLKP(oldptr))); //gets size of the next block

	aligned_size = ALIGN(size+DSIZE);

	if(aligned_size == old_size){ //if the aligned size of the request is equal to the old size same block is used just return
		return ptr;
	}

	if(aligned_size < old_size){ //case 1 new is less than old and must be shrunk
		/*
		if(old_size - aligned_size < 4*WSIZE){ //if size is less then min size
			return oldptr;
		}
		else {
		PUT(HDRP(oldptr), PACK(aligned_size,1)); //shrinking the size results in not preserving the data that is why this is commented out didn't want to delete so you saw I knew what to do
		PUT(FTRP(oldptr), PACK(aligned_size,1));
		old_size = GET_SIZE(HDRP(oldptr));
		asize = old_size - aligned_size;
		PUT(HDRP(NEXT_BLKP(oldptr)), PACK(asize, 0));
		PUT(FTRP(NEXT_BLKP(oldptr)), PACK(asize, 0));
		mm_free(NEXT_BLKP(oldptr)); //wait im freeing before coalescing
		}
		*/
		return oldptr;
	}
	
	else{
		old_size = GET_SIZE(HDRP(oldptr));
		next_size = GET_SIZE(HDRP(NEXT_BLKP(oldptr)));

		if( ((GET_ALLOC(HDRP(NEXT_BLKP(oldptr)))) == 0) 
		&& (old_size + next_size >= aligned_size) ){ //case 2 new is greater than old, next block is free and next and oldsize are greater than or equal to the aligned size requested
			PUT(HDRP(oldptr), PACK(old_size + next_size,1)); //expand the block using the free space from next
			PUT(FTRP(oldptr), PACK(old_size + next_size,1));
			return oldptr;
		}

		else{ //case 3 new is greater than old, next is free and old + next is less than aligned size or the next block is allocated
			newptr = mm_malloc(size);  //allocate memory for the block, then check to make sure malloc did not fail
			if (newptr == NULL) 
      			return NULL;
			old_size = GET_SIZE(HDRP(ptr)) - DSIZE; //get the size of payload, thus subtract header and footer size
			if(size < old_size) 
			{
				old_size = size;
			}
			memcpy(newptr, oldptr, old_size); //copy payload into newly allocated block
			mm_free(oldptr); //free old
    		return newptr;
			}
		}
}



//the role of this function is to check both the heap and the block for any errors
//it traveres through the heap, calls a check to block and heap for each interation and returns error message and visual of error
int mm_check(void){
	void *bp;
	for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
		if (check_blk(bp) != 0){ //calls check_blk and sees if that returns an error if so error message is displayed so is that block with error
			printf("error in block\n");
			show_block(bp);
			return -1;
		}
		if(heap_check(bp) != 0){ //calls heap_check and sees if that returns an error if so error message is displayed
			printf("error in heap\n");
			return -1;
		}
	}
	return 0; //no errors return 0
}


//this function makes sure there is no error in the block itself including allocation status, size differences, or an alignment error
//it retrurn -1 and a appropraite error message for each
int check_blk(void *bp){

	if((int)bp % DSIZE){ //ensure block alignment 
		printf("error block not aligned\n");
		return -1;
	}
	if(GET(FTRP(bp)) != GET(HDRP(bp))){ //ensure header and footer are matching
		printf("error header and footer do not match\n");
		return -1;
	}
	if (GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))){ //ensure that header and footer have matching allocation status
		printf("error header and footer alloc status is different\n");
		return -1;
	}
	if(GET_SIZE(HDRP(bp)) % ALIGNMENT){ //check header alignement 
		printf("error header not aligned\n");
		return -1;
	}
	if(GET_SIZE(FTRP(bp)) % ALIGNMENT){ //check footer alignement 
		printf("error footer not aligned\n");
		return -1;
	}
	if((GET_ALLOC(HDRP(bp)) == 1) && (GET_SIZE(HDRP(bp)) < DSIZE)) { //check min size alignment
		printf("error block is smaller than minimun size allocation\n");
		return -1; 
	}
	return 0;
}

//this function is used by check when a block error occurs to show the contents of the block
void show_block(void *bp){
	printf("header = %u\n", GET_SIZE(HDRP(bp))); //show header and footer of block
	printf("footer = %u\n", GET_SIZE(FTRP(bp)));
	printf("header aloocated = %u\n", GET_ALLOC(HDRP(bp))); //show allocation status of block
	printf("footer allocated = %u\n", GET_ALLOC(FTRP(bp)));
}

//this function is used by check to check different aspects of the heap such as 2 uncoalesced blocks next to eachother and if they are out of bounds
//it returns a appropraite error message and -1 if an error has occurred here
int heap_check(void *bp){
	if(GET_ALLOC(HDRP(bp)) == 0 && GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0){ //ensure that current block and next is not free
		printf("Error uncoalesced blocks current and next %p, %p \n", HDRP(bp), HDRP((NEXT_BLKP(bp))));
		return -1;
	}
	if(GET_ALLOC(HDRP(bp)) == 0 && GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0){ //ensure that no current block and prev is not free
		printf("Error uncoalesced blocks current and prev %p, %p \n", HDRP(bp), HDRP((PREV_BLKP(bp))));
		return -1;
	}
	if(HDRP(bp) > (char*)mem_heap_hi() || FTRP(bp) < (char*)mem_heap_lo()){ //make sure that blocks are in the heap
		printf("Error pointer is out of bounds %p, %p\n", HDRP(bp), FTRP(bp));
		printf("should be in range %p, %p\n",mem_heap_hi, mem_heap_lo);
		return -1;
	}
	return 0;
}