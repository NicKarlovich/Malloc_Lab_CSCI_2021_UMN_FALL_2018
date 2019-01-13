/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * This is my implementation of mm_malloc.  My implementation uses
 * a segregated free list seperated by powers of two.  Each free list is
 * a linked list sorted in ascending size.
 *
 * Nick Karlovich
 * karlo015
 * Fall 2018 - CSCI 2021
 * Discussion: 12:20pm Tuesday.
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "Ask me about my realloc memory utilization",
    /* First member's full name */
    "Nick Karlovich",
    /* First member's email address */
    "karlo015@umn.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0xf)

#define WSIZE 8
#define DSIZE 16
#define CHUNKSIZE (1<<10)
/*
I decreased the chunksize because it was much faster and more space efficient
then using the default size of (1<<12)
*/
#define OVERHEAD 16

#define MAX(x,y) ((x) > (y) ? (x) : (y))
#define MIN(x,y) ((x) < (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

/* read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* read the size and allocated fields from address p
   GET_SIZE returns size of entire block including header and footer  */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* Given block ptr bp, (not the header the bit after header before data)
        return the pointer that is in the first bit of data, ie when the
        block is free return a pointer */

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
static char *heap_listp;
static void *heap_end;

//number of segregated free lists.
static int num_of_size_class_p = 34;

static char *scp_1;

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
int mm_check(int verbose);
static void add_node(void *root, void *bp);
static void add_node_to_root(size_t size, void *p);
static void remove_node(size_t size, void *hdr);
static size_t get_size_class(size_t b_size);
static void *get_root(size_t size_class);
static void *findFreeNode(size_t size, void *in_stack);
static void printSeglist(size_t class_size);
static void printAllSeglists();

static int DEBUG = 0;
static int DEBUG_INIT = 0;
static int DEBUG_MALLOC = 0;
static int DEBUG_FREE = 0;
static int DEBUG_REALLOC = 0;
static int DEBUG_ADD = 0;
static int DEBUG_ADD_ROOT = 0;
static int DEBUG_REMOVE = 0;
static int DEBUG_FIND = 0;
static int DEBUG_PLACE = 0;
static int DEBUG_EXTEND = 0;
static int DEBUG_FREE_NODE = 0;
static int DEBUG_COALESCE = 0;

/*

        OVERALL HEAP LAYOUT
0,1,2...........................62,63
+----------------------------------+
|           PADDING                |
+----------------------------------+
|      PROLOGUE HEADER     16:1    |
+----------------------------------+   <--- heap_listp
|      PROLOGUE FOOTER     16:1    |
+----------------------------------+
| HDR BLOCK OF FREE LIST PTRS 288:1|
+----------------------------------+   <--- scp_1
|            scp_1                 |
+----------------------------------+
|            scp_2                 |
+----------------------------------+
|              :                   |
|              :                   |
|              :                   |
+----------------------------------+
|            scp_34                |
+----------------------------------+
| FTR BLOCK OF FREE LIST PTRS 288:1|
+----------------------------------+
|              :                   |
|       payload/heap area          |
|              :                   |
+----------------------------------+   <--- heap_end
|       EPILOGUE FOOTER     0:1    |
+----------------------------------+
*/

/*
 * mm_init - initialize prologue and epilogue bits
 * expand the heap to make space for segregated free list pointers
 * set the area for free list pointers to all 0 so they are ready for assignment
 */
int mm_init(void) {
    if((heap_listp = mem_sbrk(4 * WSIZE)) == NULL) {
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(OVERHEAD, 1)); //prologue header
    PUT(heap_listp + DSIZE, PACK(OVERHEAD, 1)); //prologue footer
    PUT(heap_listp + WSIZE + DSIZE, PACK(0,1)); //epilogue header
    heap_listp += DSIZE;
    heap_end = heap_listp + WSIZE + DSIZE;
    scp_1 = heap_listp + DSIZE;

    void *temp = extend_heap(num_of_size_class_p + 2);              //34 WSIZE blocks for pointers and 2, one for each header
    remove_node((num_of_size_class_p + 2) * 8, temp);
    memset(heap_listp + WSIZE  + 1, 0,(2 + num_of_size_class_p) * 8);        //setting the area for pointers to 0 so its clean
    PUT(heap_listp + WSIZE, PACK(((2 + num_of_size_class_p) * 8),1));                                   //start of root index's
    PUT(heap_listp + ((2 + num_of_size_class_p) * 8), PACK( ( (2 + num_of_size_class_p) * 8) , 1 ) );   //end of roots index's

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        printf("extend_heap == null in init:\n");
        return -1;
    } else {
        if(DEBUG || DEBUG_INIT) {
            printf("HEAP EXTENDED\n");
        }
    }
    if(DEBUG || DEBUG_INIT) {
        printf("INIT END HEAP CHECK\n");
        mm_check(1);
    }
    return 0;
}

/*
* This function takes a pointer bp that should be removed
* and it's size.  It then looks through the corresponding size_class
* for bp, once it is found the program keeps track of the node previous
* and sets it's(the previous node's) next pointer to what bp was pointing
* to thus removing bp from the list.  bp still exists but not in the list.
*/
static void remove_node(size_t size, void *bp) {

    void *secNodeAddress;                   /* address of node after bp*/
    size_t size_class = get_size_class(size);
    void *ptr = get_root(size_class);

    if(DEBUG || DEBUG_REMOVE) {
        printf("[R][BEGIN][size:%ld] ",size_class);
        printSeglist(size_class);
        mm_check(1);
    }

    void *prev = ptr;
    while(bp != ptr && ptr != NULL) {
        prev = ptr;
        ptr = GET(ptr);

        //if the node we're looking at is the one we want to remove
        if(ptr == bp){
            secNodeAddress = GET(ptr);
            PUT(prev, secNodeAddress);
            return NULL;  //return null to get out of loop
        }
    }
    if(DEBUG || DEBUG_REMOVE) {
        printf("[R][AFTER] ");
        printSeglist(size_class);
        printf("removed free node of %ld from size class %ld\n",size,size_class);
        mm_check(1);
    }
}

/*
 * Gets the respective size_class for a given size.
 * Each size class is represented by powers of two.  This function
 * divides by 32 at the beginning because 32 is the minimum block size.
 * so size_class 1 is blocks 32 and 48, size_class 2 is 64, 80, 96, 110. etc
 */
static size_t get_size_class(size_t asize) {
    size_t index = 0;
    asize = asize >> 5;
    while(index < num_of_size_class_p - 1 && asize > 1) {
        asize >>= 1;
        index++;
    }
    return index;
}

/*
 * Returns the pointer to free list pointer initially
 * declared in the init() function.  The root pointers are
 * 8 bytes long and placed immediately next to each other so
 * incrementing the pointer by 8 for its size_class gets
 * the correct size_class.
 */
static void *get_root(size_t size_class) {
    return ((void *)((scp_1 + (8 * size_class))));
}

/*
 * this function does the actual insertion of a node
 * into the list.  It takes the prev and bp pointer.  It then
 * does a simple insertion by making bp point to what is next after
 * prev and then prev's next is set to bp;
 */
static void add_node(void *root, void *bp) {
    if(DEBUG || DEBUG_ADD) {
        printf("[A][BEGIN] ");
        printSeglist(get_size_class(GET_SIZE(HDRP(bp))));
        mm_check(1);
    }
    //get what prev is pointing to.
    void *first = GET(root);

    //set bp to point to what prev, used to point to.
    PUT(bp,first);

    //set root to point to bp;
    PUT(root,bp);
    if(DEBUG || DEBUG_ADD) {
        printf("[A][AFTER] ");
        printSeglist(get_size_class(GET_SIZE(HDRP(bp))));
        mm_check(1);
    }
}

/*
 * What the program calls when it creates a free block.  This function
 * then determines which size_class the free block goes into and passes
 * that information onto add_node() which does the computation.
 */
static void add_node_to_root(size_t size, void *bp) {
    void *root = NULL;      /* root variable */
    size_t size_class = get_size_class(size);   /* size class */
    root = get_root(size_class);

    //if root list is empty then insert immediately.
    if(GET(root) == NULL) {
        PUT(root, bp);
    } else {
        void *next = GET(root);         /* pointer to next node */
        void *prev = root;              /* pointer to keep track of node before */
        int found = 0;
        int bp_size = GET_SIZE(HDRP(bp));
        do {
            if(bp_size <= GET_SIZE(HDRP(next))) {
                add_node(prev, bp);
                found = 1;
            } else {
                if(next != NULL) {
                    prev = next;
                }
                next = GET(next);
            }
        } while(next != NULL && found == 0);
        /*
         * if next is null then we've reached the end of the list and we just
         * add it to the end with this extra if() case at the end.
         * the only other way to get out of this loop is to have found == 0
         * which means it found a spot so this edge case wont run.
         */
        if(found == 0) {
            add_node(prev,bp);
        }
    }
    if(DEBUG || DEBUG_ADD_ROOT) {
        printf("added free node of %ld to size class %ld\n",size ,size_class);
        printSeglist(size_class);
        mm_check(1);
    }
}

/*
 * Allocates a block by looking for a block of size in the free lists
 * if it can find one, it will place the block there otherwise it will extend
 * the heap.  It will always allocated a block whose size is a multiple of the
 * alignment (16).
 */
void *mm_malloc(size_t size) {
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;
    if(DEBUG || DEBUG_MALLOC) {
        printf("start of malloc-size: %ld\n", size);
        printAllSeglists();
        mm_check(1);
    }

    /* Ignore weird requests */
    if (size <= 0) {
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {
        asize = DSIZE + OVERHEAD;
    } else {
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    }
    if(DEBUG || DEBUG_MALLOC) {
        printf("malloc called with input size: %ld, and alignedSize: %ld \n",size, asize);
    }

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * Takes a block.  To increase efficiency, it only coalesces if the size is < 200
 * this helps because it is a small impact on space utilization but a huge
 * buff to throughput.
 */
void mm_free(void *ptr) {
    if(DEBUG || DEBUG_FREE) {
        printf("start of free-ptr: %p\n",ptr);
        printAllSeglists();
        mm_check(1);
    }

    if(GET_SIZE(HDRP(ptr)) > 200) {
        ptr = coalesce(ptr);
    }

    /*
    * when we free we set the first 8 bytes to 0, so that its open for later whe
    * we use those first eight bytes as a pointer while it's in the free list.
    */
    PUT(ptr,0);
    int size = GET_SIZE(HDRP(ptr));
    add_node_to_root(size, ptr);


    if(DEBUG || DEBUG_FREE) {
        printf("free done:\n");
        printAllSeglists();
        mm_check(1);
    }
}

/*
 * Takes a pointer and attempts to resize it to the new size in a way
 * that most reduces the need to use memcpy() since it is very expensive.
 */
void *mm_realloc(void *ptr, size_t size) {
    if(DEBUG || DEBUG_REALLOC) {
        printf("start of realloc-ptr:%p, size:%ld\n", ptr, size);
        printAllSeglists();
        mm_check(1);
    }

    //weird input
    if(ptr == NULL) {
        return mm_malloc(size);
    } else if(size == 0) {  // basically just free.
        mm_free(ptr);
        return NULL;
    }
    size_t originalSize = GET_SIZE(HDRP(ptr));
    /*
    * some of these variables are kept as longs so that we can do subtraction
    * on them so that we can make some logic out of it, because size_t, is
    * unsigned and thus can't support negative numbers which I use.
    */
    long ogSize2 = originalSize;  /* because originalSize is changed later */
    void *oldptr = ptr;           /* ptr may get changed so we keep the old for debugging */
    long copySize;                /* the new aligned size of the block */
    long remain;                  /* if copySize > size, it is the difference, meaning how much we overflow */
    size_t extend;                /* if we extend as a result we use this */
    long spaceDifference;         /* the difference between originalSize and copySize */

    //alignment
    if(size < DSIZE) {
        copySize =   2 * DSIZE;
    } else {
        copySize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);
    }

    spaceDifference = ogSize2 - copySize;

    /*
    * if it's 0 that means the difference in change doesn't allow for the remainder
    * to be made into a new block so we basically ignore the request and just return
    * the same pointer.
    */
    if(spaceDifference == 0) {
        return ptr;

    /* if copySize > originalSize so we might need to memcpy */
    } else if(spaceDifference < DSIZE + OVERHEAD) {

        long nextBlockSize = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        void *nextBlockPointer = NEXT_BLKP(ptr);

        /*
        * the size of the block we have and the next one minus what we want
        * if its positive then we can fit our current block into next
        * if its negative then we need to find another solution
        */
        remain = ogSize2 + nextBlockSize - copySize;

        //if the next block is free
        if(GET_ALLOC(HDRP(nextBlockPointer)) == 0) {

            //if there is space
            if(remain >= DSIZE + OVERHEAD) {
                //remove the nextblock from free because we'll be using it.
                remove_node(nextBlockSize,findFreeNode(nextBlockSize,nextBlockPointer));
                //put in new size
                PUT(HDRP(ptr), PACK(copySize,1));
                PUT(FTRP(ptr), PACK(copySize,1));
                ptr = NEXT_BLKP(ptr);
                originalSize = originalSize + nextBlockSize;
                //basically just the remainder of area left in the free block we "stole"
                PUT(HDRP(ptr), PACK(originalSize - copySize,0));
                PUT(FTRP(ptr), PACK(originalSize - copySize,0));
                //cleaning up free block
                PUT(ptr,0);

                //re-adding that free block to the segregated free list.
                add_node_to_root((originalSize - copySize), ptr);
                if(DEBUG || DEBUG_REALLOC) {
                    printf("start of realloc-ptr:%p, size:%ld\n", ptr, size);
                    printAllSeglists();
                    mm_check(1);
                }
                return PREV_BLKP(ptr);
            }
        }

        //if the next block is the end of the heap we can just extend it.
        if(GET_SIZE(HDRP(NEXT_BLKP(ptr))) == 0) {

            void *after_extend;      /* pointer to new extended area */
            extend = MAX(((-remain/WSIZE)), CHUNKSIZE);

            if((after_extend = extend_heap(extend/WSIZE)) == NULL) {
                return NULL;
            }
            //remove after_extend from free list because we'll be using it.
            remove_node((extend), after_extend);

            /*
            * we need to re-update the nextBlockSize/Ponter because they
            * currently point to the epilogue block but now we have space
            */
            nextBlockSize = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
            nextBlockPointer = NEXT_BLKP(ptr);
            PUT(HDRP(ptr), PACK(copySize, 1));
            PUT(FTRP(ptr), PACK(copySize, 1));

            /*
            * earlier we chose between remain and chunk size, if we chose
            * remain then the extended area will be the perfect size, otherwise
            * the extended size may be bigger than we need so we need to add that
            * remainder of CHUNKSIZE - remain, and add it to the free list.
            */
            if(extend == CHUNKSIZE){
                originalSize = originalSize + (CHUNKSIZE) - copySize;
                nextBlockPointer = NEXT_BLKP(ptr);
                PUT(HDRP(nextBlockPointer), PACK(originalSize, 0));
                PUT(FTRP(nextBlockPointer), PACK(originalSize, 0));
                PUT(nextBlockPointer,0);
                add_node_to_root(originalSize,nextBlockPointer);
            }
            if(DEBUG || DEBUG_REALLOC) {
                printf("start of realloc-ptr:%p, size:%ld\n", ptr, size);
                printAllSeglists();
                mm_check(1);
            }
            return ptr;
        }

        /* we couldn't find a cheeky way to avoid it so we memcpy() */
        oldptr = mm_malloc(copySize - DSIZE);
        memcpy(oldptr, ptr, MIN(size, copySize));
        mm_free(ptr);
        if(DEBUG || DEBUG_REALLOC) {
            printf("start of realloc-ptr:%p, size:%ld\n", ptr, size);
            printAllSeglists();
            mm_check(1);
        }
        return oldptr;
    /*
    * if copySize < originalSize with atleast 4 blocks to spare so
    * we can make another free block.
    */
    } else {

        remove_node(originalSize, ptr);
        PUT(HDRP(ptr), PACK(copySize,1));
        PUT(FTRP(ptr), PACK(copySize,1));
        ptr = NEXT_BLKP(ptr);
        originalSize = originalSize - spaceDifference;
        PUT(HDRP(ptr), PACK(originalSize, 0));
        PUT(FTRP(ptr), PACK(originalSize, 0));
        mm_free(ptr);
        if(DEBUG || DEBUG_REALLOC) {
            printf("start of realloc-ptr:%p, size:%ld\n", ptr, size);
            printAllSeglists();
            mm_check(1);
        }
        return PREV_BLKP(ptr);
    }
}

/*
 * Prints out heap and checks for prologue and epilogue header
 * consistency.  It also checks each block in the heap to make sure
 * it has a the correct header and pointer.
 *
 * I've also included my own functions, printSeglist and printAllSeglists
 * which I used in debugging but I didn't put them inside mm_check() because
 * it was just easier to comment them in and out where needed instead of
 * messing with mm_check().
 *
 * NOTE: this mm_checK() is heavily based off mm_implicit's mm_check, with a few
 * small modifications.
 *
 */
 int mm_check(int verbose) {
    char *bp = heap_listp;
    if(verbose) {
        printf("Heap (%p):\n", heap_listp);
    }
    if((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
        printf("%d + %d\n",(int)(GET_SIZE(HDRP(heap_listp))), DSIZE);
        printf("%d\n",(int)(GET_ALLOC(HDRP(heap_listp))));
        printf("Bad prologue header\n");
    }
    checkblock(heap_listp);

    //for each block in the heap, check it is consistent.
    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if(verbose) {
            printblock(bp);
        }
        checkblock(bp);
    }
    if(verbose) {
        printblock(bp);
    }
    if((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("Bad epilogue header\n");
        printf("%ld ",GET_SIZE(HDRP(bp)));
        printf(" %ld \n", GET_ALLOC(HDRP(bp)));
    }
    return 1;
 }

/*
 * This function extends the heap by words by incrementing mem_sbrk,
 * which is different from many others, where others take size in bytes,
 * which is important to notice.
 */
static void *extend_heap(size_t words) {
    if(DEBUG || DEBUG_EXTEND) {
        printf("start extend-size(in words): %ld\n", words);
        mm_check(1);
    }
    char *bp;
    size_t size;
    //align size to even amount.
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if((bp = mem_sbrk(size)) == (void *)-1) {
        if(DEBUG || DEBUG_EXTEND) {
            printf("extend_heap failed\n");
        }
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));
    heap_end = NEXT_BLKP(bp);

    /*
     * if the block at the end of the heap is free we can coalesce it
     * right alway using a mini coalesce function.
     */
    if(!GET_ALLOC(FTRP(PREV_BLKP(bp)))) {
        remove_node(GET_SIZE(HDRP(PREV_BLKP(bp))), PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    add_node_to_root(size,bp);
    PUT(bp,0);
    if(DEBUG || DEBUG_EXTEND) {
        printf("end extend-size(in words): %ld\n", words);
        mm_check(1);
    }
    return bp;
}

/*
 * This function takes a size of a block that needs to be Allocated
 * and a block that has atleast that much size and this function
 * creates the allocated block and a remainder if it exists, and takes care
 * of the remainder if necessary.
 */
static void place(void *bp, size_t asize) {
    if(DEBUG || DEBUG_PLACE) {
        printf("start of place-bp: %p, size: %ld\n", bp, asize);
        printAllSeglists();
        mm_check(1);
    }
    long csize = GET_SIZE(HDRP(bp));   /* the size of the block found */
    long change_size = csize - asize;  /* the size difference between whats found and whats needed */
    /*
    if the size of the block found is say 72 but asize only needs 32
    then 72-32 = 40 >= DSIZE + OVERHEAD thus it will set the remaining tail
    40 blocks to open memory.

    If say bp was only 40 then 40-32 would still be greater than 0 but not the
    32 required to make a block.  it isn't even worth it to free the
    remaining 8 Words because it couldn't fit a header, footer and some data inside so
    if a function tried to look for it it could find a block of 8 but nothing could fit
    inside so instead its left as leftover garbage.  This is a place of failure for
    stack utilization
    */
    /* if there is enough for a remainder to be made */
    if((change_size) >= (DSIZE + OVERHEAD)) {

        remove_node(csize, bp);
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK((change_size), 0));
        PUT(FTRP(bp), PACK((change_size), 0));

        //this is to open up first 8 bytes so that free block points to null
        PUT(bp,0);
        add_node_to_root(change_size, bp);
    } else { /* the entire block will be allocated, and no free will be left over */
        remove_node(csize, bp);
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    if(DEBUG || DEBUG_PLACE) {
        printf("end of place-bp: %p, size: %ld\n", bp, asize);
        printAllSeglists();
        mm_check(1);
    }
}

/*
 * find a block in the entire segregated free list and return a pointer
 * to such free block if it exists, and NULL if nothing was found
 */
static void *find_fit(size_t asize) {
    if(DEBUG || DEBUG_FIND) {
        printf("beginning of find_fit-size: %ld\n", asize);
        printAllSeglists();
    }

    /*Segregated Class List */
    void *p;
    size_t size_class = get_size_class(asize);
    p = get_root(size_class);
    /*
    * iterates through each size_class starting at the size class
    * of asize and then going to increasingly larger ones.
    */
    for(; size_class < num_of_size_class_p;) {

        if(GET(p) != NULL) {//if root is not empty
            do {
                //gets the pointer to the next node in list, as long as its not null.
                p = GET(p);
            } while(GET(p) != NULL && (asize > GET_SIZE(HDRP(p))));

            if(GET_SIZE(HDRP(p)) >= asize) {
                return p;
            }
        }
        size_class++;
        p = (void*)(get_root(size_class));
    }

    //if there is no list with a size big enough for the block
    if(size_class >= num_of_size_class_p) {
        if(DEBUG || DEBUG_FIND) {
            printf("ending of find_fit-size: %ld\n", asize);
            printAllSeglists();
            printf("reached end of find_fit without finding a block of\n");
            printf("of appropriate size in the segregated free list so it is now\n");
            printf("returning null\n");
        }
        return NULL;
    } else {
        //should not get here but just in case
        if(DEBUG || DEBUG_FIND) {
            printf("end of find_fit-size: %ld\n", asize);
            printAllSeglists();
            printf("Should not have gotten here in find_fit");
        }
            return NULL;
    }
}

/*
 * Helper function to print a given segregated list
*/
static void printSeglist(size_t class_size) {

    void *root = get_root(class_size);
    int c = 0;
    printf("----%ld---\n",class_size);
    while(root != NULL) {
        printf("Block-%ld: %p\n",c , root);
        printf("Var: %p\n",(void *)(GET(root)));
        if(c != 0) {
            printf("Size: %ld\n",GET_SIZE(HDRP(root)));
        }
        root = GET(root);
        c++;
    }
    printf("-------\n");
}

/*
 * Helper function that prints all segregated lists
 */
static void printAllSeglists() {
    for(int i = 0; i < num_of_size_class_p; i++) {
        printSeglist(i);
    }
}

/*
 * A function for mm_realloc, since mm_realloc requires us
 * to find a free block inside a free list based off a pointer,
 * this funciton is very similar to find_fit but this searches based on
 * comparing addresses rather than size, because that doesn't work when
 * we're searching for a specific block in the heap.
 */
static void *findFreeNode(size_t size, void *in_stack){
    if(DEBUG || DEBUG_FREE_NODE) {
        printf("beginning of find_free_node-size: %ld, in_stack: %p\n", size, in_stack);
        printAllSeglists();
    }
    size_t look = get_size_class(size);
    void *p = get_root(look);
    size_t stack_size = GET_SIZE(HDRP(in_stack));
    for(; look < num_of_size_class_p;) {
        while(GET(p) != NULL && (stack_size >= GET_SIZE(HDRP(GET(p))))) {
            if(p == in_stack) {
                if(DEBUG || DEBUG_FREE_NODE) {
                    printf("end of find_free_node-size: %ld, in_stack: %p\n", size, in_stack);
                    printAllSeglists();
                }
                return p;
            }
            p = GET(p);
        }
        if(p == in_stack) {
            if(DEBUG || DEBUG_FREE_NODE) {
                printf("end of find_free_node-size: %ld, in_stack: %p\n", size, in_stack);
                printAllSeglists();
            }
            return p;
        }
        look++;
        p = get_root(look);
    }
    if(DEBUG || DEBUG_FREE_NODE) {
        printf("end of find_free_node-size: %ld, in_stack: %p\n", size, in_stack);
        printAllSeglists();
        printf("Couldnt' find a free node in free lists, uh oh\n");
    }
    return NULL;
}

/*
 * Takes a pointer to a block and checks if surrounding blocks
 * are also free, if so it will combine those blocks and add the
 * new block size to the free list.
 */
static void *coalesce(void *bp) {
    if(DEBUG || DEBUG_COALESCE) {
        printf("start of coalesce-bp: %p\n", bp);
        mm_check(1);
        printAllSeglists();
    }
    //constants
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    /*
     * this base_alloc is useful because it allows us to not have to
     * re-remove the block from the free list and have it fail, thus wasting
     * time.  Example: if block is allocated, then we know its already off
     * the free list so we don't have to remove it, thus we can save a
     * remove_node() call which would waste resources.
     */
    size_t base_alloc = GET_ALLOC(HDRP(bp));
    size_t size = GET_SIZE(HDRP(bp));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));

    if(prev_alloc && next_alloc) { //if both next and previous are allocated
    	PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if(prev_alloc && !next_alloc) { // if next is free
        if(!base_alloc) {
            remove_node(size,bp);
        }
        remove_node(next_size,NEXT_BLKP(bp));
        size += next_size;
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if(!prev_alloc && next_alloc) { //if previous is free
        remove_node(prev_size,PREV_BLKP(bp));
        if(!base_alloc) {
            remove_node(size,bp);
        }
        size += prev_size;
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else { // if both previous and next are both free
        remove_node(next_size,NEXT_BLKP(bp));
        remove_node(prev_size,PREV_BLKP(bp));
        if(!base_alloc) {
            remove_node(size,bp);
        }
        size += next_size + prev_size;
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

    }

    if(DEBUG || DEBUG_COALESCE) {
        printf("end of coalesce\n");
        mm_check(1);
        printAllSeglists();
    }
    return bp;
}

/*
 * Helper fucntion taken from mm_implicit that prints out block data
 */
static void printblock(void *bp) {

    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if(hsize == 0) {
        printf("%p: EOL\n\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, hsize,
        (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}

/*
 * Helper function that checks to make sure a given block has the correct
 * alignent and header/footer data.
 *
 * taken from mm_implicit
 */
static void checkblock(void *bp) {
    if((size_t)bp % DSIZE) {
        printf("Erorr: %p is not doubleword aligned \n", bp);
    }
    if(GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("Error: header does not match footer!\n");
    }
}
