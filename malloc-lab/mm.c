/* mm-naive.c - 가장 빠르지만, 메모리는 가장 낭비하는 malloc
 * 이 단순한 방식에서 블록을 할당할 때 그냥 힙 끝(brk 포인터)을 늘리기만 한다.
 * 블록은 순수하게 데이터만 있고, 헤더나 푸터가 없다. 
 * 블록은 합쳐지거나 재사용되지 않는다.
 * realloc은 mm_malloc과 mm_free를 이용해 만들었다.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * 다른 무엇보다 먼저, 아래 구조체에 팀 정보를 적어라.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* 배치 정책: 1 = first fit, 2 = next fit, 3 = best fit */
#define FIT_POLICY 1

/* rover 업데이트 방식을 고르는 스위치 */
/* 0 = 찾은 블록, 1 = 다음 블록 */
#define ROVER_NEXT 0

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN_BLOCK (3*DSIZE)

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*((char **)(bp) + 1))

#define LIST_NUM 1

static char *heap_listp;
static char *rover;
static char **free_lists;

#if FIT_POLICY == 2
    static void fix_rover(char *bp);
#endif

static void *extend_heap(size_t words);

static void *coalesce(void *bp);

static void *find_fit(size_t asize);
static void *first_fit(size_t asize);
static void *next_fit(size_t asize);
static void *best_fit(size_t asize);

static void place(void *bp, size_t asize);

static void mark_alloc(void *bp, size_t size);
static void mark_free(void *bp, size_t size);

static size_t adjust_size(size_t size);

static int get_class(size_t size);
static void insert_free(void *bp);
static void remove_free(void *bp);

/*
 * mm_init - malloc 패키지를 초기화한다. 아무것도 안 하고 0(성공)만 반환
 */
int mm_init(void)
{
    char *start = mem_sbrk(LIST_NUM*DSIZE + 4*WSIZE);

    if (start == (void *)-1) return -1;

    free_lists = (char **)start;

    for (int i = 0; i < LIST_NUM; i++)
    {
        free_lists[i] = NULL;
    }

    heap_listp = start + LIST_NUM*DSIZE;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

    heap_listp += (2 * WSIZE);
    #if FIT_POLICY == 2
        rover = heap_listp + DSIZE;
    #endif

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;

    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;  // 조정한 블록 크기
    size_t extendsize;  // 맞는 블록이 없을 때 힙을 늘릴 크기
    char *bp;
    
    if (size == 0) return NULL;

    asize = adjust_size(size);

    // 안쪽 괄호를 빼면 != 가 = 보다 먼저 계산돼서 bp에 0이나 1이 들어간다.
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;

    place(bp, asize);

    return bp;
}

/*
 * mm_free - 해제는 아무것도 하지 않는다
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    mark_free(bp, size);
    coalesce(bp);
}

/*
 * mm_realloc - mm_malloc과 mm_free를 이용해 간단하게 구현했다.
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldbp = bp;
    void *newbp;
    size_t copySize;
    size_t asize;

    // 유효성 검사

    if (oldbp == NULL) return mm_malloc(size);

    if (size == 0)
    {
        mm_free(oldbp);
        return NULL;
    }

    // asize 계산
    asize = adjust_size(size);
    
    // 제자리 확장 로직 시작
    if (asize <= GET_SIZE(HDRP(oldbp)))
    {
        return oldbp;
    }
    else if (GET_ALLOC(HDRP(NEXT_BLKP(oldbp))) == 0 && GET_SIZE(HDRP(oldbp)) + GET_SIZE(HDRP(NEXT_BLKP(oldbp))) >= asize)
    {
        size_t new_size = GET_SIZE(HDRP(oldbp)) + GET_SIZE(HDRP(NEXT_BLKP(oldbp)));
        remove_free(NEXT_BLKP(oldbp));
        mark_alloc(oldbp, new_size);

        #if FIT_POLICY == 2
            fix_rover(oldbp);
        #endif    

        return oldbp;
    }
    else if (GET_SIZE(HDRP(NEXT_BLKP(oldbp))) == 0)
    {
        if (extend_heap((asize - GET_SIZE(HDRP(oldbp))) / WSIZE) != NULL)
        {
            size_t new_size = GET_SIZE(HDRP(oldbp)) + GET_SIZE(HDRP(NEXT_BLKP(oldbp)));
            remove_free(NEXT_BLKP(oldbp));
            mark_alloc(oldbp, new_size);

            #if FIT_POLICY == 2
                fix_rover(oldbp);
            #endif 

            return oldbp;
        }
    }

    // 이사 후 확장 로직 시작 
    // 새 블록을 받았나?
    newbp = mm_malloc(size);
    if (newbp == NULL) return NULL;

    copySize = GET_SIZE(HDRP(oldbp)) - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newbp, oldbp, copySize);
    mm_free(oldbp);
    return newbp;
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 앞의 블록 할당 비트 저장
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 뒤의 블록 할당 비트 저장
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록 크기 저장

    if (prev_alloc && next_alloc)
    {
        
    }

    else if (prev_alloc && !next_alloc) {
        remove_free(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        mark_free(bp, size);
    }

    else if (!prev_alloc && next_alloc) {
        remove_free(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        mark_free(bp, size);
    }

    else {
        remove_free(PREV_BLKP(bp));
        remove_free(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
                
        bp = PREV_BLKP(bp);
        mark_free(bp, size);
    }

    #if FIT_POLICY == 2
        fix_rover(bp);
    #endif

    insert_free(bp);

    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if((long)(bp = mem_sbrk(size)) == -1) return NULL;

    mark_free(bp, size);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *find_fit(size_t asize)
{
    #if FIT_POLICY == 1
        return first_fit(asize);
    #elif FIT_POLICY == 2
        return next_fit(asize);
    #else
        return best_fit(asize);
    #endif
}

static void *first_fit(size_t asize)
{
    void *bp = free_lists[get_class(asize)];
    
    while (bp != NULL)
    {
        if (GET_SIZE(HDRP(bp)) >= asize)
        {
            return bp;
        }
        else
        {
            bp = SUCC(bp);
        }
    }

    return NULL;
}

static void *next_fit(size_t asize)
{
    void *bp = rover;

    while (GET_SIZE(HDRP(bp)) != 0)
    {
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= asize)
        {
            #if ROVER_NEXT == 0
                rover = bp;
            #else
                rover = NEXT_BLKP(bp);
            #endif
            return bp;
        }
        else
        {
            bp = NEXT_BLKP(bp);
        }
    }

    bp = NEXT_BLKP(heap_listp);

    while (bp != rover && GET_SIZE(HDRP(bp)) != 0)
    {
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= asize)
        {
            #if ROVER_NEXT == 0
                rover = bp;
            #else
                rover = NEXT_BLKP(bp);
            #endif
            return bp;
        }
        else
        {
            bp = NEXT_BLKP(bp);
        }
    }

    return NULL;
}

static void *best_fit(size_t asize)
{
    void *best_bp = NULL;
    size_t best_size = 0;
    void *bp = NEXT_BLKP(heap_listp);

    while (GET_SIZE(HDRP(bp)) != 0)
    {
        if (GET_ALLOC(HDRP(bp)) == 0)
        {
            if (GET_SIZE(HDRP(bp)) >= asize)
            {
                if (GET_SIZE(HDRP(bp)) == asize) return bp;
                else if (best_bp == NULL || GET_SIZE(HDRP(bp)) < best_size)
                {
                    best_bp = bp;
                    best_size = GET_SIZE(HDRP(bp));
                }
            }
        }
        bp = NEXT_BLKP(bp);
    }

    return best_bp;
}

static void place(void *bp, size_t asize)
{
    // 현재 블록 크기 읽기
    size_t csize = GET_SIZE(HDRP(bp));
    remove_free(bp);

    if ((csize - asize) >= MIN_BLOCK)
    {
        size_t remain_size = csize - asize;
        mark_alloc(bp, asize);
        bp = NEXT_BLKP(bp);  
        mark_free(bp, remain_size);
        insert_free(bp);
    }

    else
    {
        mark_alloc(bp, csize);  
    }
}

#if FIT_POLICY == 2
    static void fix_rover(char *bp)
    {
        if (rover > bp && rover < NEXT_BLKP(bp)) rover = bp;
    }
#endif

static void mark_alloc(void *bp, size_t size)
{
    PUT(HDRP(bp), PACK(size, 1));
    PUT(FTRP(bp), PACK(size, 1));
}

static void mark_free(void *bp, size_t size)
{
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
}

static size_t adjust_size(size_t size)
{
    size_t asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    return MAX(asize, MIN_BLOCK);
}

static int get_class(size_t size)
{
    return 0;
}

static void insert_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int idx = get_class(size);
    void *head = free_lists[idx];

    PRED(bp) = NULL;
    SUCC(bp) = head;

    if (head != NULL) PRED(head) = bp;

    free_lists[idx] = bp;
}

static void remove_free(void *bp)
{
    void *pred = PRED(bp);
    void *succ = SUCC(bp);

    if (pred != NULL) SUCC(pred) = succ;
    else
    {
        int idx = get_class(GET_SIZE(HDRP(bp)));
        free_lists[idx] = succ;
    }

    if (succ != NULL) PRED(succ) = pred;
}