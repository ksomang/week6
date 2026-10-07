/*
 * mm.c - 분리 가용 리스트(segregated free list) 기반 malloc
 *
 * [블록 구조] 64비트, 8바이트 정렬, 최소 블록 24바이트
 *
 *   할당 블록:  [헤더 4][        페이로드        ][푸터 4]
 *   가용 블록:  [헤더 4][pred 8][succ 8][ ...  ][푸터 4]
 *                       ^ bp
 *
 *   - 헤더와 푸터에는 (블록 크기 | 할당 비트)를 저장한다.
 *   - 가용 블록은 페이로드 앞 16바이트에 같은 등급 리스트의
 *     앞 블록(pred)과 뒤 블록(succ) 주소를 저장한다.
 *   - 할당 블록도 free되면 pred·succ가 필요하므로 최소 24바이트다.
 *
 * [힙 구조]
 *
 *   [리스트 시작 칸 x 20][패딩][프롤로그 헤더·푸터][블록 ...][에필로그 헤더]
 *    ^ free_lists                ^ heap_listp
 *
 *   - 과제 규칙상 전역 배열을 쓸 수 없어서, 리스트 시작 칸 20개를
 *     힙 맨 앞에 두고 전역 포인터 free_lists 하나로 가리킨다.
 *
 * [가용 리스트 구성]
 *
 *   - 크기 등급 20개: 24~31, 32~63, 64~127, ... (경계가 두 배씩),
 *     마지막 등급은 그보다 큰 블록 전부.
 *   - 등급마다 이중 연결 리스트 하나. 리스트 안에서는 크기 오름차순으로 정렬한다.
 *
 * [할당기가 리스트를 다루는 방법]
 *
 *   - malloc: 요청 크기의 등급부터 위 등급으로 올라가며 first fit으로 찾는다.
 *     등급 안이 크기 순이라 처음 맞는 블록이 그 등급의 best fit이다.
 *     못 찾으면 힙을 늘린다. 힙의 마지막 블록이 가용이면 모자란 만큼만 늘린다.
 *   - place: 고른 블록을 리스트에서 빼고, 남는 조각이 24 이상이면 자른다.
 *     요청이 PLACE_SPLIT(96) 이상이면 가용 블록의 뒤쪽을, 미만이면 앞쪽을
 *     할당해서 큰 블록과 작은 블록이 서로 다른 쪽에 모이게 한다.
 *     남은 조각은 크기에 맞는 등급 리스트에 넣는다.
 *   - free: 즉시 연결한다. 합쳐질 이웃은 먼저 리스트에서 빼고,
 *     합친 블록을 한 번 리스트에 넣는다.
 *   - realloc: 지금 블록으로 충분하면 그대로, 뒤 블록이 가용이면 흡수,
 *     힙 끝이면 모자란 만큼 늘려서 흡수, 모두 안 되면 새로 할당하고 복사한다.
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
    "SW-AI 13기 2팀",
    /* First member's full name */
    "김소망",
    /* First member's email address */
    "aaa",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define WSIZE 4                 /* 워드, 헤더·푸터 크기 (바이트) */
#define DSIZE 8                 /* 더블 워드, 정렬 단위 (바이트) */
#define CHUNKSIZE (1<<12)       /* 힙을 늘리는 기본 단위 (바이트) */
#define MIN_BLOCK (3*DSIZE)     /* 최소 블록: 헤더 4 + pred 8 + succ 8 + 푸터 4 */
#define PLACE_SPLIT 96          /* 이 크기 이상이면 가용 블록 뒤쪽에 할당 (7·8번 실험으로 결정) */
#define LIST_NUM 20             /* 크기 등급(가용 리스트) 수 */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 크기와 할당 비트를 한 워드로 합친다 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p의 워드를 읽고 쓴다 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 헤더·푸터에서 크기와 할당 비트를 읽는다 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 포인터 bp로 헤더와 푸터의 주소를 구한다 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp로 힙에서 바로 앞뒤 블록의 bp를 구한다 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 가용 블록 bp에 저장된 리스트의 앞(pred)·뒤(succ) 블록 주소 */
#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*((char **)(bp) + 1))

static char *heap_listp;        /* 프롤로그 블록의 bp */
static char **free_lists;       /* 힙 맨 앞 리스트 시작 칸들 */

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);
static void mark_alloc(void *bp, size_t size);
static void mark_free(void *bp, size_t size);
static size_t adjust_size(size_t size);
static int get_class(size_t size);
static void insert_free(void *bp);
static void remove_free(void *bp);

/*
 * mm_init - 힙을 초기화한다. 리스트 시작 칸 20개를 NULL로 비우고,
 *   패딩·프롤로그·에필로그를 깐 뒤 CHUNKSIZE만큼 첫 가용 블록을 만든다.
 *   mdriver가 트레이스마다 다시 부르므로 리스트 칸을 매번 비운다.
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

    PUT(heap_listp, 0);                             /* 패딩 */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  /* 프롤로그 헤더 */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  /* 프롤로그 푸터 */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      /* 에필로그 헤더 */

    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;

    return 0;
}

/*
 * mm_malloc - size바이트 이상의 페이로드를 가진 블록을 할당한다.
 *   맞는 가용 블록이 있으면 place로 자르고, 없으면 힙을 늘린다.
 *   힙의 마지막 블록이 가용이면 부족한 만큼만 늘려서 낭비를 줄인다.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* 조정한 블록 크기 */
    size_t extendsize;  /* 맞는 블록이 없을 때 힙을 늘릴 크기 */
    char *bp;

    if (size == 0) return NULL;

    asize = adjust_size(size);

    /* 안쪽 괄호를 빼면 != 가 = 보다 먼저 계산돼서 bp에 0이나 1이 들어간다. */
    if ((bp = find_fit(asize)) != NULL)
    {
        return place(bp, asize);
    }

    char *heap_end = mem_sbrk(0);           /* 지금 힙 끝 (brk) */
    char *last_ftr = heap_end - DSIZE;      /* 에필로그 바로 앞 = 마지막 블록 푸터 */

    if (GET_ALLOC(last_ftr) == 0)
    {
        extendsize = asize - GET_SIZE(last_ftr);    /* 가용이면 부족한 만큼만 */
    }
    else
    {
        extendsize = MAX(asize, CHUNKSIZE);         /* 할당이면 넉넉하게 */
    }

    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;

    return place(bp, asize);
}

/*
 * mm_free - 블록을 가용으로 표시하고 이웃 가용 블록과 즉시 연결한다.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    mark_free(bp, size);
    coalesce(bp);
}

/*
 * mm_realloc - 블록 크기를 바꾼다. 내용은 옛 크기와 새 크기 중 작은 쪽만큼 보존한다.
 *   [A] 지금 블록으로 충분하면 그대로 반환
 *   [B] 뒤 블록이 가용이고 합이 충분하면 흡수
 *   [C] 힙의 마지막 블록이면 모자란 만큼만 힙을 늘려서 흡수
 *   [D] 모두 안 되면 새로 할당하고 복사한 뒤 옛 블록을 해제
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldbp = bp;
    void *newbp;
    size_t copySize;
    size_t asize;

    if (oldbp == NULL) return mm_malloc(size);

    if (size == 0)
    {
        mm_free(oldbp);
        return NULL;
    }

    asize = adjust_size(size);

    /* [A] 지금 블록으로 충분 */
    if (asize <= GET_SIZE(HDRP(oldbp)))
    {
        return oldbp;
    }
    /* [B] 뒤 블록이 가용이고 합치면 충분: 뒤 블록을 리스트에서 빼고 흡수 */
    else if (GET_ALLOC(HDRP(NEXT_BLKP(oldbp))) == 0 && GET_SIZE(HDRP(oldbp)) + GET_SIZE(HDRP(NEXT_BLKP(oldbp))) >= asize)
    {
        size_t new_size = GET_SIZE(HDRP(oldbp)) + GET_SIZE(HDRP(NEXT_BLKP(oldbp)));
        remove_free(NEXT_BLKP(oldbp));
        mark_alloc(oldbp, new_size);
        return oldbp;
    }
    /* [C] 힙의 마지막 블록: 모자란 만큼 늘리고, extend_heap이 넣은 블록을 빼서 흡수 */
    else if (GET_SIZE(HDRP(NEXT_BLKP(oldbp))) == 0)
    {
        if (extend_heap((asize - GET_SIZE(HDRP(oldbp))) / WSIZE) != NULL)
        {
            size_t new_size = GET_SIZE(HDRP(oldbp)) + GET_SIZE(HDRP(NEXT_BLKP(oldbp)));
            remove_free(NEXT_BLKP(oldbp));
            mark_alloc(oldbp, new_size);
            return oldbp;
        }
    }

    /* [D] 이사: 새로 할당하고 페이로드를 복사한 뒤 옛 블록을 해제 */
    newbp = mm_malloc(size);
    if (newbp == NULL) return NULL;

    copySize = GET_SIZE(HDRP(oldbp)) - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newbp, oldbp, copySize);
    mm_free(oldbp);
    return newbp;
}

/*
 * coalesce - bp를 앞뒤 가용 블록과 합치고 결과를 리스트에 넣는다.
 *   합쳐질 이웃은 헤더를 바꾸기 전에 리스트에서 뺀다. 합친 블록의 bp를 반환한다.
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  /* 앞 블록 할당 비트 */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  /* 뒤 블록 할당 비트 */
    size_t size = GET_SIZE(HDRP(bp));                    /* 현재 블록 크기 */

    if (prev_alloc && next_alloc)
    {
        /* 합칠 이웃 없음. 아래 공통 insert로 내려감 */
    }
    else if (prev_alloc && !next_alloc)
    {
        remove_free(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        mark_free(bp, size);
    }
    else if (!prev_alloc && next_alloc)
    {
        remove_free(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        mark_free(bp, size);
    }
    else
    {
        remove_free(PREV_BLKP(bp));
        remove_free(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        mark_free(bp, size);
    }

    insert_free(bp);

    return bp;
}

/*
 * extend_heap - 힙을 words워드만큼 늘려 가용 블록을 만들고 새 에필로그를 쓴다.
 *   힙 끝의 가용 블록과 연결한 결과를 반환한다.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;   /* 8바이트 정렬 유지 */

    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    mark_free(bp, size);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* 새 에필로그 헤더 */

    return coalesce(bp);
}

/*
 * find_fit - asize의 등급부터 위 등급으로 올라가며 처음 맞는 가용 블록을 찾는다.
 *   등급 안이 크기 순이라 처음 맞는 블록이 그 등급의 best fit이다.
 *   모든 등급에 없으면 NULL을 반환한다.
 */
static void *find_fit(size_t asize)
{
    for (int idx = get_class(asize); idx < LIST_NUM; idx++)
    {
        char *bp = free_lists[idx];

        while (bp != NULL)
        {
            if (GET_SIZE(HDRP(bp)) >= asize) return bp;
            bp = SUCC(bp);
        }
    }

    return NULL;
}

/*
 * place - 가용 블록 bp를 리스트에서 빼고 asize만큼 할당한다. 할당한 블록의 bp를 반환한다.
 *   남는 조각이 MIN_BLOCK보다 작으면 통째로 할당한다.
 *   asize가 PLACE_SPLIT 이상이면 뒤쪽을, 미만이면 앞쪽을 할당하고
 *   남은 조각을 리스트에 넣는다.
 */
static void *place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_free(bp);                        /* 헤더를 바꾸기 전에 뺀다 */
    size_t remain = csize - asize;

    if (remain < MIN_BLOCK)
    {
        mark_alloc(bp, csize);
        return bp;
    }
    else if (asize < PLACE_SPLIT)          /* 작은 블록: 뒤쪽에 */
    {
        mark_free(bp, remain);              /* 앞 조각 헤더를 먼저 써야 */
        insert_free(bp);
        char *alloc_bp = NEXT_BLKP(bp);     /* NEXT_BLKP가 뒷부분을 정확히 가리킨다 */
        mark_alloc(alloc_bp, asize);
        return alloc_bp;
    }
    else                                    /* 큰 블록: 앞쪽에 */
    {
        mark_alloc(bp, asize);
        char *next = NEXT_BLKP(bp);
        mark_free(next, remain);
        insert_free(next);
        return bp;
    }
}

/*
 * mark_alloc, mark_free - 블록의 헤더와 푸터에 크기와 할당 비트를 쓴다.
 *   헤더를 먼저 써야 FTRP가 새 크기로 계산된다.
 */
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

/*
 * adjust_size - 요청 크기에 헤더·푸터 8바이트를 더해 8의 배수로 올리고,
 *   최소 블록 크기(24)보다 작으면 24로 맞춘다.
 */
static size_t adjust_size(size_t size)
{
    size_t asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    return MAX(asize, MIN_BLOCK);
}

/*
 * get_class - 블록 크기가 속한 등급 번호(0 ~ LIST_NUM-1)를 반환한다.
 *   경계를 32부터 두 배씩 키우며 크기가 경계보다 작아지는 첫 등급을 찾는다.
 */
static int get_class(size_t size)
{
    int idx = 0;
    size_t limit = 32;

    while (idx < LIST_NUM - 1 && size >= limit)
    {
        limit = limit * 2;
        idx++;
    }

    return idx;
}

/*
 * insert_free - 가용 블록을 크기에 맞는 등급 리스트의 크기 오름차순 자리에 넣는다.
 *   호출 전에 헤더에 크기가 쓰여 있어야 한다.
 */
static void insert_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int idx = get_class(size);

    char *prev = NULL;
    char *cur = free_lists[idx];

    while (cur != NULL && GET_SIZE(HDRP(cur)) < size)
    {
        prev = cur;
        cur = SUCC(cur);
    }

    PRED(bp) = prev;
    SUCC(bp) = cur;

    if (cur != NULL) PRED(cur) = bp;
    if (prev != NULL) SUCC(prev) = bp;
    else free_lists[idx] = bp;
}

/*
 * remove_free - 가용 블록을 들어 있던 등급 리스트에서 뺀다.
 *   맨 앞이면 리스트 시작 칸을 고친다. 호출 시점에 헤더는 원래 크기여야 한다.
 */
static void remove_free(void *bp)
{
    char *pred = PRED(bp);
    char *succ = SUCC(bp);

    if (pred != NULL) SUCC(pred) = succ;
    else
    {
        int idx = get_class(GET_SIZE(HDRP(bp)));
        free_lists[idx] = succ;
    }

    if (succ != NULL) PRED(succ) = pred;
}