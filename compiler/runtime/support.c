#define _POSIX_C_SOURCE 200112L
#include "cavo.h"
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#if defined(_WIN32)
#include <malloc.h>
#endif

_Static_assert(sizeof(size_t) == 8, "Cavo native runtime requires 64-bit size_t");
_Static_assert(sizeof(cavo_result) == 8, "Cavo entry result ABI changed");

void *cavo_rt_allocate(uint64_t count, uint64_t size, uint64_t alignment)
{
    if (alignment == 0 || (alignment & (alignment - 1)) != 0 ||
        alignment > (UINT64_C(1) << 29) ||
        (size != 0 && count > INT64_MAX / size)) {
        return NULL;
    }
    size_t bytes = (size_t)(count * size);
    if (bytes == 0) bytes = 1;
    if (alignment < sizeof(void *)) alignment = sizeof(void *);
#if defined(_WIN32)
    return _aligned_malloc(bytes, (size_t)alignment);
#else
    void *allocation = NULL;
    if (posix_memalign(&allocation, (size_t)alignment, bytes) != 0) return NULL;
    return allocation;
#endif
}

void cavo_rt_free(void *pointer)
{
#if defined(_WIN32)
    _aligned_free(pointer);
#else
    free(pointer);
#endif
}

_Noreturn void cavo_rt_abort(void)
{
    fputs("cavoite / E-RUNTIME-CHECK\nA fatal arithmetic, bounds, contract or cleanup check failed.\n", stderr);
    abort();
}
