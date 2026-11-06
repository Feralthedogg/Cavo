#ifndef CAVO_RUNTIME_H
#define CAVO_RUNTIME_H
#include <stdint.h>

/* The host owns this cell until the LLAM task is joined, not merely ready.
 * Status: 0 completed, 1 panicked, 2 cancelled. The entry takes no Cavo args. */
typedef struct cavo_result {
    int32_t status;
    int32_t exit_code;
} cavo_result;

void cavo_program_entry(void *result);
void *cavo_rt_allocate(uint64_t count, uint64_t size, uint64_t alignment);
void cavo_rt_free(void *pointer);
_Noreturn void cavo_rt_abort(void);
#endif
