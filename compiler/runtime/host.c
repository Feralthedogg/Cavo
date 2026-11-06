#include "cavo.h"
#include <stdio.h>
#include <stdlib.h>
#if defined(CAVO_WITH_LLAM)
#include <llam/managed.h>
#if LLAM_VERSION_MAJOR != 3 || LLAM_VERSION_MINOR != 0 || LLAM_VERSION_PATCH != 0
#error Cavo requires the pinned LLAM 3.0.0 runtime SDK
#endif
#if LLAM_ABI_VERSION_MAJOR != 2 || LLAM_ABI_VERSION_MINOR != 4
#error Cavo requires LLAM public ABI 2.4
#endif

static int run_managed(cavo_result *result)
{
    llam_runtime_opts_t options;
    llam_preempt_opts_t preemption;
    llam_runtime_t *runtime = NULL;
    if (llam_abi_version() != LLAM_ABI_VERSION) {
        fputs("cavoite / E-RUNTIME-ABI\nLoaded LLAM library does not match public ABI 2.4.\n", stderr);
        return 125;
    }
    if (llam_runtime_opts_init(&options, sizeof options) != 0 ||
        llam_preempt_opts_init(&preemption, sizeof preemption) != 0) {
        perror("cavoite / E-RUNTIME-OPTIONS");
        return 125;
    }
    preemption.policy = LLAM_PREEMPT_POLICY_ASYNC_REQUIRED;
    if (llam_runtime_create_managed(&options, sizeof options, &preemption,
                                    sizeof preemption, &runtime) != 0) {
        perror("cavoite / E-RUNTIME-START: required asynchronous profile unavailable");
        return 125;
    }
    llam_task_t *task = llam_runtime_spawn_ex(runtime, cavo_program_entry, result, NULL, 0);
    if (task == NULL) {
        perror("cavoite / E-RUNTIME-ADMISSION");
        llam_runtime_destroy(runtime);
        return 125;
    }
    /* A failed run/join does not prove that the host stack is no longer used.
     * Stop the process rather than returning through live borrowed storage. */
    if (llam_runtime_run_handle(runtime) != 0 || llam_join(task) != 0) {
        perror("cavoite / E-RUNTIME-RECLAIM");
        cavo_rt_abort();
    }
    llam_preempt_info_t info;
    if (llam_runtime_preempt_info_ex(runtime, &info, sizeof info) != 0 ||
        info.effective_policy != LLAM_PREEMPT_POLICY_ASYNC_REQUIRED ||
        info.reason != LLAM_PREEMPT_REASON_NONE || info.registered_entries == 0) {
        fputs("cavoite / E-RUNTIME-POLICY\nRequired asynchronous admission was not established.\n", stderr);
        cavo_rt_abort();
    }
    if (getenv("CAVO_RUNTIME_STATS") != NULL) {
        (void)llam_runtime_write_stats_json_handle(runtime, 2);
    }
    llam_runtime_destroy(runtime);
    return 0;
}
#endif

int main(void)
{
    cavo_result result = {0, 0};
#if defined(CAVO_WITH_LLAM)
    int failure = run_managed(&result);
    if (failure != 0) return failure;
#else
    cavo_program_entry(&result);
#endif
    if (result.status != 0) {
        fprintf(stderr, "cavoite / E-RUNTIME-TASK\nRoot task %s.\n",
                result.status == 2 ? "was cancelled" : "panicked");
        return 125;
    }
    return result.exit_code;
}
