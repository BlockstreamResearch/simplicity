#ifndef SIMPLICITY_CPU_H
#define SIMPLICITY_CPU_H

#include <stdint.h>

static const uint32_t SIMPLICITY_HAS_SHA_NI_FLAG = 1;

/* WARNING: This function isn't threadsafe and must not be called concurrently with any function in this library, including itself.
 * It is encouranged that you call this function once in the main function of your program
 *
 * This function inspects the CPU's capabilities and enables the use of some optimized instructions, if they are known and available.
 *
 * If the CPU supports Intel sha_ni operations, the result value has the SIMPLICITY_HAS_SHA_NI_FLAG bit set.
 */
uint32_t simplicity_cpu_optimize_not_thread_safe(void);

#endif
