#ifndef PQ_MIGRATE_AGGREGATE_H
#define PQ_MIGRATE_AGGREGATE_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
/* Fixed four-owner C profile. 0 accepted; 1 invalid input; 2 invalid proof; 3 local fault. */
int32_t pq_aggregate_verify(const uint8_t *proof, size_t proof_len,
                            const uint8_t *statement, size_t statement_len);
/* 0 ready, 3 local fault; no caller-supplied key or parameters. */
int32_t pq_aggregate_ready_v1(void);
/* Static NUL-terminated lowercase C verifier-key digest; do not free. */
const char *pq_aggregate_key_v1(void);
#ifdef __cplusplus
}
#endif
#endif
