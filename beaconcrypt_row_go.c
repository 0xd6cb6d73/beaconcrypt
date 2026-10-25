// SPDX-License-Identifier: 0BSD
//go:build cgo && !beaconcrypt_wazero

#include "beaconcrypt_row_go.h"
#include "_cgo_export.h"

typedef struct {
	void (*sink)(void *, const uint8_t *, uintptr_t);
	void *context;
} row_delivery;

static bool row_begin(void *context) { return beaconcryptGoRowBegin((uintptr_t)context); }
static bool row_commit(void *context) { return beaconcryptGoRowCommit((uintptr_t)context); }
static void row_rollback(void *context) { beaconcryptGoRowRollback((uintptr_t)context); }
static void row_destroy(void *context) { beaconcryptGoRowDestroy((uintptr_t)context); }
static int32_t row_load(void *context, const uint8_t *key, uintptr_t len, void *sink_context, void (*sink)(void *, const uint8_t *, uintptr_t)) {
	row_delivery delivery = {sink, sink_context};
	return beaconcryptGoRowLoad((uintptr_t)context, (uint8_t *)key, len, &delivery);
}
static bool row_store(void *context, const uint8_t *key, uintptr_t key_len, const uint8_t *value, uintptr_t value_len) {
	return beaconcryptGoRowStore((uintptr_t)context, (uint8_t *)key, key_len, (uint8_t *)value, value_len);
}
static beaconcrypt_RowStoreCallbacks callbacks(uintptr_t token) {
	beaconcrypt_RowStoreCallbacks result = {(void *)token, row_begin, row_load, row_store, row_commit, row_rollback, row_destroy};
	return result;
}
beaconcrypt_RowServerHandle *beaconcrypt_go_row_create(uint64_t kid, const uint8_t *seed, uintptr_t seed_len, const uint8_t *mldsa, uintptr_t mldsa_len, uintptr_t token, const uint8_t *lineage, uint32_t *status) {
	return beaconcrypt_row_server_create(kid, seed, seed_len, mldsa, mldsa_len, callbacks(token), lineage, 32, status);
}
beaconcrypt_RowServerHandle *beaconcrypt_go_row_open(uintptr_t token, const uint8_t *lineage, uint32_t *status) {
	return beaconcrypt_row_server_open(callbacks(token), lineage, 32, status);
}
void beaconcrypt_go_deliver_row(void *opaque, const uint8_t *bytes, uintptr_t len) {
	row_delivery *delivery = (row_delivery *)opaque;
	delivery->sink(delivery->context, bytes, len);
}

static bool row_transaction(void *context, beaconcrypt_RowSessionHandle *session, void *sink_context, void (*sink)(void *, const uint8_t *, uintptr_t)) {
	row_delivery delivery = {sink, sink_context};
	return beaconcryptGoRowTransaction((uintptr_t)context, session, &delivery);
}
static int32_t row_acceptance(void *context, beaconcrypt_RowSessionHandle *session, void *sink_context, void (*sink)(void *, const uint8_t *, uintptr_t)) {
	row_delivery delivery = {sink, sink_context};
	return beaconcryptGoRowAcceptance((uintptr_t)context, session, &delivery);
}
static bool row_completion(void *context, beaconcrypt_RowSessionHandle *session, const uint8_t *accepted, uintptr_t accepted_len, void *sink_context, void (*sink)(void *, const uint8_t *, uintptr_t)) {
	row_delivery delivery = {sink, sink_context};
	return beaconcryptGoRowCompletion((uintptr_t)context, session, (uint8_t *)accepted, accepted_len, &delivery);
}
beaconcrypt_Buffer beaconcrypt_go_row_transaction(beaconcrypt_RowServerHandle *server, uintptr_t token) {
	return beaconcrypt_row_server_transaction(server, (void *)token, row_transaction);
}
beaconcrypt_Buffer beaconcrypt_go_row_registration_transaction(beaconcrypt_RowServerHandle *server, uintptr_t token, uint32_t *phase) {
	return beaconcrypt_row_server_registration_transaction(server, (void *)token, row_acceptance, row_completion, phase);
}
