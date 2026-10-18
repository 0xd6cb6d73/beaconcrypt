// SPDX-License-Identifier: 0BSD

#include "beaconcrypt_go.h"
#include "_cgo_export.h"

typedef struct {
	void (*sink)(void *, const uint8_t *, uintptr_t);
	void *context;
} snapshot_delivery;

static bool go_store_load(void *context, void *sink_context, void (*sink)(void *, const uint8_t *, uintptr_t)) {
	snapshot_delivery delivery = {sink, sink_context};
	return beaconcryptGoStoreLoad((uintptr_t)context, &delivery);
}

static bool go_store_compare_and_swap(void *context, const beaconcrypt_SnapshotHeadInfo *expected, const uint8_t *bytes, uintptr_t len) {
	return beaconcryptGoStoreCompareAndSwap((uintptr_t)context, (beaconcrypt_SnapshotHeadInfo *)expected, (uint8_t *)bytes, len);
}

static void go_store_destroy(void *context) {
	beaconcryptGoStoreDestroy((uintptr_t)context);
}

static beaconcrypt_SnapshotStoreCallbacks go_store_callbacks(uintptr_t handle) {
	beaconcrypt_SnapshotStoreCallbacks callbacks = {
		(void *)handle, go_store_load, go_store_compare_and_swap, go_store_destroy
	};
	return callbacks;
}

beaconcrypt_Server *beaconcrypt_go_server_create_with_store(uint64_t server_kid, const uint8_t *seed, uintptr_t seed_len, uintptr_t token, uint32_t *status_out) {
	return beaconcrypt_server_create_with_store(server_kid, seed, seed_len, go_store_callbacks(token), status_out);
}

beaconcrypt_Server *beaconcrypt_go_server_create_with_store_and_lineage(uint64_t server_kid, const uint8_t *seed, uintptr_t seed_len, uintptr_t token, const uint8_t *lineage, uintptr_t lineage_len, uint32_t *status_out) {
	return beaconcrypt_server_create_with_store_and_lineage(server_kid, seed, seed_len, go_store_callbacks(token), lineage, lineage_len, status_out);
}

beaconcrypt_Server *beaconcrypt_go_server_restore_with_store(uintptr_t token, uint32_t *status_out) {
	return beaconcrypt_server_restore_with_store(go_store_callbacks(token), status_out);
}

void beaconcrypt_go_deliver_snapshot(void *opaque_delivery, const uint8_t *bytes, uintptr_t len) {
	snapshot_delivery *delivery = (snapshot_delivery *)opaque_delivery;
	delivery->sink(delivery->context, bytes, len);
}
