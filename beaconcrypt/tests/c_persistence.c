// SPDX-License-Identifier: 0BSD

#include "bindings.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* Test store only: production stores need durable, rollback-resistant CAS. */
typedef struct {
  uint8_t *bytes;
  uintptr_t len;
  beaconcrypt_SnapshotHeadInfo head;
  bool present;
  bool fail_next;
  unsigned attempts;
  unsigned destroyed;
} Store;

typedef struct {
  Store *store;
} Context;

static bool load(void *opaque, void *sink_context,
                 void (*sink)(void *, const uint8_t *, uintptr_t)) {
  Store *store = ((Context *)opaque)->store;
  if (!store->present) {
    return false;
  }
  sink(sink_context, store->bytes, store->len);
  return true;
}

static bool same_head(const beaconcrypt_SnapshotHeadInfo *left,
                      const beaconcrypt_SnapshotHeadInfo *right) {
  return left->generation == right->generation &&
         memcmp(left->lineage, right->lineage, sizeof(left->lineage)) == 0 &&
         memcmp(left->digest, right->digest, sizeof(left->digest)) == 0;
}

static bool compare_and_swap(void *opaque,
                             const beaconcrypt_SnapshotHeadInfo *expected,
                             const uint8_t *bytes, uintptr_t len) {
  Store *store = ((Context *)opaque)->store;
  store->attempts++;
  if (store->fail_next) {
    store->fail_next = false;
    return false;
  }
  if (store->present != (expected != NULL) ||
      (expected != NULL && !same_head(&store->head, expected))) {
    return false;
  }
  beaconcrypt_SnapshotHeadInfo next;
  if (beaconcrypt_snapshot_validate_successor(bytes, len, expected, &next) !=
      beaconcrypt_STATUS_OK) {
    return false;
  }
  uint8_t *copy = malloc(len);
  if (copy == NULL) {
    return false;
  }
  memcpy(copy, bytes, len);
  free(store->bytes);
  store->bytes = copy;
  store->len = len;
  store->head = next;
  store->present = true;
  return true;
}

static void destroy(void *opaque) {
  Context *context = opaque;
  context->store->destroyed++;
  free(context);
}

static beaconcrypt_SnapshotStoreCallbacks callbacks(Store *store) {
  Context *context = malloc(sizeof(*context));
  assert(context != NULL);
  context->store = store;
  beaconcrypt_SnapshotStoreCallbacks result = {
      .context = context,
      .load = load,
      .compare_and_swap = compare_and_swap,
      .destroy = destroy,
  };
  return result;
}

int main(void) {
  Store store = {0};
  uint8_t seed[32] = {7};
  uint8_t mldsa_seed[32] = {8};
  uint8_t lineage[32] = {9};
  uint32_t status = UINT32_MAX;
  beaconcrypt_Server *server = beaconcrypt_server_create_with_store_and_lineage(
      19, seed, sizeof(seed), mldsa_seed, sizeof(mldsa_seed), callbacks(&store),
      lineage, sizeof(lineage), &status);
  assert(server != NULL && status == beaconcrypt_STATUS_OK);
  assert(store.attempts == 1 && store.head.generation == 0);
  beaconcrypt_SnapshotHeadInfo head;
  assert(beaconcrypt_server_head(server, &head) == beaconcrypt_STATUS_OK);
  assert(same_head(&head, &store.head));
  assert(memcmp(head.lineage, lineage, sizeof(lineage)) == 0);

  beaconcrypt_Buffer pk = beaconcrypt_server_identity_pk(server);
  beaconcrypt_Buffer mldsa_pk = beaconcrypt_server_mldsa_public_key(server);
  assert(pk.len == 32 && mldsa_pk.len == beaconcrypt_MLDSA_PUBLIC_KEY_LEN);
  beaconcrypt_Beacon *beacon =
      beaconcrypt_beacon_new(19, pk.ptr, pk.len, mldsa_pk.ptr, mldsa_pk.len);
  assert(beacon != NULL);
  beaconcrypt_free_buffer(pk);
  beaconcrypt_free_buffer(mldsa_pk);
  beaconcrypt_Buffer registration = beaconcrypt_generate_registration(beacon);
  beaconcrypt_RegistrationResponse response = beaconcrypt_register_beacon(
      server, registration.ptr, registration.len, NULL, 0);
  beaconcrypt_free_buffer(registration);
  assert(response.response.ptr != NULL);
  assert(store.attempts == 3 && store.head.generation == 2);
  beaconcrypt_Buffer initial = beaconcrypt_process_initial_message(
      beacon, response.response.ptr, response.response.len);
  assert(initial.ptr != NULL);
  beaconcrypt_free_buffer(initial);
  beaconcrypt_free_buffer(response.response);

  store.fail_next = true;
  beaconcrypt_Buffer outbound = beaconcrypt_encrypt_to_beacon(
      server, response.key_id, (const uint8_t *)"task", 4);
  assert(outbound.ptr == NULL && store.head.generation == 2);
  assert(beaconcrypt_server_last_status(server) ==
         beaconcrypt_STATUS_STALE_GENERATION);
  assert(beaconcrypt_server_is_poisoned(server));
  assert(beaconcrypt_server_head(server, &head) == beaconcrypt_STATUS_OK);
  pk = beaconcrypt_server_identity_pk(server);
  assert(pk.len == 32);
  beaconcrypt_free_buffer(pk);
  assert(beaconcrypt_server_last_status(server) ==
         beaconcrypt_STATUS_STALE_GENERATION);
  beaconcrypt_server_free(server);
  assert(store.destroyed == 1);

  server = beaconcrypt_server_restore_with_store(callbacks(&store), &status);
  assert(server != NULL && status == beaconcrypt_STATUS_OK);
  assert(store.head.generation == 3);
  outbound = beaconcrypt_encrypt_to_beacon(server, response.key_id,
                                          (const uint8_t *)"task", 4);
  assert(outbound.ptr != NULL && store.head.generation == 4);
  beaconcrypt_Buffer plaintext = beaconcrypt_decrypt_server_message(
      beacon, outbound.ptr, outbound.len);
  assert(plaintext.len == 4 && memcmp(plaintext.ptr, "task", 4) == 0);
  beaconcrypt_free_buffer(plaintext);
  beaconcrypt_free_buffer(outbound);

  beaconcrypt_Buffer inbound = beaconcrypt_encrypt_to_server(
      beacon, (const uint8_t *)"result", 6);
  store.fail_next = true;
  plaintext = beaconcrypt_decrypt_beacon_message(server, inbound.ptr, inbound.len);
  assert(plaintext.ptr == NULL && store.head.generation == 4);
  assert(beaconcrypt_server_is_poisoned(server));
  assert(beaconcrypt_server_last_status(server) ==
         beaconcrypt_STATUS_STALE_GENERATION);
  beaconcrypt_server_free(server);
  assert(store.destroyed == 2);

  server = beaconcrypt_server_restore_with_store(callbacks(&store), &status);
  assert(server != NULL && status == beaconcrypt_STATUS_OK);
  plaintext = beaconcrypt_decrypt_beacon_message(server, inbound.ptr, inbound.len);
  assert(plaintext.len == 6 && memcmp(plaintext.ptr, "result", 6) == 0);
  beaconcrypt_free_buffer(plaintext);
  unsigned attempts = store.attempts;
  plaintext = beaconcrypt_decrypt_beacon_message(server, inbound.ptr, inbound.len);
  assert(plaintext.ptr == NULL && store.attempts == attempts);
  assert(beaconcrypt_server_last_status(server) == beaconcrypt_STATUS_REJECTED);
  assert(!beaconcrypt_server_is_poisoned(server));
  beaconcrypt_free_buffer(inbound);
  beaconcrypt_server_free(server);
  beaconcrypt_beacon_free(beacon);
  assert(store.destroyed == 3);
  free(store.bytes);
  return 0;
}
