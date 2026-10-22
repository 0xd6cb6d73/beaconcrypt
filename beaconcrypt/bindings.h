#ifndef _BEACON_CRYPT_H_
#define _BEACON_CRYPT_H_

/* Generated with cbindgen:0.29.4 */

// Do not modify manually.

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

/**
 * Maximum complete encoded transport message size in bytes, including all framing.
 */
#define beaconcrypt_MAX_MESSAGE_SIZE 33554432

#define beaconcrypt_MLDSA_PUBLIC_KEY_LEN 1952

#define beaconcrypt_MLDSA_SIGNATURE_LEN 3309



#define beaconcrypt_KDF_STATE_SIZE 32

/**
 * crypto_aead::chacha20poly1305_ietf::KEYBYTES
 */
#define beaconcrypt_AEAD_KEY_LEN 32

/**
 * crypto_aead::chacha20poly1305_ietf::NPUBBYTES
 */
#define beaconcrypt_AEAD_NONCE_LEN 12

/**
 * crypto_aead::chacha20poly1305_ietf::ABYTES
 */
#define beaconcrypt_AEAD_TAG_LEN 16

#define beaconcrypt_KDF_RATCHET_OUTPUT_LEN ((beaconcrypt_AEAD_KEY_LEN + beaconcrypt_KDF_STATE_SIZE) + beaconcrypt_AEAD_NONCE_LEN)

#define beaconcrypt_RATCHET_MAX_GAP 50

#define beaconcrypt_COMMITMENT_SIZE 64

#define beaconcrypt_MESSAGE_OVERHEAD (beaconcrypt_COMMITMENT_SIZE + beaconcrypt_AEAD_TAG_LEN)

#define beaconcrypt_KEX_KDF_OUT_LEN 32

/**
 * crypto_scalarmult::BYTES
 */
#define beaconcrypt_DH_OUT_LEN 32

#define beaconcrypt_ED25519_SEED_SIZE 32

#define beaconcrypt_STATUS_OK 0

#define beaconcrypt_STATUS_REJECTED 1

#define beaconcrypt_STATUS_INVALID_ARGUMENT 2

#define beaconcrypt_STATUS_MISSING_SNAPSHOT 3

#define beaconcrypt_STATUS_INVALID_SNAPSHOT 4

#define beaconcrypt_STATUS_NON_CANONICAL_SNAPSHOT 5

#define beaconcrypt_STATUS_STALE_GENERATION 6

#define beaconcrypt_STATUS_GENERATION_EXHAUSTED 7

#define beaconcrypt_STATUS_ENCODING 8

#define beaconcrypt_STATUS_OUTPUT_ENCODING 9

#define beaconcrypt_STATUS_INITIALIZATION 10

#define beaconcrypt_STATUS_DIGEST 11

#define beaconcrypt_STATUS_POISONED 12

/**
 * Opaque beacon handle exposed by the C API and owned by its caller.
 */
typedef struct beaconcrypt_Beacon beaconcrypt_Beacon;

/**
 * Opaque server handle owned by the C caller.
 *
 * Callers must serialize all access to one handle, including queries and destruction. Store callbacks must not reenter their owning handle.
 */
/**
 * Server backed by trusted snapshot storage. Store callbacks must not reenter this server.
 */
typedef struct beaconcrypt_Server beaconcrypt_Server;

/**
 * Heap-allocated byte buffer returned by the C API.
 *
 * A non-empty buffer must be released exactly once with `beaconcrypt_free_buffer`. An empty buffer has a null `ptr` and indicates either empty output or failure, depending on the called function.
 */
typedef struct beaconcrypt_Buffer {
  /**
   * Pointer to the first byte, or null when the buffer is empty.
   */
  uint8_t *ptr;
  /**
   * Number of initialized bytes available through `ptr`.
   */
  uintptr_t len;
  /**
   * Allocation capacity reserved for `beaconcrypt_free_buffer`; callers must not modify it.
   */
  uintptr_t cap;
} beaconcrypt_Buffer;

/**
 * Non-secret identity of one complete server snapshot. Its digest is not an authenticator.
 */
typedef struct beaconcrypt_SnapshotHeadInfo {
  uint8_t lineage[32];
  uint64_t generation;
  uint8_t digest[32];
} beaconcrypt_SnapshotHeadInfo;

/**
 * Trusted, rollback-resistant, linearizable durable storage for one server lineage.
 *
 * `load` returns false without calling `sink` for an empty store. Otherwise it calls `sink` synchronously exactly once with nonempty borrowed snapshot bytes and returns true; Rust copies the bytes before `sink` returns. `compare_and_swap` compares the complete current head against `expected` (null means an empty store), validates the successor, and durably stores the exact replacement bytes and head before returning true. The store must protect integrity, provenance and freshness; snapshot bytes and digests do not authenticate themselves.
 *
 * Constructors take ownership of `context` immediately, including on failure. `destroy`, when supplied, runs exactly once after the final callback; otherwise the caller manages the context lifetime. All callbacks and borrowed arguments remain valid until they return, must not unwind, retain borrowed pointers, call the sink after `load` returns, or reenter the owning handle. The caller serializes access to the handle and store.
 */
typedef struct beaconcrypt_SnapshotStoreCallbacks {
  void *context;
  bool (*load)(void *context, void *sink_context, void (*sink)(void*, const uint8_t*, uintptr_t));
  bool (*compare_and_swap)(void *context,
                           const struct beaconcrypt_SnapshotHeadInfo *expected,
                           const uint8_t *replacement,
                           uintptr_t replacement_len);
  void (*destroy)(void *context);
} beaconcrypt_SnapshotStoreCallbacks;

/**
 * Result returned after a successful server-side beacon registration.
 */
typedef struct beaconcrypt_RegistrationResponse {
  /**
   * Serialized registration response for the beacon.
   */
  struct beaconcrypt_Buffer response;
  /**
   * Key identifier assigned to the registered beacon.
   */
  uint64_t key_id;
} beaconcrypt_RegistrationResponse;

/**
 * Message output accompanied by observational ratchet metadata.
 */
typedef struct beaconcrypt_EncryptState {
  /**
   * Ciphertext for encryption calls or plaintext for decryption calls.
   */
  struct beaconcrypt_Buffer data;
  /**
   * Inert plaintext ratchet JSON for observation only.
   * It is secret-bearing, unauthenticated, and not restorable.
   */
  struct beaconcrypt_Buffer state;
  /**
   * Key identifier used by the ratchet operation.
   */
  uint64_t key_id;
  /**
   * Ratchet sequence number used by the operation.
   */
  uint64_t seq;
} beaconcrypt_EncryptState;



#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/**
 * Release a byte buffer returned by this API.
 *
 * Passing an empty buffer is allowed. The buffer and its pointer must not be used after this call.
 * The complete allocation is wiped before release. Copies retained by the caller are not erased.
 */
void beaconcrypt_free_buffer(struct beaconcrypt_Buffer buffer);

/**
 * Create a server with independently generated Ed25519 and ML-DSA-65 identity keys.
 *
 * Returns an owned handle, or null on failure. Release a non-null handle with `beaconcrypt_server_free`.
 */
struct beaconcrypt_Server *beaconcrypt_server_new(uint64_t server_kid);

/**
 * Create a server with independent optional Ed25519 and ML-DSA-65 identity seeds.
 *
 * Each null pointer or zero length selects an independently generated identity key. Each non-empty seed must contain exactly 32 readable secret bytes.
 *
 * Returns an owned handle, or null when creation fails. Release a non-null handle with `beaconcrypt_server_free`.
 */
struct beaconcrypt_Server *beaconcrypt_server_new_from_seed(uint64_t server_kid,
                                                            const uint8_t *seed_ptr,
                                                            uintptr_t seed_len,
                                                            const uint8_t *mldsa_seed_ptr,
                                                            uintptr_t mldsa_seed_len);

/**
 * Create a server whose results are released only after the store's durable compare-and-swap succeeds.
 *
 * The callbacks take ownership of their context even when construction fails. Each null seed or zero seed length selects an independently generated identity. `status_out` may be null; otherwise it receives a `beaconcrypt_STATUS_*` code. Returns null on failure.
 */
struct beaconcrypt_Server *beaconcrypt_server_create_with_store(uint64_t server_kid,
                                                                const uint8_t *seed_ptr,
                                                                uintptr_t seed_len,
                                                                const uint8_t *mldsa_seed_ptr,
                                                                uintptr_t mldsa_seed_len,
                                                                struct beaconcrypt_SnapshotStoreCallbacks callbacks,
                                                                uint32_t *status_out);

/**
 * Create a durable server under a caller-provisioned 32-byte lineage.
 *
 * Allocate each lineage to exactly one rollback-resistant authoritative store head. Callback context ownership and `status_out` follow `beaconcrypt_server_create_with_store`.
 */
struct beaconcrypt_Server *beaconcrypt_server_create_with_store_and_lineage(uint64_t server_kid,
                                                                            const uint8_t *seed_ptr,
                                                                            uintptr_t seed_len,
                                                                            const uint8_t *mldsa_seed_ptr,
                                                                            uintptr_t mldsa_seed_len,
                                                                            struct beaconcrypt_SnapshotStoreCallbacks callbacks,
                                                                            const uint8_t *lineage_ptr,
                                                                            uintptr_t lineage_len,
                                                                            uint32_t *status_out);

/**
 * Restore the trusted current snapshot and durably claim its next generation before returning a live owner.
 *
 * Callback context ownership and `status_out` follow `beaconcrypt_server_create_with_store`. The store must protect snapshot integrity, provenance and freshness and coordinate concurrent owners.
 */
struct beaconcrypt_Server *beaconcrypt_server_restore_with_store(struct beaconcrypt_SnapshotStoreCallbacks callbacks,
                                                                 uint32_t *status_out);

/**
 * Read the owner's current non-secret snapshot head. Returns a status code without changing the last operation's status.
 */
uint32_t beaconcrypt_server_head(const struct beaconcrypt_Server *handle,
                                 struct beaconcrypt_SnapshotHeadInfo *out);

/**
 * Query whether a failed commit has fenced this owner. Returns false for null and preserves the last operation's status.
 */
bool beaconcrypt_server_is_poisoned(const struct beaconcrypt_Server *handle);

/**
 * Return the last server operation's status, or `beaconcrypt_STATUS_INVALID_ARGUMENT` for null.
 * Head, identity and poison-state queries preserve this value; checkpoint export records its own status.
 */
uint32_t beaconcrypt_server_last_status(const struct beaconcrypt_Server *handle);

/**
 * Parse a snapshot envelope and compute its exact-byte head. This does not authenticate bytes or establish freshness.
 */
uint32_t beaconcrypt_snapshot_head(const uint8_t *bytes,
                                   uintptr_t len,
                                   struct beaconcrypt_SnapshotHeadInfo *out);

/**
 * Check a snapshot's lineage, next generation and exact parent digest against `expected` (null for an empty store).
 *
 * This does not authenticate bytes or make the store atomic. A store must perform this check together with comparison against its trusted current head inside its durable compare-and-swap transaction.
 */
uint32_t beaconcrypt_snapshot_validate_successor(const uint8_t *bytes,
                                                 uintptr_t len,
                                                 const struct beaconcrypt_SnapshotHeadInfo *expected,
                                                 struct beaconcrypt_SnapshotHeadInfo *out);

/**
 * Restore a server from trusted checkpoint bytes.
 *
 * The caller must reject stale or untrusted checkpoints. These bytes are plaintext and are not cryptographically authenticated.
 *
 * Restoration advances the generation, so export and save the returned handle immediately before using it. Returns an owned handle, or null for invalid state.
 */
struct beaconcrypt_Server *beaconcrypt_server_new_from_state(const uint8_t *state_ptr,
                                                             uintptr_t state_len);

/**
 * Export the current plaintext checkpoint.
 *
 * Save it immediately after every accepted receive or other state-changing call and before using that call's output.
 * A normal rejected receive leaves the checkpoint unchanged.
 * Returns an empty buffer on failure.
 */
struct beaconcrypt_Buffer beaconcrypt_server_export_state(const struct beaconcrypt_Server *handle);

/**
 * Create a beacon bound to both server identity public keys.
 *
 * `server_pk_ptr` must point to an Ed25519 public key, and `server_mldsa_pk_ptr` must point to an ML-DSA-65 public key of `beaconcrypt_MLDSA_PUBLIC_KEY_LEN` bytes. Both pins are mandatory.
 *
 * Returns an owned handle, or null for absent or incorrectly sized input or a reported initialization/key-generation failure. Release a non-null handle with `beaconcrypt_beacon_free`.
 */
struct beaconcrypt_Beacon *beaconcrypt_beacon_new(uint64_t server_kid,
                                                  const uint8_t *server_pk_ptr,
                                                  uintptr_t server_pk_len,
                                                  const uint8_t *server_mldsa_pk_ptr,
                                                  uintptr_t server_mldsa_pk_len);

/**
 * Release a server handle created by this API.
 *
 * Passing null is allowed. The handle must not be used after this call.
 */
void beaconcrypt_server_free(struct beaconcrypt_Server *handle);

/**
 * Release a beacon handle created by this API.
 *
 * Passing null is allowed. The handle must not be used after this call.
 */
void beaconcrypt_beacon_free(struct beaconcrypt_Beacon *handle);

/**
 * Copy the server identity public key into a caller-owned buffer.
 *
 * Returns an empty buffer when `handle` is null.
 */
struct beaconcrypt_Buffer beaconcrypt_server_identity_pk(const struct beaconcrypt_Server *handle);

/**
 * Copy the beacon identity public key into a caller-owned buffer.
 *
 * Returns an empty buffer when `handle` is null.
 */
struct beaconcrypt_Buffer beaconcrypt_beacon_identity_pk(const struct beaconcrypt_Beacon *handle);

/**
 * Copy the server's ML-DSA-65 public key into a caller-owned buffer.
 * Returns an empty buffer for a null handle and preserves the last operation's status.
 */
struct beaconcrypt_Buffer beaconcrypt_server_mldsa_public_key(const struct beaconcrypt_Server *handle);

/**
 * Copy the beacon's ML-DSA-65 public key into a caller-owned buffer.
 * Returns an empty buffer for a null handle.
 */
struct beaconcrypt_Buffer beaconcrypt_beacon_mldsa_public_key(const struct beaconcrypt_Beacon *handle);

/**
 * Generate the beacon's serialized registration bundle.
 *
 * Returns an empty buffer when the handle is invalid or the beacon cannot generate a bundle in its current state.
 */
struct beaconcrypt_Buffer beaconcrypt_generate_registration(struct beaconcrypt_Beacon *handle);

/**
 * Register a beacon and build its initial server response.
 *
 * `msg_ptr` may be null when `msg_len` is zero to omit the initial message. On failure, returns an empty response with key identifier zero.
 */
struct beaconcrypt_RegistrationResponse beaconcrypt_register_beacon(struct beaconcrypt_Server *handle,
                                                                    const uint8_t *reg_ptr,
                                                                    uintptr_t reg_len,
                                                                    const uint8_t *msg_ptr,
                                                                    uintptr_t msg_len);

/**
 * Finish beacon registration and return the optional initial plaintext message.
 *
 * Returns an empty buffer when the input is invalid, registration fails, or no initial message was supplied.
 */
struct beaconcrypt_Buffer beaconcrypt_process_initial_message(struct beaconcrypt_Beacon *handle,
                                                              const uint8_t *ptr,
                                                              uintptr_t len);

/**
 * Encrypt a message from the server to the beacon identified by `key_id`.
 *
 * Returns an empty buffer when the handle or input is invalid, the key is unknown, or encryption fails.
 */
struct beaconcrypt_Buffer beaconcrypt_encrypt_to_beacon(struct beaconcrypt_Server *handle,
                                                        uint64_t key_id,
                                                        const uint8_t *ptr,
                                                        uintptr_t len);

/**
 * Decrypt a beacon-to-server message.
 *
 * Returns an empty buffer when the handle or input is invalid, authentication fails, or the ratchet rejects the message.
 */
struct beaconcrypt_Buffer beaconcrypt_decrypt_beacon_message(struct beaconcrypt_Server *handle,
                                                             const uint8_t *ptr,
                                                             uintptr_t len);

/**
 * Encrypt a server-to-beacon message and return observational ratchet metadata.
 *
 * Returns an empty `beaconcrypt_EncryptState` when the operation fails. Persist the server checkpoint before using the returned output.
 */
struct beaconcrypt_EncryptState beaconcrypt_encrypt_and_update(struct beaconcrypt_Server *handle,
                                                               uint64_t key_id,
                                                               const uint8_t *ptr,
                                                               uintptr_t len);

/**
 * Encrypt a server-to-beacon message and return the result and ratchet metadata as JSON.
 *
 * Returns an empty buffer when the operation fails. Persist the server checkpoint before using the returned output.
 */
struct beaconcrypt_Buffer beaconcrypt_encrypt_and_update_json(struct beaconcrypt_Server *handle,
                                                              uint64_t key_id,
                                                              const uint8_t *ptr,
                                                              uintptr_t len);

/**
 * Decrypt a beacon-to-server message and return observational ratchet metadata.
 *
 * Returns an empty `beaconcrypt_EncryptState` when the operation fails. Persist the server checkpoint before using the returned output.
 */
struct beaconcrypt_EncryptState beaconcrypt_decrypt_and_update(struct beaconcrypt_Server *handle,
                                                               const uint8_t *ptr,
                                                               uintptr_t len);

/**
 * Decrypt a beacon-to-server message and return the result and ratchet metadata as JSON.
 *
 * Returns an empty buffer when the operation fails. Persist the server checkpoint before using the returned output.
 */
struct beaconcrypt_Buffer beaconcrypt_decrypt_and_update_json(struct beaconcrypt_Server *handle,
                                                              const uint8_t *ptr,
                                                              uintptr_t len);

/**
 * Encrypt a message from the beacon to its server.
 *
 * Returns an empty buffer when the handle or input is invalid or encryption fails.
 */
struct beaconcrypt_Buffer beaconcrypt_encrypt_to_server(struct beaconcrypt_Beacon *handle,
                                                        const uint8_t *ptr,
                                                        uintptr_t len);

/**
 * Decrypt a server-to-beacon message.
 *
 * Returns an empty buffer when the handle or input is invalid, authentication fails, or the ratchet rejects the message.
 */
struct beaconcrypt_Buffer beaconcrypt_decrypt_server_message(struct beaconcrypt_Beacon *handle,
                                                             const uint8_t *ptr,
                                                             uintptr_t len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  /* _BEACON_CRYPT_H_ */
