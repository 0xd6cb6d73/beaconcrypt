// SPDX-License-Identifier: 0BSD

package beaconcrypt

import "fmt"

// SnapshotHead identifies the exact committed bytes of one server generation.
// Its digest identifies bytes; it does not authenticate a snapshot.
type SnapshotHead struct {
	Lineage    [32]byte
	Generation uint64
	Digest     [32]byte
}

// SnapshotStore is the authoritative storage for a persistent server.
// Load returns nil, nil when no snapshot exists. CompareAndSwap must atomically
// compare expected with the current head, validate the replacement's successor
// relationship, and durably commit its exact bytes before returning true.
// A nil expected head requires an empty store. Store callbacks must not call
// methods on the Server using that store, because its mutex remains locked.
// Snapshot bytes contain plaintext secrets and require trusted storage.
// Close store-backed servers when finished. A store that retains its Server
// prevents automatic finalization until Close releases the callback handle.
type SnapshotStore interface {
	Load() ([]byte, error)
	CompareAndSwap(expected *SnapshotHead, replacement []byte) (bool, error)
}

// PersistenceStatus is a stable status code returned by the binding.
type PersistenceStatus uint32

const (
	StatusOK PersistenceStatus = iota
	StatusRejected
	StatusInvalidArgument
	StatusMissingSnapshot
	StatusInvalidSnapshot
	StatusNonCanonicalSnapshot
	StatusStaleGeneration
	StatusGenerationExhausted
	StatusEncoding
	StatusOutputEncoding
	StatusInitialization
	StatusDigest
	StatusPoisoned
)

// PersistenceError reports a persistence failure, including an underlying store
// error when a callback supplied one. A failed commit suppresses operation output.
type PersistenceError struct {
	Code  PersistenceStatus
	Cause error
}

func (e *PersistenceError) Error() string {
	message := map[PersistenceStatus]string{
		StatusRejected:             "operation rejected",
		StatusInvalidArgument:      "invalid argument",
		StatusMissingSnapshot:      "missing snapshot",
		StatusInvalidSnapshot:      "invalid snapshot",
		StatusNonCanonicalSnapshot: "noncanonical snapshot",
		StatusStaleGeneration:      "stale snapshot generation",
		StatusGenerationExhausted:  "snapshot generation exhausted",
		StatusEncoding:             "snapshot encoding failed",
		StatusOutputEncoding:       "output encoding failed",
		StatusInitialization:       "initialization failed",
		StatusDigest:               "snapshot digest failed",
		StatusPoisoned:             "persistent server is poisoned",
	}[e.Code]
	if message == "" {
		message = fmt.Sprintf("persistence status %d", e.Code)
	}
	if e.Cause != nil {
		return "beaconcrypt: " + message + ": " + e.Cause.Error()
	}
	return "beaconcrypt: " + message
}

func (e *PersistenceError) Unwrap() error { return e.Cause }
