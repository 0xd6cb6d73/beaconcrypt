// SPDX-License-Identifier: 0BSD

package beaconcrypt

/*
#include "beaconcrypt_go.h"
*/
import "C"

import (
	"errors"
	"fmt"
	"runtime/cgo"
	"sync"
	"unsafe"
)

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

// PersistenceStatus is a stable status code returned by the native API.
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

type snapshotStoreContext struct {
	store  SnapshotStore
	handle cgo.Handle
	mu     sync.Mutex
	err    error
}

func newSnapshotStoreContext(store SnapshotStore) *snapshotStoreContext {
	context := &snapshotStoreContext{store: store}
	context.handle = cgo.NewHandle(context)
	return context
}

func (context *snapshotStoreContext) setError(err error) {
	if err == nil {
		return
	}
	context.mu.Lock()
	defer context.mu.Unlock()
	if context.err == nil {
		context.err = err
	}
}

func (context *snapshotStoreContext) takeError() error {
	if context == nil {
		return nil
	}
	context.mu.Lock()
	defer context.mu.Unlock()
	err := context.err
	context.err = nil
	return err
}

// NewServerWithStore creates and commits generation zero before returning.
// An empty seed selects a random identity; a nonempty seed must be 32 bytes.
func NewServerWithStore(serverKID uint64, seed []byte, store SnapshotStore) (*Server, error) {
	return newServerWithStore(serverKID, seed, store, nil)
}

// NewServerWithStoreAndLineage uses an externally allocated lineage.
// Each lineage must belong to exactly one authoritative storage domain.
func NewServerWithStoreAndLineage(serverKID uint64, seed []byte, store SnapshotStore, lineage [32]byte) (*Server, error) {
	return newServerWithStore(serverKID, seed, store, &lineage)
}

func newServerWithStore(serverKID uint64, seed []byte, store SnapshotStore, lineage *[32]byte) (*Server, error) {
	if store == nil {
		return nil, &PersistenceError{Code: StatusInvalidArgument}
	}
	if len(seed) != 0 && len(seed) != 32 {
		return nil, ErrSeedSize
	}
	context := newSnapshotStoreContext(store)
	return createServerWithStoreContext(serverKID, seed, context, lineage)
}

func createServerWithStoreContext(serverKID uint64, seed []byte, context *snapshotStoreContext, lineage *[32]byte) (*Server, error) {
	seedPtr, freeSeed := cBytes(seed)
	defer freeSeed()
	var status C.uint32_t
	var handle *C.beaconcrypt_Server
	if lineage == nil {
		handle = C.beaconcrypt_go_server_create_with_store(C.uint64_t(serverKID), seedPtr, C.uintptr_t(len(seed)), C.uintptr_t(context.handle), &status)
	} else {
		lineagePtr, freeLineage := cBytes(lineage[:])
		defer freeLineage()
		handle = C.beaconcrypt_go_server_create_with_store_and_lineage(C.uint64_t(serverKID), seedPtr, C.uintptr_t(len(seed)), C.uintptr_t(context.handle), lineagePtr, 32, &status)
	}
	if handle == nil {
		return nil, &PersistenceError{Code: PersistenceStatus(status), Cause: context.takeError()}
	}
	native := newServerNativeHandle(handle)
	native.store = context
	return &Server{native: native}, nil
}

// RestoreServer loads the trusted current snapshot and commits its next
// generation before activating a server. Competing owners must share one store.
func RestoreServer(store SnapshotStore) (*Server, error) {
	if store == nil {
		return nil, &PersistenceError{Code: StatusInvalidArgument}
	}
	context := newSnapshotStoreContext(store)
	return restoreServerWithStoreContext(context)
}

func restoreServerWithStoreContext(context *snapshotStoreContext) (*Server, error) {
	var status C.uint32_t
	handle := C.beaconcrypt_go_server_restore_with_store(C.uintptr_t(context.handle), &status)
	if handle == nil {
		return nil, &PersistenceError{Code: PersistenceStatus(status), Cause: context.takeError()}
	}
	native := newServerNativeHandle(handle)
	native.store = context
	return &Server{native: native}, nil
}

// Head returns the currently committed generation and exact snapshot identity.
func (s *Server) Head() (SnapshotHead, error) {
	if s == nil {
		return SnapshotHead{}, ErrClosed
	}
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) (SnapshotHead, error) {
		var head C.beaconcrypt_SnapshotHeadInfo
		status := C.beaconcrypt_server_head(handle, &head)
		if status != 0 {
			return SnapshotHead{}, &PersistenceError{Code: PersistenceStatus(status)}
		}
		return snapshotHeadFromC(&head), nil
	})
}

// IsPoisoned reports whether a failed commit has disabled the server.
// It also returns true for a closed or absent handle.
func (s *Server) IsPoisoned() bool {
	if s == nil {
		return true
	}
	poisoned, err := withServerHandle(s.native, func(handle *C.beaconcrypt_Server) (bool, error) {
		return bool(C.beaconcrypt_server_is_poisoned(handle)), nil
	})
	return err != nil || poisoned
}

// ParseSnapshotHead parses the envelope and computes its exact-byte digest.
// It does not authenticate the snapshot or activate its protocol state.
func ParseSnapshotHead(snapshot []byte) (SnapshotHead, error) {
	return inspectSnapshot(snapshot, nil, false)
}

// ValidateSnapshotSuccessor validates the lineage, next generation and parent
// digest against expected. A nil expected requires generation zero. The store
// must separately compare expected with its trusted head in the same transaction.
func ValidateSnapshotSuccessor(snapshot []byte, expected *SnapshotHead) (SnapshotHead, error) {
	return inspectSnapshot(snapshot, expected, true)
}

func inspectSnapshot(snapshot []byte, expected *SnapshotHead, successor bool) (SnapshotHead, error) {
	ptr, free := cBytes(snapshot)
	defer free()
	var head C.beaconcrypt_SnapshotHeadInfo
	var status C.uint32_t
	if successor {
		var nativeExpected C.beaconcrypt_SnapshotHeadInfo
		var expectedPtr *C.beaconcrypt_SnapshotHeadInfo
		if expected != nil {
			nativeExpected = snapshotHeadToC(*expected)
			expectedPtr = &nativeExpected
		}
		status = C.beaconcrypt_snapshot_validate_successor(ptr, C.uintptr_t(len(snapshot)), expectedPtr, &head)
	} else {
		status = C.beaconcrypt_snapshot_head(ptr, C.uintptr_t(len(snapshot)), &head)
	}
	if status != 0 {
		return SnapshotHead{}, &PersistenceError{Code: PersistenceStatus(status)}
	}
	return snapshotHeadFromC(&head), nil
}

func snapshotHeadFromC(head *C.beaconcrypt_SnapshotHeadInfo) SnapshotHead {
	var result SnapshotHead
	result.Generation = uint64(head.generation)
	for i := 0; i < 32; i++ {
		result.Lineage[i] = byte(head.lineage[i])
		result.Digest[i] = byte(head.digest[i])
	}
	return result
}

func snapshotHeadToC(head SnapshotHead) C.beaconcrypt_SnapshotHeadInfo {
	var result C.beaconcrypt_SnapshotHeadInfo
	result.generation = C.uint64_t(head.Generation)
	for i := 0; i < 32; i++ {
		result.lineage[i] = C.uint8_t(head.Lineage[i])
		result.digest[i] = C.uint8_t(head.Digest[i])
	}
	return result
}

func withServerMutation[T any](native *serverNativeHandle, call func(*C.beaconcrypt_Server) (T, error)) (T, error) {
	return withServerHandle(native, func(handle *C.beaconcrypt_Server) (T, error) {
		native.store.takeError()
		result, err := call(handle)
		if errors.Is(err, ErrEmptyData) {
			return result, err
		}
		status := PersistenceStatus(C.beaconcrypt_server_last_status(handle))
		cause := native.store.takeError()
		if status != StatusOK && status != StatusRejected {
			var zero T
			return zero, &PersistenceError{Code: status, Cause: cause}
		}
		return result, err
	})
}

func callbackBytes(ptr *C.uint8_t, length C.uintptr_t) ([]byte, error) {
	if uint64(length) > uint64(^uint(0)>>1) || (ptr == nil && length != 0) {
		return nil, errors.New("invalid snapshot callback buffer")
	}
	return append([]byte(nil), unsafe.Slice((*byte)(unsafe.Pointer(ptr)), int(length))...), nil
}

//export beaconcryptGoStoreLoad
func beaconcryptGoStoreLoad(token C.uintptr_t, delivery unsafe.Pointer) (ok C.bool) {
	var context *snapshotStoreContext
	defer func() {
		if problem := recover(); problem != nil {
			if context != nil {
				context.setError(fmt.Errorf("snapshot store Load panic: %v", problem))
			}
			ok = false
		}
	}()
	context = cgo.Handle(token).Value().(*snapshotStoreContext)
	snapshot, err := context.store.Load()
	if err != nil {
		context.setError(err)
		return false
	}
	if snapshot == nil {
		return false
	}
	ptr, free := cBytes(snapshot)
	defer free()
	C.beaconcrypt_go_deliver_snapshot(delivery, ptr, C.uintptr_t(len(snapshot)))
	return true
}

//export beaconcryptGoStoreCompareAndSwap
func beaconcryptGoStoreCompareAndSwap(token C.uintptr_t, expected *C.beaconcrypt_SnapshotHeadInfo, bytes *C.uint8_t, length C.uintptr_t) (ok C.bool) {
	var context *snapshotStoreContext
	defer func() {
		if problem := recover(); problem != nil {
			if context != nil {
				context.setError(fmt.Errorf("snapshot store CompareAndSwap panic: %v", problem))
			}
			ok = false
		}
	}()
	context = cgo.Handle(token).Value().(*snapshotStoreContext)
	replacement, err := callbackBytes(bytes, length)
	if err != nil {
		context.setError(err)
		return false
	}
	var previous *SnapshotHead
	if expected != nil {
		head := snapshotHeadFromC(expected)
		previous = &head
	}
	accepted, err := context.store.CompareAndSwap(previous, replacement)
	if err != nil {
		context.setError(err)
		return false
	}
	return C.bool(accepted)
}

//export beaconcryptGoStoreDestroy
func beaconcryptGoStoreDestroy(token C.uintptr_t) {
	defer func() { _ = recover() }()
	cgo.Handle(token).Delete()
}
