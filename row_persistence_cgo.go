// SPDX-License-Identifier: 0BSD
//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

/*
#include "beaconcrypt_row_go.h"
*/
import "C"

import (
	"errors"
	"fmt"
	"runtime"
	"runtime/cgo"
	"sync"
	"unsafe"
)

// RowServer operates on individual peers in an application database. Calls on
// one handle are serialized; independent handles can share the database.
// Close releases callbacks. A store retaining its server requires explicit Close.
type RowServer struct{ native *rowNative }
type rowNative struct {
	mu     sync.Mutex
	handle *C.beaconcrypt_RowServerHandle
	store  *rowContext
}
type rowContext struct {
	store RowStore
	err   error
}

func rowCreate(kid uint64, seed, mldsa []byte, store RowStore, lineage [32]byte, open bool) (*RowServer, error) {
	if store == nil {
		return nil, &PersistenceError{Code: StatusInvalidArgument}
	}
	if (len(seed) != 0 && len(seed) != 32) || (len(mldsa) != 0 && len(mldsa) != 32) {
		return nil, ErrSeedSize
	}
	context := &rowContext{store: store}
	token := cgo.NewHandle(context)
	seedPtr, freeSeed := cBytes(seed)
	defer freeSeed()
	mldsaPtr, freeMLDSA := cBytes(mldsa)
	defer freeMLDSA()
	lineagePtr, freeLineage := cBytes(lineage[:])
	defer freeLineage()
	var status C.uint32_t
	var handle *C.beaconcrypt_RowServerHandle
	if open {
		handle = C.beaconcrypt_go_row_open(C.uintptr_t(token), lineagePtr, &status)
	} else {
		handle = C.beaconcrypt_go_row_create(C.uint64_t(kid), seedPtr, C.uintptr_t(len(seed)), mldsaPtr, C.uintptr_t(len(mldsa)), C.uintptr_t(token), lineagePtr, &status)
	}
	if handle == nil {
		return nil, &PersistenceError{Code: PersistenceStatus(status), Cause: context.err}
	}
	native := &rowNative{handle: handle, store: context}
	runtime.SetFinalizer(native, (*rowNative).close)
	return &RowServer{native: native}, nil
}

// NewRowServer creates a namespace and commits its identity and allocator.
func NewRowServer(kid uint64, seed, mldsaSeed []byte, store RowStore, lineage [32]byte) (*RowServer, error) {
	return rowCreate(kid, seed, mldsaSeed, store, lineage, false)
}

// OpenRowServer opens an existing namespace without loading any peer state.
func OpenRowServer(store RowStore, lineage [32]byte) (*RowServer, error) {
	return rowCreate(0, nil, nil, store, lineage, true)
}

func (n *rowNative) close() {
	n.mu.Lock()
	defer n.mu.Unlock()
	if n.handle != nil {
		C.beaconcrypt_row_server_free(n.handle)
		n.handle = nil
		n.store = nil
	}
}

func (s *RowServer) Close() {
	if s != nil && s.native != nil {
		s.native.close()
	}
}

func rowCall[T any](s *RowServer, mutation bool, call func(*C.beaconcrypt_RowServerHandle) (T, error)) (T, error) {
	var zero T
	if s == nil || s.native == nil {
		return zero, ErrClosed
	}
	n := s.native
	n.mu.Lock()
	defer n.mu.Unlock()
	if n.handle == nil {
		return zero, ErrClosed
	}
	n.store.err = nil
	value, err := call(n.handle)
	if errors.Is(err, ErrEmptyData) {
		return value, err
	}
	if mutation {
		status := PersistenceStatus(C.beaconcrypt_row_server_last_status(n.handle))
		if status != StatusOK && status != StatusRejected {
			return zero, &PersistenceError{Code: status, Cause: n.store.err}
		}
	}
	runtime.KeepAlive(n)
	return value, err
}

func (s *RowServer) IdentityPK() ([]byte, error) {
	return rowCall(s, false, func(handle *C.beaconcrypt_RowServerHandle) ([]byte, error) {
		return copyBuffer(C.beaconcrypt_row_server_identity_pk(handle))
	})
}
func (s *RowServer) MLDSAPublicKey() ([]byte, error) {
	return rowCall(s, false, func(handle *C.beaconcrypt_RowServerHandle) ([]byte, error) {
		return copyBuffer(C.beaconcrypt_row_server_mldsa_public_key(handle))
	})
}

// RegisterBeacon uses a nil initialMessage for the protocol witness. A non-nil empty slice consumes the accepted registration but rejects its empty response payload.
func (s *RowServer) RegisterBeacon(registration, initialMessage []byte) (*RegistrationResponse, error) {
	return rowCall(s, true, func(handle *C.beaconcrypt_RowServerHandle) (*RegistrationResponse, error) {
		if len(registration) == 0 {
			return nil, ErrEmptyData
		}
		reg, freeReg := cBytes(registration)
		defer freeReg()
		messageBytes := initialMessage
		if initialMessage != nil && len(initialMessage) == 0 {
			messageBytes = []byte{0}
		}
		msg, freeMsg := cBytes(messageBytes)
		defer freeMsg()
		value := C.beaconcrypt_row_server_register(handle, reg, C.uintptr_t(len(registration)), msg, C.uintptr_t(len(initialMessage)))
		data, err := copyBuffer(value.response)
		if err != nil {
			return nil, err
		}
		return &RegistrationResponse{Serialized: data, KeyID: uint64(value.key_id)}, nil
	})
}
func (s *RowServer) EncryptToBeacon(kid uint64, data []byte) ([]byte, error) {
	return rowCall(s, true, func(handle *C.beaconcrypt_RowServerHandle) ([]byte, error) {
		if len(data) == 0 {
			return nil, ErrEmptyData
		}
		ptr, free := cBytes(data)
		defer free()
		return copyBuffer(C.beaconcrypt_row_server_encrypt(handle, ptr, C.uintptr_t(len(data)), C.uint64_t(kid)))
	})
}
func (s *RowServer) DecryptBeaconMessage(data []byte) ([]byte, error) {
	return rowCall(s, true, func(handle *C.beaconcrypt_RowServerHandle) ([]byte, error) {
		if len(data) == 0 {
			return nil, ErrEmptyData
		}
		ptr, free := cBytes(data)
		defer free()
		return copyBuffer(C.beaconcrypt_row_server_decrypt(handle, ptr, C.uintptr_t(len(data))))
	})
}

func callbackRow(token C.uintptr_t, operation func(*rowContext) error) (ok C.bool) {
	var context *rowContext
	defer func() {
		if problem := recover(); problem != nil {
			if context != nil && context.err == nil {
				context.err = fmt.Errorf("row store callback panic: %v", problem)
			}
			ok = false
		}
	}()
	context = cgo.Handle(token).Value().(*rowContext)
	if err := operation(context); err != nil {
		if context.err == nil {
			context.err = err
		}
		return false
	}
	return true
}

//export beaconcryptGoRowBegin
func beaconcryptGoRowBegin(token C.uintptr_t) C.bool {
	return callbackRow(token, func(c *rowContext) error { return c.store.Begin() })
}

//export beaconcryptGoRowCommit
func beaconcryptGoRowCommit(token C.uintptr_t) C.bool {
	return callbackRow(token, func(c *rowContext) error { return c.store.Commit() })
}

//export beaconcryptGoRowRollback
func beaconcryptGoRowRollback(token C.uintptr_t) {
	callbackRow(token, func(c *rowContext) error { return c.store.Rollback() })
}

//export beaconcryptGoRowDestroy
func beaconcryptGoRowDestroy(token C.uintptr_t) { cgo.Handle(token).Delete() }

//export beaconcryptGoRowLoad
func beaconcryptGoRowLoad(token C.uintptr_t, key *C.uint8_t, keyLen C.uintptr_t, delivery unsafe.Pointer) C.int32_t {
	present := false
	ok := callbackRow(token, func(c *rowContext) error {
		keyBytes, err := callbackBytes(key, keyLen)
		if err != nil {
			return err
		}
		value, err := c.store.Load(keyBytes)
		if err != nil {
			return err
		}
		if value == nil {
			return nil
		}
		ptr, free := cBytes(value)
		defer free()
		C.beaconcrypt_go_deliver_row(delivery, ptr, C.uintptr_t(len(value)))
		present = true
		return nil
	})
	if !bool(ok) {
		return -1
	}
	if present {
		return 1
	}
	return 0
}

//export beaconcryptGoRowStore
func beaconcryptGoRowStore(token C.uintptr_t, key *C.uint8_t, keyLen C.uintptr_t, value *C.uint8_t, valueLen C.uintptr_t) C.bool {
	return callbackRow(token, func(c *rowContext) error {
		keyBytes, err := callbackBytes(key, keyLen)
		if err != nil {
			return err
		}
		valueBytes, err := callbackBytes(value, valueLen)
		if err != nil {
			return err
		}
		return c.store.Store(keyBytes, valueBytes)
	})
}
