// SPDX-License-Identifier: 0BSD
//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

/*
#include "beaconcrypt_row_go.h"
*/
import "C"

import (
	"fmt"
	"runtime/cgo"
	"sync"
	"sync/atomic"
	"unsafe"
)

// RowSession exists only during a Transaction or RegistrationTransaction callback.
// Load and Store use application keys isolated from native records. Native message
// outputs are pending; the trusted callback must not publish them or perform other
// irreversible side effects before its outer server call succeeds. A session
// allows zero or one native attempt, including rejection. Any method error aborts
// its transaction even if the callback ignores the error. Use the session only
// synchronously on the callback goroutine; concurrent or recursive session calls
// are rejected. Do not reenter its server (whose mutex remains held).
type RowSession struct{ state *rowSessionState }
type rowSessionState struct {
	mu      sync.Mutex
	invalid atomic.Bool
	handle  *C.beaconcrypt_RowSessionHandle
	store   *rowContext
}

type rowOperationContext struct {
	store     *rowContext
	operation func(*RowSession) ([]byte, error)
	accept    func(*RowSession) (RowRegistrationDecision, error)
	complete  func(*RowSession, []byte) ([]byte, error)
}

// Transaction commits application rows and at most one native message transition
// atomically, then returns the callback's opaque result bytes. Callback errors and
// uncertain commits return no result. The callback must not publish pending data.
func (s *RowServer) Transaction(operation func(*RowSession) ([]byte, error)) ([]byte, error) {
	return rowCall(s, false, func(handle *C.beaconcrypt_RowServerHandle) ([]byte, error) {
		if operation == nil {
			return nil, &PersistenceError{Code: StatusInvalidArgument}
		}
		context := &rowOperationContext{store: s.native.store, operation: operation}
		token := cgo.NewHandle(context)
		defer token.Delete()
		buffer := C.beaconcrypt_go_row_transaction(handle, C.uintptr_t(token))
		return rowOperationOutput(handle, buffer, context.store)
	})
}

// RegistrationTransaction composes two durable registration phases. Accept may
// return cached bytes, or call AcceptRegistration and return Continue with opaque
// context bytes. Complete runs only after acceptance commits and can call
// CompleteRegistration once. A completion failure retains the acceptance marker
// and application records from the first commit. Lookup those records to resolve
// incomplete or uncertain outcomes; no request-ID or retry policy is built in.
func (s *RowServer) RegistrationTransaction(
	accept func(*RowSession) (RowRegistrationDecision, error),
	complete func(*RowSession, []byte) ([]byte, error),
) ([]byte, error) {
	return rowCall(s, false, func(handle *C.beaconcrypt_RowServerHandle) ([]byte, error) {
		if accept == nil || complete == nil {
			return nil, &PersistenceError{Code: StatusInvalidArgument}
		}
		context := &rowOperationContext{store: s.native.store, accept: accept, complete: complete}
		token := cgo.NewHandle(context)
		defer token.Delete()
		var phase C.uint32_t
		buffer := C.beaconcrypt_go_row_registration_transaction(handle, C.uintptr_t(token), &phase)
		output, err := rowOperationOutput(handle, buffer, context.store)
		if err != nil {
			return nil, &RowRegistrationError{Phase: RowRegistrationPhase(phase), Cause: err}
		}
		return output, nil
	})
}

func rowOperationOutput(handle *C.beaconcrypt_RowServerHandle, buffer C.beaconcrypt_Buffer, store *rowContext) ([]byte, error) {
	status := PersistenceStatus(C.beaconcrypt_row_server_last_status(handle))
	if status != StatusOK {
		C.beaconcrypt_free_buffer(buffer)
		return nil, &PersistenceError{Code: status, Cause: store.err}
	}
	return copyBuffer(buffer)
}

func rowSessionCall[T any](session *RowSession, operation func(*rowSessionState) (T, error)) (T, error) {
	var zero T
	if session == nil || session.state == nil {
		return zero, ErrRowSessionExpired
	}
	state := session.state
	if !state.mu.TryLock() {
		state.invalid.Store(true)
		return zero, &PersistenceError{Code: StatusInvalidSession}
	}
	defer state.mu.Unlock()
	if state.handle == nil {
		return zero, ErrRowSessionExpired
	}
	if state.invalid.Load() {
		return zero, &PersistenceError{Code: StatusInvalidSession}
	}
	return operation(state)
}
func rowSessionError(state *rowSessionState) error {
	status := PersistenceStatus(C.beaconcrypt_row_session_last_status(state.handle))
	if status == StatusOK || status == StatusRejected {
		return nil
	}
	return &PersistenceError{Code: status, Cause: state.store.err}
}

func (s *RowSession) Load(key []byte) ([]byte, error) {
	return rowSessionCall(s, func(state *rowSessionState) ([]byte, error) {
		keyPtr, free := cBytes(key)
		defer free()
		buffer := C.beaconcrypt_row_session_load(state.handle, keyPtr, C.uintptr_t(len(key)))
		if err := rowSessionError(state); err != nil {
			C.beaconcrypt_free_buffer(buffer)
			return nil, err
		}
		if buffer.ptr == nil {
			return nil, nil
		}
		return copyBuffer(buffer)
	})
}
func (s *RowSession) Store(key, value []byte) error {
	_, err := rowSessionCall(s, func(state *rowSessionState) (struct{}, error) {
		keyPtr, freeKey := cBytes(key)
		defer freeKey()
		valuePtr, freeValue := cBytes(value)
		defer freeValue()
		C.beaconcrypt_row_session_store(state.handle, keyPtr, C.uintptr_t(len(key)), valuePtr, C.uintptr_t(len(value)))
		return struct{}{}, rowSessionError(state)
	})
	return err
}
func rowSessionTransition(state *rowSessionState, value C.beaconcrypt_RowTransitionBuffer) (*RowTransition, error) {
	if err := rowSessionError(state); err != nil {
		C.beaconcrypt_free_buffer(value.message.data)
		return nil, err
	}
	result := &RowTransition{Changed: bool(value.changed)}
	if value.message.data.ptr != nil {
		message, err := copyRowMessage(value.message)
		if err != nil {
			return nil, err
		}
		result.Message = message
	}
	return result, nil
}
func (s *RowSession) EncryptToBeacon(kid uint64, data []byte) (*RowTransition, error) {
	return rowSessionCall(s, func(state *rowSessionState) (*RowTransition, error) {
		ptr, free := cBytes(data)
		defer free()
		return rowSessionTransition(state, C.beaconcrypt_row_session_encrypt(state.handle, ptr, C.uintptr_t(len(data)), C.uint64_t(kid)))
	})
}
func (s *RowSession) DecryptBeaconMessage(data []byte) (*RowTransition, error) {
	return rowSessionCall(s, func(state *rowSessionState) (*RowTransition, error) {
		ptr, free := cBytes(data)
		defer free()
		return rowSessionTransition(state, C.beaconcrypt_row_session_decrypt(state.handle, ptr, C.uintptr_t(len(data))))
	})
}
func (s *RowSession) AcceptRegistration(data []byte) (bool, error) {
	return rowSessionCall(s, func(state *rowSessionState) (bool, error) {
		ptr, free := cBytes(data)
		defer free()
		accepted := bool(C.beaconcrypt_row_session_accept_registration(state.handle, ptr, C.uintptr_t(len(data))))
		return accepted, rowSessionError(state)
	})
}
func (s *RowSession) CompleteRegistration(initialMessage []byte) (*RowTransition, error) {
	return rowSessionCall(s, func(state *rowSessionState) (*RowTransition, error) {
		message := initialMessage
		if initialMessage != nil && len(initialMessage) == 0 {
			message = []byte{0}
		}
		ptr, free := cBytes(message)
		defer free()
		return rowSessionTransition(state, C.beaconcrypt_row_session_complete_registration(state.handle, ptr, C.uintptr_t(len(initialMessage))))
	})
}

func withRowOperation(token C.uintptr_t, handle *C.beaconcrypt_RowSessionHandle, operation func(*rowOperationContext, *RowSession) error) (ok C.bool) {
	var context *rowOperationContext
	var state *rowSessionState
	var failure error
	defer func() {
		problem := recover()
		if state != nil {
			// Finish any active call before invalidating the pointer or inspecting its cause.
			state.mu.Lock()
			defer state.mu.Unlock()
			state.handle = nil
			if state.invalid.Load() && failure == nil {
				failure = &PersistenceError{Code: StatusInvalidSession}
			}
		}
		if problem != nil {
			failure = fmt.Errorf("row transaction callback panic: %v", problem)
		}
		if failure != nil {
			if context != nil && context.store.err == nil {
				context.store.err = failure
			}
			ok = false
		}
	}()
	context = cgo.Handle(token).Value().(*rowOperationContext)
	state = &rowSessionState{handle: handle, store: context.store}
	failure = operation(context, &RowSession{state: state})
	return failure == nil
}
func deliverRowOutput(delivery unsafe.Pointer, output []byte) {
	ptr, free := cBytes(output)
	defer free()
	C.beaconcrypt_go_deliver_row(delivery, ptr, C.uintptr_t(len(output)))
}

//export beaconcryptGoRowTransaction
func beaconcryptGoRowTransaction(token C.uintptr_t, session *C.beaconcrypt_RowSessionHandle, delivery unsafe.Pointer) C.bool {
	return withRowOperation(token, session, func(context *rowOperationContext, session *RowSession) error {
		output, err := context.operation(session)
		if err != nil {
			return err
		}
		deliverRowOutput(delivery, output)
		return nil
	})
}

//export beaconcryptGoRowAcceptance
func beaconcryptGoRowAcceptance(token C.uintptr_t, session *C.beaconcrypt_RowSessionHandle, delivery unsafe.Pointer) C.int32_t {
	var decision C.int32_t
	ok := withRowOperation(token, session, func(context *rowOperationContext, session *RowSession) error {
		output, err := context.accept(session)
		if err != nil {
			return err
		}
		if output.Continue {
			decision = 1
		}
		deliverRowOutput(delivery, output.Data)
		return nil
	})
	if !bool(ok) {
		return -1
	}
	return decision
}

//export beaconcryptGoRowCompletion
func beaconcryptGoRowCompletion(token C.uintptr_t, session *C.beaconcrypt_RowSessionHandle, accepted *C.uint8_t, acceptedLen C.uintptr_t, delivery unsafe.Pointer) C.bool {
	return withRowOperation(token, session, func(context *rowOperationContext, session *RowSession) error {
		input, err := callbackBytes(accepted, acceptedLen)
		if err != nil {
			return err
		}
		output, err := context.complete(session, input)
		if err != nil {
			return err
		}
		deliverRowOutput(delivery, output)
		return nil
	})
}
