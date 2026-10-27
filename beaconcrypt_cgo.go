// SPDX-License-Identifier: 0BSD

//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

/*
#cgo CFLAGS: -I${SRCDIR}/beaconcrypt
#cgo windows LDFLAGS: -L${SRCDIR}/target/x86_64-pc-windows-gnu/release -l:libbeaconcrypt.a -lbcrypt -lws2_32 -luserenv -ldbghelp -lntdll
#cgo linux LDFLAGS: -L${SRCDIR}/target/release -l:libbeaconcrypt.a
#cgo darwin LDFLAGS: ${SRCDIR}/target/release/libbeaconcrypt.a
#include "beaconcrypt_go.h"
*/
import "C"

import (
	"runtime"
	"sync"
)

// Keep the backend-independent public constant tied to the native ABI.
const _ = uint(MaxMessageSize - int(C.beaconcrypt_MAX_MESSAGE_SIZE))
const _ = uint(int(C.beaconcrypt_MAX_MESSAGE_SIZE) - MaxMessageSize)
const _ = uint(MLDSA65PublicKeySize - int(C.beaconcrypt_MLDSA_PUBLIC_KEY_LEN))
const _ = uint(int(C.beaconcrypt_MLDSA_PUBLIC_KEY_LEN) - MLDSA65PublicKeySize)

type serverNativeHandle struct {
	mu     sync.Mutex
	handle *C.beaconcrypt_Server
	store  *snapshotStoreContext
}
type beaconNativeHandle struct {
	mu     sync.Mutex
	handle *C.beaconcrypt_Beacon
}

func NewServer(serverKID uint64) (*Server, error) {
	handle := C.beaconcrypt_server_new(C.uint64_t(serverKID))
	if handle == nil {
		return nil, ErrCrypto
	}
	server := &Server{native: newServerNativeHandle(handle)}
	return server, nil
}

func NewServerFromSeed(serverKID uint64, seed, mldsaSeed []byte) (*Server, error) {
	if len(seed) != 32 || len(mldsaSeed) != 32 {
		return nil, ErrSeedSize
	}
	ptr, free := cBytes(seed)
	defer free()
	mldsaPtr, mldsaFree := cBytes(mldsaSeed)
	defer mldsaFree()
	handle := C.beaconcrypt_server_new_from_seed(C.uint64_t(serverKID), ptr, C.uintptr_t(len(seed)), mldsaPtr, C.uintptr_t(len(mldsaSeed)))
	if handle == nil {
		return nil, ErrCrypto
	}
	server := &Server{native: newServerNativeHandle(handle)}
	return server, nil
}

// NewServerFromState restores trusted plaintext checkpoint bytes.
//
// The caller must reject stale or untrusted checkpoints. The bytes do not
// authenticate themselves and cannot detect rollback to an older export.
// Restoration advances the generation, so call ExportState and save the
// returned server immediately before using it.
func NewServerFromState(state []byte) (*Server, error) {
	if len(state) == 0 {
		return nil, ErrEmptyData
	}
	ptr, free := cBytes(state)
	defer free()
	handle := C.beaconcrypt_server_new_from_state(ptr, C.uintptr_t(len(state)))
	if handle == nil {
		return nil, ErrCrypto
	}
	return &Server{native: newServerNativeHandle(handle)}, nil
}

// ExportState returns the current plaintext server checkpoint. A store-backed
// server loads its already committed snapshot from its authoritative store.
//
// Save it immediately after every accepted receive or other state-changing call and before using that call's output.
// A normal rejected receive leaves the checkpoint unchanged.
// A standalone exported checkpoint does not prevent rollback.
func (s *Server) ExportState() ([]byte, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) ([]byte, error) {
		return copyBuffer(C.beaconcrypt_server_export_state(handle))
	})
}

func NewBeacon(serverKID uint64, serverPK, serverMLDSAPK []byte) (*Beacon, error) {
	if len(serverPK) != 32 || len(serverMLDSAPK) != MLDSA65PublicKeySize {
		return nil, ErrCrypto
	}
	ptr, free := cBytes(serverPK)
	defer free()
	mldsaPtr, mldsaFree := cBytes(serverMLDSAPK)
	defer mldsaFree()
	handle := C.beaconcrypt_beacon_new(C.uint64_t(serverKID), ptr, C.uintptr_t(len(serverPK)), mldsaPtr, C.uintptr_t(len(serverMLDSAPK)))
	if handle == nil {
		return nil, ErrCrypto
	}
	beacon := &Beacon{native: newBeaconNativeHandle(handle)}
	return beacon, nil
}

func (s *Server) Close() {
	if s == nil {
		return
	}
	s.native.close()
}

func (b *Beacon) Close() {
	if b == nil {
		return
	}
	b.native.close()
}

func (s *Server) IdentityPK() ([]byte, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) ([]byte, error) {
		return copyBuffer(C.beaconcrypt_server_identity_pk(handle))
	})
}

// MLDSAPublicKey returns the server authentication key to provision into beacons.
func (s *Server) MLDSAPublicKey() ([]byte, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) ([]byte, error) {
		return copyBuffer(C.beaconcrypt_server_mldsa_public_key(handle))
	})
}

// MLDSAPublicKey returns the beacon's ML-DSA-65 authentication key.
func (b *Beacon) MLDSAPublicKey() ([]byte, error) {
	if b == nil {
		return nil, ErrClosed
	}
	return withBeaconHandle(b.native, func(handle *C.beaconcrypt_Beacon) ([]byte, error) {
		return copyBuffer(C.beaconcrypt_beacon_mldsa_public_key(handle))
	})
}

func (b *Beacon) GenerateRegistration() ([]byte, error) {
	if b == nil {
		return nil, ErrClosed
	}
	return withBeaconHandle(b.native, func(handle *C.beaconcrypt_Beacon) ([]byte, error) {
		return copyBuffer(C.beaconcrypt_generate_registration(handle))
	})
}

func (s *Server) RegisterBeacon(registration, initialMessage []byte) (*RegistrationResponse, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) (*RegistrationResponse, error) {
		if len(registration) == 0 {
			return nil, ErrEmptyData
		}
		regPtr, regFree := cBytes(registration)
		defer regFree()
		msgPtr, msgFree := cBytes(initialMessage)
		defer msgFree()
		response := C.beaconcrypt_register_beacon(
			handle,
			regPtr,
			C.uintptr_t(len(registration)),
			msgPtr,
			C.uintptr_t(len(initialMessage)),
		)
		serialized, err := copyBuffer(response.response)
		if err != nil {
			return nil, err
		}
		return &RegistrationResponse{
			Serialized: serialized,
			KeyID:      uint64(response.key_id),
		}, nil
	})
}

func (b *Beacon) ProcessInitialMessage(data []byte) ([]byte, error) {
	if b == nil {
		return nil, ErrClosed
	}
	return withBeaconHandle(b.native, func(handle *C.beaconcrypt_Beacon) ([]byte, error) {
		return callUnary(data, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_buffer {
			return C.beaconcrypt_process_initial_message(handle, ptr, len)
		})
	})
}

func (s *Server) EncryptToBeacon(keyID uint64, plaintext []byte) ([]byte, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) ([]byte, error) {
		return callUnary(plaintext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_buffer {
			return C.beaconcrypt_encrypt_to_beacon(handle, C.uint64_t(keyID), ptr, len)
		})
	})
}

func (s *Server) DecryptBeaconMessage(ciphertext []byte) ([]byte, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) ([]byte, error) {
		return callUnary(ciphertext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_buffer {
			return C.beaconcrypt_decrypt_beacon_message(handle, ptr, len)
		})
	})
}

func (s *Server) EncryptAndUpdate(keyID uint64, plaintext []byte) (*EncryptState, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) (*EncryptState, error) {
		return callStateUpdate(plaintext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_encrypt_state {
			return C.beaconcrypt_encrypt_and_update(handle, C.uint64_t(keyID), ptr, len)
		})
	})
}

func (s *Server) EncryptAndUpdateJSON(keyID uint64, plaintext []byte) (string, error) {
	if s == nil {
		return "", ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) (string, error) {
		data, err := callUnary(plaintext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_buffer {
			return C.beaconcrypt_encrypt_and_update_json(handle, C.uint64_t(keyID), ptr, len)
		})
		if err != nil {
			return "", err
		}
		return string(data), nil
	})
}

func (s *Server) DecryptAndUpdate(ciphertext []byte) (*EncryptState, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) (*EncryptState, error) {
		return callStateUpdate(ciphertext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_encrypt_state {
			return C.beaconcrypt_decrypt_and_update(handle, ptr, len)
		})
	})
}

func (s *Server) DecryptAndUpdateJSON(ciphertext []byte) (string, error) {
	if s == nil {
		return "", ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) (string, error) {
		data, err := callUnary(ciphertext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_buffer {
			return C.beaconcrypt_decrypt_and_update_json(handle, ptr, len)
		})
		if err != nil {
			return "", err
		}
		return string(data), nil
	})
}

func (b *Beacon) EncryptToServer(plaintext []byte) ([]byte, error) {
	if b == nil {
		return nil, ErrClosed
	}
	return withBeaconHandle(b.native, func(handle *C.beaconcrypt_Beacon) ([]byte, error) {
		return callUnary(plaintext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_buffer {
			return C.beaconcrypt_encrypt_to_server(handle, ptr, len)
		})
	})
}

func (b *Beacon) DecryptServerMessage(ciphertext []byte) ([]byte, error) {
	if b == nil {
		return nil, ErrClosed
	}
	return withBeaconHandle(b.native, func(handle *C.beaconcrypt_Beacon) ([]byte, error) {
		return callUnary(ciphertext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_buffer {
			return C.beaconcrypt_decrypt_server_message(handle, ptr, len)
		})
	})
}

func withServerHandle[T any](native *serverNativeHandle, call func(*C.beaconcrypt_Server) (T, error)) (T, error) {
	var zero T
	if native == nil {
		return zero, ErrClosed
	}
	native.mu.Lock()
	defer native.mu.Unlock()
	defer runtime.KeepAlive(native)
	if native.handle == nil {
		return zero, ErrClosed
	}
	return call(native.handle)
}
func withBeaconHandle[T any](native *beaconNativeHandle, call func(*C.beaconcrypt_Beacon) (T, error)) (T, error) {
	var zero T
	if native == nil {
		return zero, ErrClosed
	}
	native.mu.Lock()
	defer native.mu.Unlock()
	defer runtime.KeepAlive(native)
	if native.handle == nil {
		return zero, ErrClosed
	}
	return call(native.handle)
}
func newServerNativeHandle(handle *C.beaconcrypt_Server) *serverNativeHandle {
	native := &serverNativeHandle{handle: handle}
	runtime.SetFinalizer(native, (*serverNativeHandle).close)
	return native
}
func newBeaconNativeHandle(handle *C.beaconcrypt_Beacon) *beaconNativeHandle {
	native := &beaconNativeHandle{handle: handle}
	runtime.SetFinalizer(native, (*beaconNativeHandle).close)
	return native
}
func (native *serverNativeHandle) close() {
	if native == nil {
		return
	}
	native.mu.Lock()
	defer native.mu.Unlock()
	defer runtime.KeepAlive(native)
	runtime.SetFinalizer(native, nil)
	if native.handle != nil {
		C.beaconcrypt_server_free(native.handle)
		native.handle = nil
		native.store = nil
	}
}
func (native *beaconNativeHandle) close() {
	if native == nil {
		return
	}
	native.mu.Lock()
	defer native.mu.Unlock()
	defer runtime.KeepAlive(native)
	runtime.SetFinalizer(native, nil)
	if native.handle != nil {
		C.beaconcrypt_beacon_free(native.handle)
		native.handle = nil
	}
}

func callUnary(data []byte, call func(*C.uint8_t, C.uintptr_t) C.beaconcrypt_buffer) ([]byte, error) {
	if len(data) == 0 {
		return nil, ErrEmptyData
	}
	ptr, free := cBytes(data)
	defer free()
	return copyBuffer(call(ptr, C.uintptr_t(len(data))))
}

func callStateUpdate(data []byte, call func(*C.uint8_t, C.uintptr_t) C.beaconcrypt_encrypt_state) (*EncryptState, error) {
	if len(data) == 0 {
		return nil, ErrEmptyData
	}
	ptr, free := cBytes(data)
	defer free()
	state := call(ptr, C.uintptr_t(len(data)))
	output, err := copyBuffer(state.data)
	if err != nil {
		C.beaconcrypt_free_buffer(state.state)
		return nil, err
	}
	serializedState, err := copyBuffer(state.state)
	if err != nil {
		return nil, err
	}
	return &EncryptState{
		Data:  output,
		State: string(serializedState),
		KeyID: uint64(state.key_id),
		Seq:   uint64(state.seq),
	}, nil
}

func copyBuffer(buffer C.beaconcrypt_buffer) ([]byte, error) {
	if buffer.ptr == nil {
		return nil, ErrCrypto
	}
	defer C.beaconcrypt_free_buffer(buffer)
	if buffer.len == 0 {
		return []byte{}, nil
	}
	return callbackBytes(buffer.ptr, buffer.len)
}

func cBytes(data []byte) (*C.uint8_t, func()) {
	if len(data) == 0 {
		return nil, func() {}
	}
	ptr := C.CBytes(data)
	return (*C.uint8_t)(ptr), func() { C.beaconcrypt_wipe_free(ptr, C.uintptr_t(len(data))) }
}
