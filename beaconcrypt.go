// SPDX-License-Identifier: 0BSD

package beaconcrypt

/*
#cgo windows LDFLAGS: -L${SRCDIR}/target/x86_64-pc-windows-gnu/release -l:libbeaconcrypt.a -lbcrypt -lws2_32 -luserenv -ldbghelp -lntdll
#cgo linux LDFLAGS: -L${SRCDIR}/target/release -l:libbeaconcrypt.a
#cgo darwin LDFLAGS: ${SRCDIR}/target/release/libbeaconcrypt.a
#include <stdint.h>
#include <stdlib.h>

typedef struct {
	uint8_t *ptr;
	uintptr_t len;
	uintptr_t cap;
} beaconcrypt_buffer;

typedef struct {
	beaconcrypt_buffer response;
	uint64_t key_id;
} beaconcrypt_registration_response;

typedef struct {
	beaconcrypt_buffer data;
	beaconcrypt_buffer state;
	uint64_t key_id;
	uint64_t seq;
} beaconcrypt_encrypt_state;

typedef struct beaconcrypt_Server beaconcrypt_Server;
typedef struct beaconcrypt_Beacon beaconcrypt_Beacon;

void beaconcrypt_free_buffer(beaconcrypt_buffer buffer);
beaconcrypt_Server *beaconcrypt_server_new(uint64_t server_kid);
beaconcrypt_Server *beaconcrypt_server_new_from_seed(uint64_t server_kid, const uint8_t *seed_ptr, uintptr_t seed_len);
beaconcrypt_Server *beaconcrypt_server_new_from_state(const uint8_t *state_ptr, uintptr_t state_len);
beaconcrypt_buffer beaconcrypt_server_export_state(const beaconcrypt_Server *handle);
beaconcrypt_Beacon *beaconcrypt_beacon_new(uint64_t server_kid, const uint8_t *server_pk_ptr, uintptr_t server_pk_len);
void beaconcrypt_server_free(beaconcrypt_Server *handle);
void beaconcrypt_beacon_free(beaconcrypt_Beacon *handle);
beaconcrypt_buffer beaconcrypt_server_identity_pk(const beaconcrypt_Server *handle);
beaconcrypt_buffer beaconcrypt_beacon_identity_pk(const beaconcrypt_Beacon *handle);
beaconcrypt_buffer beaconcrypt_generate_registration(beaconcrypt_Beacon *handle);
beaconcrypt_registration_response beaconcrypt_register_beacon(beaconcrypt_Server *handle, const uint8_t *reg_ptr, uintptr_t reg_len, const uint8_t *msg_ptr, uintptr_t msg_len);
beaconcrypt_buffer beaconcrypt_process_initial_message(beaconcrypt_Beacon *handle, const uint8_t *ptr, uintptr_t len);
beaconcrypt_buffer beaconcrypt_encrypt_to_beacon(beaconcrypt_Server *handle, uint64_t key_id, const uint8_t *ptr, uintptr_t len);
beaconcrypt_buffer beaconcrypt_decrypt_beacon_message(beaconcrypt_Server *handle, const uint8_t *ptr, uintptr_t len);
beaconcrypt_encrypt_state beaconcrypt_encrypt_and_update(beaconcrypt_Server *handle, uint64_t key_id, const uint8_t *ptr, uintptr_t len);
beaconcrypt_buffer beaconcrypt_encrypt_and_update_json(beaconcrypt_Server *handle, uint64_t key_id, const uint8_t *ptr, uintptr_t len);
beaconcrypt_encrypt_state beaconcrypt_decrypt_and_update(beaconcrypt_Server *handle, const uint8_t *ptr, uintptr_t len);
beaconcrypt_buffer beaconcrypt_decrypt_and_update_json(beaconcrypt_Server *handle, const uint8_t *ptr, uintptr_t len);
beaconcrypt_buffer beaconcrypt_encrypt_to_server(beaconcrypt_Beacon *handle, const uint8_t *ptr, uintptr_t len);
beaconcrypt_buffer beaconcrypt_decrypt_server_message(beaconcrypt_Beacon *handle, const uint8_t *ptr, uintptr_t len);
*/
import "C"

import (
	"errors"
	"runtime"
	"sync"
	"unsafe"
)

var (
	ErrClosed    = errors.New("beaconcrypt: handle is closed")
	ErrCrypto    = errors.New("beaconcrypt: cryptographic operation failed")
	ErrSeedSize  = errors.New("beaconcrypt: server seed must be 32 bytes")
	ErrEmptyData = errors.New("beaconcrypt: input must not be empty")
)

type serverNativeHandle struct {
	mu     sync.Mutex
	handle *C.beaconcrypt_Server
}
type beaconNativeHandle struct {
	mu     sync.Mutex
	handle *C.beaconcrypt_Beacon
}

// Server is safe for concurrent use. Calls on one Server are serialized because
// they mutate shared native ratchet state.
type Server struct {
	native *serverNativeHandle
}

// Beacon is safe for concurrent use. Calls on one Beacon are serialized because
// they mutate shared native ratchet state.
type Beacon struct {
	native *beaconNativeHandle
}

type RegistrationResponse struct {
	Serialized []byte
	KeyID      uint64
}

type EncryptState struct {
	Data []byte
	// State is inert plaintext ratchet JSON for observation only.
	// It is secret-bearing, unauthenticated, and not restorable.
	State string
	KeyID uint64
	Seq   uint64
}

func NewServer(serverKID uint64) (*Server, error) {
	handle := C.beaconcrypt_server_new(C.uint64_t(serverKID))
	if handle == nil {
		return nil, ErrCrypto
	}
	server := &Server{native: newServerNativeHandle(handle)}
	return server, nil
}

func NewServerFromSeed(serverKID uint64, seed []byte) (*Server, error) {
	if len(seed) != 32 {
		return nil, ErrSeedSize
	}
	ptr, free := cBytes(seed)
	defer free()
	handle := C.beaconcrypt_server_new_from_seed(C.uint64_t(serverKID), ptr, C.uintptr_t(len(seed)))
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

// ExportState returns the current plaintext server checkpoint.
//
// Save it immediately after every state-changing call and before using that
// call's output. A standalone exported checkpoint does not prevent rollback.
func (s *Server) ExportState() ([]byte, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) ([]byte, error) {
		return copyBuffer(C.beaconcrypt_server_export_state(handle))
	})
}

func NewBeacon(serverKID uint64, serverPK []byte) (*Beacon, error) {
	ptr, free := cBytes(serverPK)
	defer free()
	handle := C.beaconcrypt_beacon_new(C.uint64_t(serverKID), ptr, C.uintptr_t(len(serverPK)))
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
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) (*RegistrationResponse, error) {
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
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) ([]byte, error) {
		return callUnary(plaintext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_buffer {
			return C.beaconcrypt_encrypt_to_beacon(handle, C.uint64_t(keyID), ptr, len)
		})
	})
}

func (s *Server) DecryptBeaconMessage(ciphertext []byte) ([]byte, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) ([]byte, error) {
		return callUnary(ciphertext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_buffer {
			return C.beaconcrypt_decrypt_beacon_message(handle, ptr, len)
		})
	})
}

func (s *Server) EncryptAndUpdate(keyID uint64, plaintext []byte) (*EncryptState, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) (*EncryptState, error) {
		return callStateUpdate(plaintext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_encrypt_state {
			return C.beaconcrypt_encrypt_and_update(handle, C.uint64_t(keyID), ptr, len)
		})
	})
}

func (s *Server) EncryptAndUpdateJSON(keyID uint64, plaintext []byte) (string, error) {
	if s == nil {
		return "", ErrClosed
	}
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) (string, error) {
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
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) (*EncryptState, error) {
		return callStateUpdate(ciphertext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_encrypt_state {
			return C.beaconcrypt_decrypt_and_update(handle, ptr, len)
		})
	})
}

func (s *Server) DecryptAndUpdateJSON(ciphertext []byte) (string, error) {
	if s == nil {
		return "", ErrClosed
	}
	return withServerHandle(s.native, func(handle *C.beaconcrypt_Server) (string, error) {
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
	return C.GoBytes(unsafe.Pointer(buffer.ptr), C.int(buffer.len)), nil
}

func cBytes(data []byte) (*C.uint8_t, func()) {
	if len(data) == 0 {
		return nil, func() {}
	}
	ptr := C.CBytes(data)
	return (*C.uint8_t)(ptr), func() { C.free(ptr) }
}
