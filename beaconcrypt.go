// SPDX-License-Identifier: 0BSD

package beaconcrypt

/*
#cgo windows LDFLAGS: -L${SRCDIR}/target/x86_64-pc-windows-gnu/debug -l:libbeaconcrypt.a -lbcrypt -lws2_32 -luserenv -ldbghelp -lntdll
#cgo linux LDFLAGS: -L${SRCDIR}/target/debug -l:libbeaconcrypt.a
#cgo darwin LDFLAGS: ${SRCDIR}/target/debug/libbeaconcrypt.a
#include <stdint.h>
#include <stdlib.h>

typedef struct {
	uint8_t *ptr;
	uintptr_t len;
	uintptr_t cap;
} beaconcrypt_go_buffer;

typedef struct {
	beaconcrypt_go_buffer response;
	beaconcrypt_go_buffer beacon_pk;
	uint64_t key_id;
} beaconcrypt_go_registration_response;

void beaconcrypt_go_free_buffer(beaconcrypt_go_buffer buffer);
void *beaconcrypt_go_server_new(uint64_t server_kid);
void *beaconcrypt_go_server_new_from_seed(uint64_t server_kid, const uint8_t *seed_ptr, uintptr_t seed_len);
void *beaconcrypt_go_beacon_new(uint64_t server_kid, const uint8_t *server_pk_ptr, uintptr_t server_pk_len);
void beaconcrypt_go_free(void *handle);
beaconcrypt_go_buffer beaconcrypt_go_identity_pk(const void *handle);
beaconcrypt_go_buffer beaconcrypt_go_generate_registration(void *handle);
beaconcrypt_go_registration_response beaconcrypt_go_register_beacon(void *handle, const uint8_t *reg_ptr, uintptr_t reg_len, const uint8_t *msg_ptr, uintptr_t msg_len);
beaconcrypt_go_buffer beaconcrypt_go_process_initial_message(void *handle, const uint8_t *ptr, uintptr_t len);
beaconcrypt_go_buffer beaconcrypt_go_encrypt_to_beacon(void *handle, uint64_t key_id, const uint8_t *ptr, uintptr_t len);
beaconcrypt_go_buffer beaconcrypt_go_encrypt_to_beacon_signed(void *handle, uint64_t key_id, const uint8_t *ptr, uintptr_t len);
beaconcrypt_go_buffer beaconcrypt_go_decrypt_beacon_message(void *handle, uint64_t key_id, const uint8_t *ptr, uintptr_t len);
beaconcrypt_go_buffer beaconcrypt_go_decrypt_beacon_message_signed(void *handle, const uint8_t *ptr, uintptr_t len);
beaconcrypt_go_buffer beaconcrypt_go_encrypt_to_server(void *handle, const uint8_t *ptr, uintptr_t len);
beaconcrypt_go_buffer beaconcrypt_go_encrypt_to_server_signed(void *handle, const uint8_t *ptr, uintptr_t len);
beaconcrypt_go_buffer beaconcrypt_go_decrypt_server_message(void *handle, const uint8_t *ptr, uintptr_t len);
beaconcrypt_go_buffer beaconcrypt_go_decrypt_server_message_signed(void *handle, const uint8_t *ptr, uintptr_t len);
*/
import "C"

import (
	"errors"
	"runtime"
	"unsafe"
)

var (
	ErrClosed    = errors.New("beaconcrypt: handle is closed")
	ErrCrypto    = errors.New("beaconcrypt: cryptographic operation failed")
	ErrSeedSize  = errors.New("beaconcrypt: server seed must be 32 bytes")
	ErrEmptyData = errors.New("beaconcrypt: input must not be empty")
)

type Server struct {
	handle unsafe.Pointer
}

type Beacon struct {
	handle unsafe.Pointer
}

type RegistrationResponse struct {
	Serialized []byte
	BeaconPK   []byte
	KeyID      uint64
}

func NewServer(serverKID uint64) (*Server, error) {
	handle := C.beaconcrypt_go_server_new(C.uint64_t(serverKID))
	if handle == nil {
		return nil, ErrCrypto
	}
	server := &Server{handle: handle}
	runtime.SetFinalizer(server, (*Server).Close)
	return server, nil
}

func NewServerFromSeed(serverKID uint64, seed []byte) (*Server, error) {
	if len(seed) != 32 {
		return nil, ErrSeedSize
	}
	ptr, free := cBytes(seed)
	defer free()
	handle := C.beaconcrypt_go_server_new_from_seed(C.uint64_t(serverKID), ptr, C.uintptr_t(len(seed)))
	if handle == nil {
		return nil, ErrCrypto
	}
	server := &Server{handle: handle}
	runtime.SetFinalizer(server, (*Server).Close)
	return server, nil
}

func NewBeacon(serverKID uint64, serverPK []byte) (*Beacon, error) {
	ptr, free := cBytes(serverPK)
	defer free()
	handle := C.beaconcrypt_go_beacon_new(C.uint64_t(serverKID), ptr, C.uintptr_t(len(serverPK)))
	if handle == nil {
		return nil, ErrCrypto
	}
	beacon := &Beacon{handle: handle}
	runtime.SetFinalizer(beacon, (*Beacon).Close)
	return beacon, nil
}

func (s *Server) Close() {
	if s != nil && s.handle != nil {
		C.beaconcrypt_go_free(s.handle)
		s.handle = nil
		runtime.SetFinalizer(s, nil)
	}
}

func (b *Beacon) Close() {
	if b != nil && b.handle != nil {
		C.beaconcrypt_go_free(b.handle)
		b.handle = nil
		runtime.SetFinalizer(b, nil)
	}
}

func (s *Server) IdentityPK() ([]byte, error) {
	if s == nil || s.handle == nil {
		return nil, ErrClosed
	}
	return copyBuffer(C.beaconcrypt_go_identity_pk(s.handle))
}

func (b *Beacon) GenerateRegistration() ([]byte, error) {
	if b == nil || b.handle == nil {
		return nil, ErrClosed
	}
	return copyBuffer(C.beaconcrypt_go_generate_registration(b.handle))
}

func (s *Server) RegisterBeacon(registration, initialMessage []byte) (*RegistrationResponse, error) {
	if s == nil || s.handle == nil {
		return nil, ErrClosed
	}
	if len(registration) == 0 {
		return nil, ErrEmptyData
	}
	regPtr, regFree := cBytes(registration)
	defer regFree()
	msgPtr, msgFree := cBytes(initialMessage)
	defer msgFree()
	response := C.beaconcrypt_go_register_beacon(
		s.handle,
		regPtr,
		C.uintptr_t(len(registration)),
		msgPtr,
		C.uintptr_t(len(initialMessage)),
	)
	serialized, err := copyBuffer(response.response)
	if err != nil {
		C.beaconcrypt_go_free_buffer(response.beacon_pk)
		return nil, err
	}
	beaconPK, err := copyBuffer(response.beacon_pk)
	if err != nil {
		return nil, err
	}
	return &RegistrationResponse{
		Serialized: serialized,
		BeaconPK:   beaconPK,
		KeyID:      uint64(response.key_id),
	}, nil
}

func (b *Beacon) ProcessInitialMessage(data []byte) ([]byte, error) {
	if b == nil || b.handle == nil {
		return nil, ErrClosed
	}
	return callUnary(data, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_go_buffer {
		return C.beaconcrypt_go_process_initial_message(b.handle, ptr, len)
	})
}

func (s *Server) EncryptToBeacon(keyID uint64, plaintext []byte) ([]byte, error) {
	if s == nil || s.handle == nil {
		return nil, ErrClosed
	}
	return callUnary(plaintext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_go_buffer {
		return C.beaconcrypt_go_encrypt_to_beacon(s.handle, C.uint64_t(keyID), ptr, len)
	})
}

func (s *Server) EncryptToBeaconSigned(keyID uint64, plaintext []byte) ([]byte, error) {
	if s == nil || s.handle == nil {
		return nil, ErrClosed
	}
	return callUnary(plaintext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_go_buffer {
		return C.beaconcrypt_go_encrypt_to_beacon_signed(s.handle, C.uint64_t(keyID), ptr, len)
	})
}

func (s *Server) DecryptBeaconMessage(keyID uint64, ciphertext []byte) ([]byte, error) {
	if s == nil || s.handle == nil {
		return nil, ErrClosed
	}
	return callUnary(ciphertext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_go_buffer {
		return C.beaconcrypt_go_decrypt_beacon_message(s.handle, C.uint64_t(keyID), ptr, len)
	})
}

func (s *Server) DecryptBeaconMessageSigned(ciphertext []byte) ([]byte, error) {
	if s == nil || s.handle == nil {
		return nil, ErrClosed
	}
	return callUnary(ciphertext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_go_buffer {
		return C.beaconcrypt_go_decrypt_beacon_message_signed(s.handle, ptr, len)
	})
}

func (b *Beacon) EncryptToServer(plaintext []byte) ([]byte, error) {
	if b == nil || b.handle == nil {
		return nil, ErrClosed
	}
	return callUnary(plaintext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_go_buffer {
		return C.beaconcrypt_go_encrypt_to_server(b.handle, ptr, len)
	})
}

func (b *Beacon) EncryptToServerSigned(plaintext []byte) ([]byte, error) {
	if b == nil || b.handle == nil {
		return nil, ErrClosed
	}
	return callUnary(plaintext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_go_buffer {
		return C.beaconcrypt_go_encrypt_to_server_signed(b.handle, ptr, len)
	})
}

func (b *Beacon) DecryptServerMessage(ciphertext []byte) ([]byte, error) {
	if b == nil || b.handle == nil {
		return nil, ErrClosed
	}
	return callUnary(ciphertext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_go_buffer {
		return C.beaconcrypt_go_decrypt_server_message(b.handle, ptr, len)
	})
}

func (b *Beacon) DecryptServerMessageSigned(ciphertext []byte) ([]byte, error) {
	if b == nil || b.handle == nil {
		return nil, ErrClosed
	}
	return callUnary(ciphertext, func(ptr *C.uint8_t, len C.uintptr_t) C.beaconcrypt_go_buffer {
		return C.beaconcrypt_go_decrypt_server_message_signed(b.handle, ptr, len)
	})
}

func callUnary(data []byte, call func(*C.uint8_t, C.uintptr_t) C.beaconcrypt_go_buffer) ([]byte, error) {
	if len(data) == 0 {
		return nil, ErrEmptyData
	}
	ptr, free := cBytes(data)
	defer free()
	return copyBuffer(call(ptr, C.uintptr_t(len(data))))
}

func copyBuffer(buffer C.beaconcrypt_go_buffer) ([]byte, error) {
	if buffer.ptr == nil {
		return nil, ErrCrypto
	}
	defer C.beaconcrypt_go_free_buffer(buffer)
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
