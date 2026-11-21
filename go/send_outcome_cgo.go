// SPDX-License-Identifier: 0BSD

//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

/*
#include "beaconcrypt_go.h"
*/
import "C"

func copySendResult(value C.beaconcrypt_SendResult) (*SendResult, error) {
	defer C.beaconcrypt_free_buffer(value.message.data)
	defer C.beaconcrypt_free_buffer(value.message.state)
	if status := PersistenceStatus(value.status); status != StatusOK {
		return nil, &PersistenceError{Code: status}
	}
	var data, state []byte
	var err error
	if value.message.data.ptr != nil {
		data, err = callbackBytes(value.message.data.ptr, value.message.data.len)
		if err != nil {
			return nil, err
		}
	} else if value.message.data.len != 0 || value.message.data.cap != 0 {
		return nil, ErrCrypto
	}
	if value.message.state.ptr != nil {
		state, err = callbackBytes(value.message.state.ptr, value.message.state.len)
		if err != nil {
			clear(data)
			return nil, err
		}
		defer clear(state)
	} else if value.message.state.len != 0 || value.message.state.cap != 0 {
		clear(data)
		return nil, ErrCrypto
	}
	result, err := makeSendResult(SendOutcome(value.outcome), data, state, uint64(value.message.key_id), uint64(value.message.seq))
	if err != nil {
		clear(data)
	}
	return result, err
}

func callSendOutcome(data []byte, call func(*C.uint8_t, C.uintptr_t) C.beaconcrypt_SendResult) (*SendResult, error) {
	ptr, free := cBytes(data)
	defer free()
	return copySendResult(call(ptr, C.uintptr_t(len(data))))
}

// EncryptToBeaconOutcome reports whether a key was consumed, including when no
// ciphertext was produced. A store-backed result is returned only after commit.
func (s *Server) EncryptToBeaconOutcome(keyID uint64, plaintext []byte) (*SendResult, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) (*SendResult, error) {
		return callSendOutcome(plaintext, func(ptr *C.uint8_t, length C.uintptr_t) C.beaconcrypt_SendResult {
			return C.beaconcrypt_encrypt_to_beacon_outcome(handle, C.uint64_t(keyID), ptr, length)
		})
	})
}

// EncryptToServerOutcome reports the effect of one beacon send attempt.
func (b *Beacon) EncryptToServerOutcome(plaintext []byte) (*SendResult, error) {
	if b == nil {
		return nil, ErrClosed
	}
	return withBeaconHandle(b.native, func(handle *C.beaconcrypt_Beacon) (*SendResult, error) {
		return callSendOutcome(plaintext, func(ptr *C.uint8_t, length C.uintptr_t) C.beaconcrypt_SendResult {
			return C.beaconcrypt_encrypt_to_server_outcome(handle, ptr, length)
		})
	})
}

// EncryptAndUpdateOutcome includes observational ratchet JSON only for SendSent.
func (s *Server) EncryptAndUpdateOutcome(keyID uint64, plaintext []byte) (*SendResult, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) (*SendResult, error) {
		return callSendOutcome(plaintext, func(ptr *C.uint8_t, length C.uintptr_t) C.beaconcrypt_SendResult {
			return C.beaconcrypt_encrypt_and_update_outcome(handle, C.uint64_t(keyID), ptr, length)
		})
	})
}

// EncryptAndUpdateJSONOutcome puts the successful JSON result in Data.
func (s *Server) EncryptAndUpdateJSONOutcome(keyID uint64, plaintext []byte) (*SendResult, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return withServerMutation(s.native, func(handle *C.beaconcrypt_Server) (*SendResult, error) {
		return callSendOutcome(plaintext, func(ptr *C.uint8_t, length C.uintptr_t) C.beaconcrypt_SendResult {
			return C.beaconcrypt_encrypt_and_update_json_outcome(handle, C.uint64_t(keyID), ptr, length)
		})
	})
}

// EncryptToBeaconOutcome returns the committed row send effect without exposing
// pending transaction output. CachedRowServer inherits this method.
func (s *RowServer) EncryptToBeaconOutcome(keyID uint64, plaintext []byte) (*SendResult, error) {
	return rowCall(s, true, func(handle *C.beaconcrypt_RowServerHandle) (*SendResult, error) {
		return callSendOutcome(plaintext, func(ptr *C.uint8_t, length C.uintptr_t) C.beaconcrypt_SendResult {
			return C.beaconcrypt_row_server_encrypt_outcome(handle, ptr, length, C.uint64_t(keyID))
		})
	})
}
