// SPDX-License-Identifier: 0BSD

//go:build !cgo || beaconcrypt_wazero

package beaconcrypt

func decodeWasmSendResult(response wasmResponse) (*SendResult, error) {
	defer clear(response.state)
	if len(response.state) == 0 {
		clear(response.data)
		return nil, ErrCrypto
	}
	result, err := makeSendResult(SendOutcome(response.state[0]), response.data, response.state[1:], response.keyID, response.seq)
	if err != nil {
		clear(response.data)
	}
	return result, err
}

// EncryptToBeaconOutcome reports the effect only after confirmed durable commit.
func (s *Server) EncryptToBeaconOutcome(keyID uint64, plaintext []byte) (*SendResult, error) {
	result, err := s.wasmCall(25, keyID, plaintext, nil)
	if err != nil {
		return nil, wasmMutationError(err)
	}
	return decodeWasmSendResult(result)
}

// EncryptToServerOutcome reports the effect of one beacon send attempt.
func (b *Beacon) EncryptToServerOutcome(plaintext []byte) (*SendResult, error) {
	result, err := b.wasmCall(25, 0, plaintext)
	if err != nil {
		return nil, err
	}
	return decodeWasmSendResult(result)
}

// EncryptAndUpdateOutcome includes observational JSON only for SendSent.
func (s *Server) EncryptAndUpdateOutcome(keyID uint64, plaintext []byte) (*SendResult, error) {
	result, err := s.wasmCall(26, keyID, plaintext, nil)
	if err != nil {
		return nil, wasmMutationError(err)
	}
	return decodeWasmSendResult(result)
}

// EncryptAndUpdateJSONOutcome puts the successful JSON result in Data.
func (s *Server) EncryptAndUpdateJSONOutcome(keyID uint64, plaintext []byte) (*SendResult, error) {
	result, err := s.wasmCall(27, keyID, plaintext, nil)
	if err != nil {
		return nil, wasmMutationError(err)
	}
	return decodeWasmSendResult(result)
}

func (s *RowServer) EncryptToBeaconOutcome(keyID uint64, plaintext []byte) (*SendResult, error) {
	return nil, ErrClosed
}
