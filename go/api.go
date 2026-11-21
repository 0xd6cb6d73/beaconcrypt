// SPDX-License-Identifier: 0BSD

package beaconcrypt

import "errors"

// MaxMessageSize is the maximum complete encoded transport message in bytes, including framing, authentication tags, and commitments. It does not limit snapshots or JSON state.
const MaxMessageSize int = 32 * 1024 * 1024

// MLDSA65PublicKeySize is the size of a pinned ML-DSA-65 public key.
const MLDSA65PublicKeySize = 1952

var (
	ErrClosed    = errors.New("beaconcrypt: handle is closed")
	ErrCrypto    = errors.New("beaconcrypt: cryptographic operation failed")
	ErrSeedSize  = errors.New("beaconcrypt: identity seeds must each be 32 bytes")
	ErrEmptyData = errors.New("beaconcrypt: input must not be empty")
)

// Server is safe for concurrent use. Calls on one Server are serialized because
// they mutate shared ratchet state.
type Server struct {
	native *serverNativeHandle
}

// Beacon is safe for concurrent use. Calls on one Beacon are serialized because
// they mutate shared ratchet state.
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
