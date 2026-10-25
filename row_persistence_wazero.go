// SPDX-License-Identifier: 0BSD
//go:build !cgo || beaconcrypt_wazero

package beaconcrypt

// RowServer reserves the native row persistence API in WASM builds. Constructors
// return ErrPersistenceUnsupported; the guest currently exposes snapshot storage.
type RowServer struct{}

func NewRowServer(kid uint64, seed, mldsaSeed []byte, store RowStore, lineage [32]byte) (*RowServer, error) {
	return nil, ErrPersistenceUnsupported
}
func OpenRowServer(store RowStore, lineage [32]byte) (*RowServer, error) {
	return nil, ErrPersistenceUnsupported
}
func (s *RowServer) Close()                          {}
func (s *RowServer) IdentityPK() ([]byte, error)     { return nil, ErrClosed }
func (s *RowServer) MLDSAPublicKey() ([]byte, error) { return nil, ErrClosed }
func (s *RowServer) RegisterBeacon(registration, initialMessage []byte) (*RegistrationResponse, error) {
	return nil, ErrClosed
}
func (s *RowServer) EncryptToBeacon(kid uint64, data []byte) ([]byte, error) { return nil, ErrClosed }
func (s *RowServer) DecryptBeaconMessage(data []byte) ([]byte, error)        { return nil, ErrClosed }
