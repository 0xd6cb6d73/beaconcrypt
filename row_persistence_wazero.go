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
func (s *RowServer) EncryptToBeaconWithMetadata(kid uint64, data []byte) (*RowMessage, error) {
	return nil, ErrClosed
}
func (s *RowServer) DecryptBeaconMessageWithMetadata(data []byte) (*RowMessage, error) {
	return nil, ErrClosed
}

// RowSession reserves the native transaction composition API in WASM builds.
type RowSession struct{}

func (s *RowServer) Transaction(operation func(*RowSession) ([]byte, error)) ([]byte, error) {
	return nil, ErrClosed
}
func (s *RowServer) RegistrationTransaction(accept func(*RowSession) (RowRegistrationDecision, error), complete func(*RowSession, []byte) ([]byte, error)) ([]byte, error) {
	return nil, ErrClosed
}
func (s *RowSession) Load(key []byte) ([]byte, error) { return nil, ErrRowSessionExpired }
func (s *RowSession) Store(key, value []byte) error   { return ErrRowSessionExpired }
func (s *RowSession) EncryptToBeacon(kid uint64, data []byte) (*RowTransition, error) {
	return nil, ErrRowSessionExpired
}
func (s *RowSession) DecryptBeaconMessage(data []byte) (*RowTransition, error) {
	return nil, ErrRowSessionExpired
}
func (s *RowSession) AcceptRegistration(data []byte) (bool, error) {
	return false, ErrRowSessionExpired
}
func (s *RowSession) CompleteRegistration(initialMessage []byte) (*RowTransition, error) {
	return nil, ErrRowSessionExpired
}
