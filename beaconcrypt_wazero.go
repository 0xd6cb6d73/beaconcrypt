// SPDX-License-Identifier: 0BSD

//go:build !cgo || beaconcrypt_wazero

package beaconcrypt

import (
	"encoding/binary"
	"errors"
	"fmt"
	"runtime"
)

type serverNativeHandle struct{ instance *wasmInstance }
type beaconNativeHandle struct{ instance *wasmInstance }

func wasmServer(instance *wasmInstance) *Server {
	handle := &serverNativeHandle{instance: instance}
	runtime.SetFinalizer(handle, (*serverNativeHandle).close)
	return &Server{native: handle}
}

func wasmBeacon(instance *wasmInstance) *Beacon {
	handle := &beaconNativeHandle{instance: instance}
	runtime.SetFinalizer(handle, (*beaconNativeHandle).close)
	return &Beacon{native: handle}
}

func (handle *serverNativeHandle) close() {
	if handle != nil {
		defer runtime.KeepAlive(handle)
		runtime.SetFinalizer(handle, nil)
		handle.instance.close()
	}
}

func (handle *beaconNativeHandle) close() {
	if handle != nil {
		defer runtime.KeepAlive(handle)
		runtime.SetFinalizer(handle, nil)
		handle.instance.close()
	}
}

func wasmCryptoError(err error) error {
	var failure *PersistenceError
	if errors.As(err, &failure) {
		return ErrCrypto
	}
	return err
}

func wasmMutationError(err error) error {
	var failure *PersistenceError
	if errors.As(err, &failure) && failure.Code == StatusRejected {
		return ErrCrypto
	}
	return err
}

func constructWasm(op uint32, arg uint64, input, extra []byte, store SnapshotStore) (*wasmInstance, error) {
	engine, err := sharedWasmEngine()
	if err != nil {
		return nil, fmt.Errorf("%w: WASM runtime: %v", ErrCrypto, err)
	}
	return engine.construct(op, arg, input, extra, store)
}

func wasmIdentitySeeds(edSeed, mldsaSeed []byte) ([]byte, byte, error) {
	if (len(edSeed) != 0 && len(edSeed) != 32) || (len(mldsaSeed) != 0 && len(mldsaSeed) != 32) {
		return nil, 0, ErrSeedSize
	}
	var flags byte
	if len(edSeed) != 0 {
		flags |= 1
	}
	if len(mldsaSeed) != 0 {
		flags |= 2
	}
	input := append(append(make([]byte, 0, len(edSeed)+len(mldsaSeed)), edSeed...), mldsaSeed...)
	return input, flags, nil
}

func NewServer(serverKID uint64) (*Server, error) {
	instance, err := constructWasm(1, serverKID, nil, []byte{0}, nil)
	if err != nil {
		return nil, wasmCryptoError(err)
	}
	return wasmServer(instance), nil
}

func NewServerFromSeed(serverKID uint64, seed, mldsaSeed []byte) (*Server, error) {
	if len(seed) != 32 || len(mldsaSeed) != 32 {
		return nil, ErrSeedSize
	}
	input, flags, _ := wasmIdentitySeeds(seed, mldsaSeed)
	defer clear(input)
	instance, err := constructWasm(1, serverKID, input, []byte{flags}, nil)
	if err != nil {
		return nil, wasmCryptoError(err)
	}
	return wasmServer(instance), nil
}

// NewServerFromState restores trusted plaintext checkpoint bytes. The caller
// must reject stale/untrusted checkpoints and immediately save the advanced
// generation returned by ExportState before using the restored server.
func NewServerFromState(state []byte) (*Server, error) {
	if len(state) == 0 {
		return nil, ErrEmptyData
	}
	instance, err := constructWasm(11, 0, state, nil, nil)
	if err != nil {
		return nil, wasmCryptoError(err)
	}
	return wasmServer(instance), nil
}

func NewBeacon(serverKID uint64, serverPK, serverMLDSAPK []byte) (*Beacon, error) {
	if len(serverPK) != 32 || len(serverMLDSAPK) != MLDSA65PublicKeySize {
		return nil, ErrCrypto
	}
	input := append(append(make([]byte, 0, 32+MLDSA65PublicKeySize), serverPK...), serverMLDSAPK...)
	instance, err := constructWasm(2, serverKID, input, nil, nil)
	if err != nil {
		return nil, wasmCryptoError(err)
	}
	return wasmBeacon(instance), nil
}

// NewServerWithStore creates and commits generation zero before returning.
// Each empty seed generates its corresponding identity key; supplied seeds must be 32 bytes.
func NewServerWithStore(serverKID uint64, seed, mldsaSeed []byte, store SnapshotStore) (*Server, error) {
	return newWasmServerWithStore(serverKID, seed, mldsaSeed, store, nil)
}

// NewServerWithStoreAndLineage uses an externally allocated lineage belonging
// to exactly one authoritative storage domain.
func NewServerWithStoreAndLineage(serverKID uint64, seed, mldsaSeed []byte, store SnapshotStore, lineage [32]byte) (*Server, error) {
	return newWasmServerWithStore(serverKID, seed, mldsaSeed, store, &lineage)
}

func newWasmServerWithStore(serverKID uint64, seed, mldsaSeed []byte, store SnapshotStore, lineage *[32]byte) (*Server, error) {
	if store == nil {
		return nil, &PersistenceError{Code: StatusInvalidArgument}
	}
	input, flags, err := wasmIdentitySeeds(seed, mldsaSeed)
	if err != nil {
		return nil, err
	}
	defer clear(input)
	op := uint32(12)
	extra := make([]byte, 4)
	binary.LittleEndian.PutUint32(extra, 1)
	if lineage != nil {
		op = 18
		extra = append(extra, lineage[:]...)
	}
	extra = append(extra, flags)
	instance, err := constructWasm(op, serverKID, input, extra, store)
	if err != nil {
		return nil, wasmPersistenceConstructorError(err)
	}
	return wasmServer(instance), nil
}

func wasmPersistenceConstructorError(err error) error {
	var failure *PersistenceError
	if errors.As(err, &failure) {
		return err
	}
	return &PersistenceError{Code: StatusInitialization, Cause: err}
}

// RestoreServer loads the trusted current snapshot and commits its next
// generation before activating a server. Competing owners must share one store.
func RestoreServer(store SnapshotStore) (*Server, error) {
	if store == nil {
		return nil, &PersistenceError{Code: StatusInvalidArgument}
	}
	instance, err := constructWasm(13, 1, nil, nil, store)
	if err != nil {
		return nil, wasmPersistenceConstructorError(err)
	}
	return wasmServer(instance), nil
}

func (s *Server) Close() {
	if s != nil {
		s.native.close()
	}
}

func (b *Beacon) Close() {
	if b != nil {
		b.native.close()
	}
}

func (s *Server) wasmCall(op uint32, arg uint64, input, extra []byte) (wasmResponse, error) {
	if s == nil || s.native == nil {
		return wasmResponse{}, ErrClosed
	}
	defer runtime.KeepAlive(s.native)
	return s.native.instance.call(op, arg, input, extra)
}

func (b *Beacon) wasmCall(op uint32, arg uint64, input []byte) (wasmResponse, error) {
	if b == nil || b.native == nil {
		return wasmResponse{}, ErrClosed
	}
	defer runtime.KeepAlive(b.native)
	response, err := b.native.instance.call(op, arg, input, nil)
	return response, wasmCryptoError(err)
}

func (s *Server) IdentityPK() ([]byte, error) {
	r, err := s.wasmCall(3, 0, nil, nil)
	return r.data, wasmCryptoError(err)
}

// MLDSAPublicKey returns the server authentication key to provision into beacons.
func (s *Server) MLDSAPublicKey() ([]byte, error) {
	r, err := s.wasmCall(24, 0, nil, nil)
	return r.data, wasmCryptoError(err)
}

// MLDSAPublicKey returns the beacon's ML-DSA-65 authentication key.
func (b *Beacon) MLDSAPublicKey() ([]byte, error) {
	r, err := b.wasmCall(24, 0, nil)
	return r.data, err
}

func (b *Beacon) GenerateRegistration() ([]byte, error) {
	r, err := b.wasmCall(4, 0, nil)
	return r.data, err
}

func (s *Server) RegisterBeacon(registration, initialMessage []byte) (*RegistrationResponse, error) {
	r, err := s.wasmCall(5, 0, registration, initialMessage)
	if err != nil {
		return nil, wasmMutationError(err)
	}
	return &RegistrationResponse{Serialized: r.data, KeyID: r.keyID}, nil
}

func (b *Beacon) ProcessInitialMessage(data []byte) ([]byte, error) {
	r, err := b.wasmCall(6, 0, data)
	return r.data, err
}

func (s *Server) EncryptToBeacon(keyID uint64, plaintext []byte) ([]byte, error) {
	r, err := s.wasmCall(7, keyID, plaintext, nil)
	return r.data, wasmMutationError(err)
}

func (s *Server) DecryptBeaconMessage(ciphertext []byte) ([]byte, error) {
	r, err := s.wasmCall(8, 0, ciphertext, nil)
	return r.data, wasmMutationError(err)
}

func (b *Beacon) EncryptToServer(plaintext []byte) ([]byte, error) {
	r, err := b.wasmCall(7, 0, plaintext)
	return r.data, err
}

func (b *Beacon) DecryptServerMessage(ciphertext []byte) ([]byte, error) {
	r, err := b.wasmCall(8, 0, ciphertext)
	return r.data, err
}

func (s *Server) updateWasm(op uint32, keyID uint64, data []byte) (*EncryptState, error) {
	r, err := s.wasmCall(op, keyID, data, nil)
	if err != nil {
		return nil, wasmMutationError(err)
	}
	defer clear(r.state)
	return &EncryptState{Data: r.data, State: string(r.state), KeyID: r.keyID, Seq: r.seq}, nil
}

func (s *Server) EncryptAndUpdate(keyID uint64, plaintext []byte) (*EncryptState, error) {
	return s.updateWasm(20, keyID, plaintext)
}

func (s *Server) DecryptAndUpdate(ciphertext []byte) (*EncryptState, error) {
	return s.updateWasm(21, 0, ciphertext)
}

func (s *Server) EncryptAndUpdateJSON(keyID uint64, plaintext []byte) (string, error) {
	r, err := s.wasmCall(22, keyID, plaintext, nil)
	defer clear(r.data)
	return string(r.data), wasmMutationError(err)
}

func (s *Server) DecryptAndUpdateJSON(ciphertext []byte) (string, error) {
	r, err := s.wasmCall(23, 0, ciphertext, nil)
	defer clear(r.data)
	return string(r.data), wasmMutationError(err)
}

// ExportState returns the current trusted plaintext checkpoint. Save it after
// every state-changing operation and before releasing that operation's output.
// An exported checkpoint alone does not prevent rollback.
func (s *Server) ExportState() ([]byte, error) {
	r, err := s.wasmCall(10, 0, nil, nil)
	return r.data, wasmMutationError(err)
}

// Head returns the currently committed generation and exact snapshot identity.
func (s *Server) Head() (SnapshotHead, error) {
	r, err := s.wasmCall(14, 0, nil, nil)
	if err != nil {
		return SnapshotHead{}, err
	}
	return decodeWasmHead(r.data)
}

// IsPoisoned reports whether a failed commit has disabled the server, or the
// server is closed or absent.
func (s *Server) IsPoisoned() bool {
	r, err := s.wasmCall(15, 0, nil, nil)
	return err != nil || len(r.data) != 1 || r.data[0] != 0
}

// ParseSnapshotHead parses the envelope and computes its exact-byte digest.
// It does not authenticate a snapshot or activate its protocol state.
func ParseSnapshotHead(snapshot []byte) (SnapshotHead, error) {
	engine, err := sharedWasmEngine()
	if err != nil {
		return SnapshotHead{}, err
	}
	return engine.inspect(snapshot, nil, false)
}

// ValidateSnapshotSuccessor validates lineage, next generation and parent digest
// against expected. The store must separately compare its authoritative head in
// the same transaction. A separate instance permits validation inside a CAS.
func ValidateSnapshotSuccessor(snapshot []byte, expected *SnapshotHead) (SnapshotHead, error) {
	engine, err := sharedWasmEngine()
	if err != nil {
		return SnapshotHead{}, err
	}
	return engine.inspect(snapshot, expected, true)
}
