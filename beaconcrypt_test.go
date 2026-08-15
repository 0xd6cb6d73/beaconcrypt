// SPDX-License-Identifier: 0BSD

package beaconcrypt

import (
	"bytes"
	"encoding/json"
	"errors"
	"sync"
	"testing"
)

const (
	kdfStateSystemID  = 6
	chainSendKeyRole  = 8
	chainReceiveRole  = 9
	ratchetStateBytes = 32
)

type jsonStateUpdate struct {
	KID       uint64
	Seq       uint64
	State     string
	KeySystem uint8
	KeyRole   uint8
	Key       []byte
	Data      []byte
}

func decodeJSONStateUpdate(t *testing.T, serialized string, keyField string) jsonStateUpdate {
	t.Helper()

	var encoded struct {
		KID   uint64 `json:"kid"`
		Seq   uint64 `json:"seq"`
		State string `json:"state"`
		Data  []byte `json:"data"`
	}
	if err := json.Unmarshal([]byte(serialized), &encoded); err != nil {
		t.Fatalf("state update is not valid JSON: %v", err)
	}
	system, role, keyBytes := decodeJSONRatchetKey(t, json.RawMessage(encoded.State), keyField)
	return jsonStateUpdate{
		KID:       encoded.KID,
		Seq:       encoded.Seq,
		State:     encoded.State,
		KeySystem: system,
		KeyRole:   role,
		Key:       keyBytes,
		Data:      encoded.Data,
	}
}

func decodeJSONRatchetKey(t *testing.T, state json.RawMessage, keyField string) (uint8, uint8, []byte) {
	t.Helper()

	var encoded struct {
		SendKey []json.RawMessage `json:"send_key"`
		RecvKey []json.RawMessage `json:"recv_key"`
	}
	if err := json.Unmarshal(state, &encoded); err != nil {
		t.Fatalf("ratchet state is not valid JSON: %v", err)
	}
	var key []json.RawMessage
	switch keyField {
	case "send_key":
		key = encoded.SendKey
	case "recv_key":
		key = encoded.RecvKey
	default:
		t.Fatalf("unknown ratchet key field %q", keyField)
	}
	if len(key) != 3 {
		t.Fatalf("state %s tuple length mismatch: got %d want 3", keyField, len(key))
	}

	var system, role uint8
	var keyBytes []byte
	if err := json.Unmarshal(key[0], &system); err != nil {
		t.Fatalf("invalid state key system tag: %v", err)
	}
	if err := json.Unmarshal(key[1], &role); err != nil {
		t.Fatalf("invalid state key role tag: %v", err)
	}
	if err := json.Unmarshal(key[2], &keyBytes); err != nil {
		t.Fatalf("invalid state key payload: %v", err)
	}
	return system, role, keyBytes
}

func registerBeacon(t *testing.T, server *Server, beacon *Beacon) *RegistrationResponse {
	t.Helper()

	message := bytes.Repeat([]byte{0xff}, 32)
	regOut := registerBeaconWithInitial(t, server, beacon, message)

	phase2, err := beacon.ProcessInitialMessage(regOut.Serialized)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(phase2, message) {
		t.Fatalf("initial message mismatch: got %x want %x", phase2, message)
	}
	return regOut
}

func corruptAEADCiphertext(t *testing.T, ciphertext []byte) []byte {
	t.Helper()

	if len(ciphertext) == 0 {
		t.Fatal("cannot corrupt an empty ciphertext")
	}
	corrupted := bytes.Clone(ciphertext)
	corrupted[len(corrupted)-1] ^= 0x01
	return corrupted
}

func registerBeaconWithInitial(t *testing.T, server *Server, beacon *Beacon, message []byte) *RegistrationResponse {
	t.Helper()

	phase1, err := beacon.GenerateRegistration()
	if err != nil {
		t.Fatal(err)
	}

	regOut, err := server.RegisterBeacon(phase1, message)
	if err != nil {
		t.Fatal(err)
	}
	if regOut.KeyID == 0 {
		t.Fatal("expected non-zero beacon key id")
	}
	return regOut
}

func newServer(t *testing.T) *Server {
	t.Helper()

	server, err := NewServer(0)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	return server
}

func newBeacon(t *testing.T, serverPK []byte) *Beacon {
	t.Helper()

	beacon, err := NewBeacon(0, serverPK)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(beacon.Close)
	return beacon
}

func TestRegister(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)

	if registerBeacon(t, server, beacon) == nil {
		t.Fatal("expected registration to return initial message")
	}
}

func TestRegisterWithoutInitialMessageReturnsWitness(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)

	regOut := registerBeaconWithInitial(t, server, beacon, nil)
	if regOut.KeyID != 1 {
		t.Fatalf("expected first beacon key id 1, got %d", regOut.KeyID)
	}
	phase2, err := beacon.ProcessInitialMessage(regOut.Serialized)
	if err != nil {
		t.Fatal(err)
	}
	witness := []byte{0xff}
	if !bytes.Equal(phase2, witness) {
		t.Fatalf("registration witness mismatch: got %x want %x", phase2, witness)
	}
}

func TestServerFromSeedUsesStableIdentity(t *testing.T) {
	seed := bytes.Repeat([]byte{0x00}, 32)
	expectedPK := []byte{
		0x3b, 0x6a, 0x27, 0xbc, 0xce, 0xb6, 0xa4, 0x2d,
		0x62, 0xa3, 0xa8, 0xd0, 0x2a, 0x6f, 0x0d, 0x73,
		0x65, 0x32, 0x15, 0x77, 0x1d, 0xe2, 0x43, 0xa6,
		0x3a, 0xc0, 0x48, 0xa1, 0x8b, 0x59, 0xda, 0x29,
	}
	serverA, err := NewServerFromSeed(0, seed)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(serverA.Close)
	serverB, err := NewServerFromSeed(0, seed)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(serverB.Close)

	pkA, err := serverA.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	pkB, err := serverB.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(pkA, pkB) {
		t.Fatalf("seeded server public keys differ: got %x want %x", pkA, pkB)
	}
	if !bytes.Equal(pkA, expectedPK) {
		t.Fatalf("unexpected seeded server public key: got %x want %x", pkA, expectedPK)
	}
}

func TestServerCheckpointExportsRestoresAndContinues(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	response := registerBeacon(t, server, beacon)

	checkpoint, err := server.ExportState()
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.HasPrefix(checkpoint, []byte("beaconcrypt-snap")) {
		t.Fatal("checkpoint is missing the snapshot envelope")
	}
	server.Close()

	restored, err := NewServerFromState(checkpoint)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(restored.Close)
	inbound, err := beacon.EncryptToServer([]byte("after Go restore"))
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err := restored.DecryptBeaconMessage(inbound)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, []byte("after Go restore")) {
		t.Fatalf("restored plaintext mismatch: got %q", plaintext)
	}

	outbound, err := restored.EncryptToBeacon(response.KeyID, []byte("restored reply"))
	if err != nil {
		t.Fatal(err)
	}
	reply, err := beacon.DecryptServerMessage(outbound)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(reply, []byte("restored reply")) {
		t.Fatalf("restored reply mismatch: got %q", reply)
	}
	advanced, err := restored.ExportState()
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(advanced, checkpoint) {
		t.Fatal("restored checkpoint generation did not advance")
	}
}

func TestMalformedRegistrationIsRejected(t *testing.T) {
	server := newServer(t)

	if _, err := server.RegisterBeacon([]byte("not a registration"), []byte("initial")); err == nil {
		t.Fatal("expected malformed registration to be rejected")
	}
}

func TestBeaconRejectsRegistrationResponseFromWrongServer(t *testing.T) {
	expectedServer := newServer(t)
	expectedServerPK, err := expectedServer.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	wrongServer := newServer(t)
	beacon := newBeacon(t, expectedServerPK)

	phase1, err := beacon.GenerateRegistration()
	if err != nil {
		t.Fatal(err)
	}
	if _, err := expectedServer.RegisterBeacon(phase1, []byte("expected server")); err != nil {
		t.Fatal(err)
	}
	wrongResponse, err := wrongServer.RegisterBeacon(phase1, []byte("wrong server"))
	if err != nil {
		t.Fatal(err)
	}

	if _, err := beacon.ProcessInitialMessage(wrongResponse.Serialized); err == nil {
		t.Fatal("expected registration response from wrong server to be rejected")
	}
}

func TestEncryptToMultiple(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	b1 := newBeacon(t, serverPK)
	b2 := newBeacon(t, serverPK)
	message := bytes.Repeat([]byte{0x01}, 32)

	b1Registration := registerBeacon(t, server, b1)
	b2Registration := registerBeacon(t, server, b2)

	b1M1, err := server.EncryptToBeacon(b1Registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	b2M1, err := server.EncryptToBeacon(b2Registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(b1M1, b2M1) {
		t.Fatal("expected different ciphertexts for different beacons")
	}
}

func TestServerUsesPerBeaconAssociatedData(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	b1 := newBeacon(t, serverPK)
	b2 := newBeacon(t, serverPK)

	b1Registration := registerBeacon(t, server, b1)
	b2Registration := registerBeacon(t, server, b2)

	toB1, err := server.EncryptToBeacon(b1Registration.KeyID, []byte("server to b1"))
	if err != nil {
		t.Fatal(err)
	}
	toB2, err := server.EncryptToBeacon(b2Registration.KeyID, []byte("server to b2"))
	if err != nil {
		t.Fatal(err)
	}
	plainB1, err := b1.DecryptServerMessage(toB1)
	if err != nil {
		t.Fatal(err)
	}
	plainB2, err := b2.DecryptServerMessage(toB2)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plainB1, []byte("server to b1")) || !bytes.Equal(plainB2, []byte("server to b2")) {
		t.Fatalf("server-to-beacon messages mismatch: got %q and %q", plainB1, plainB2)
	}

	fromB1, err := b1.EncryptToServer([]byte("b1 to server"))
	if err != nil {
		t.Fatal(err)
	}
	fromB2, err := b2.EncryptToServer([]byte("b2 to server"))
	if err != nil {
		t.Fatal(err)
	}
	plainFromB1, err := server.DecryptBeaconMessage(fromB1)
	if err != nil {
		t.Fatal(err)
	}
	plainFromB2, err := server.DecryptBeaconMessage(fromB2)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plainFromB1, []byte("b1 to server")) || !bytes.Equal(plainFromB2, []byte("b2 to server")) {
		t.Fatalf("beacon-to-server messages mismatch: got %q and %q", plainFromB1, plainFromB2)
	}
}

func TestServerCanEncryptToBeaconAAfterRegisteringBeaconB(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beaconA := newBeacon(t, serverPK)
	beaconB := newBeacon(t, serverPK)

	beaconARegistration := registerBeacon(t, server, beaconA)
	registerBeacon(t, server, beaconB)

	message := []byte("server to beacon A after registering beacon B")
	ciphertext, err := server.EncryptToBeacon(beaconARegistration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err := beaconA.DecryptServerMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("server-to-beacon decrypt mismatch: got %q want %q", plaintext, message)
	}
}

func TestServerCanDecryptFromBeaconAAfterRegisteringBeaconB(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beaconA := newBeacon(t, serverPK)
	beaconB := newBeacon(t, serverPK)

	registerBeacon(t, server, beaconA)
	registerBeacon(t, server, beaconB)

	message := []byte("beacon A to server after registering beacon B")
	ciphertext, err := beaconA.EncryptToServer(message)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err := server.DecryptBeaconMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("beacon-to-server decrypt mismatch: got %q want %q", plaintext, message)
	}
}

func TestServerCanDecryptFromBeaconAAfterEncryptingToBeaconB(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beaconA := newBeacon(t, serverPK)
	beaconB := newBeacon(t, serverPK)

	registerBeacon(t, server, beaconA)
	beaconBRegistration := registerBeacon(t, server, beaconB)

	toBeaconB, err := server.EncryptToBeacon(beaconBRegistration.KeyID, []byte("server to beacon B"))
	if err != nil {
		t.Fatal(err)
	}
	plainToBeaconB, err := beaconB.DecryptServerMessage(toBeaconB)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plainToBeaconB, []byte("server to beacon B")) {
		t.Fatalf("server-to-beacon B decrypt mismatch: got %q", plainToBeaconB)
	}

	fromBeaconA, err := beaconA.EncryptToServer([]byte("beacon A to server"))
	if err != nil {
		t.Fatal(err)
	}
	plainFromBeaconA, err := server.DecryptBeaconMessage(fromBeaconA)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plainFromBeaconA, []byte("beacon A to server")) {
		t.Fatalf("beacon A-to-server decrypt mismatch: got %q", plainFromBeaconA)
	}
}

func TestEncryptMultiple(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	b1 := newBeacon(t, serverPK)
	message := bytes.Repeat([]byte{0x01}, 32)

	b1Registration := registerBeacon(t, server, b1)

	b1M1, err := server.EncryptToBeacon(b1Registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	b1M2, err := server.EncryptToBeacon(b1Registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(b1M1, b1M2) {
		t.Fatal("expected repeated encryption to produce different ciphertexts")
	}
}

func TestDecryptMultiple(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	message := bytes.Repeat([]byte{0x01}, 32)

	registration := registerBeacon(t, server, beacon)
	m1, err := server.EncryptToBeacon(registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	m2, err := server.EncryptToBeacon(registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(m1, m2) {
		t.Fatal("expected different ciphertexts")
	}

	plain1, err := beacon.DecryptServerMessage(m1)
	if err != nil {
		t.Fatal(err)
	}
	plain2, err := beacon.DecryptServerMessage(m2)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plain1, message) || !bytes.Equal(plain2, message) {
		t.Fatalf("decrypted messages mismatch: got %x and %x want %x", plain1, plain2, message)
	}
}

func TestDecryptCatchUp(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	message := bytes.Repeat([]byte{0x01}, 32)

	registration := registerBeacon(t, server, beacon)
	m1, err := server.EncryptToBeacon(registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	m2, err := server.EncryptToBeacon(registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(m1, m2) {
		t.Fatal("expected different ciphertexts")
	}

	plain2, err := beacon.DecryptServerMessage(m2)
	if err != nil {
		t.Fatal(err)
	}
	plain1, err := beacon.DecryptServerMessage(m1)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plain1, message) || !bytes.Equal(plain2, message) {
		t.Fatalf("catch-up decrypt mismatch: got %x and %x want %x", plain1, plain2, message)
	}
}

func TestBeaconEncryptsToServer(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	message := []byte("beacon to server")

	registerBeacon(t, server, beacon)
	ciphertext, err := beacon.EncryptToServer(message)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err := server.DecryptBeaconMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("beacon-to-server decrypt mismatch: got %x want %x", plaintext, message)
	}
}

func TestServerEncryptAndUpdateReturnsSerializedRatchetSnapshot(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)
	message := []byte("server to beacon with snapshot")

	update, err := server.EncryptAndUpdate(registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	if update.KeyID != registration.KeyID {
		t.Fatalf("state key ID mismatch: got %d want %d", update.KeyID, registration.KeyID)
	}
	if update.Seq != 2 {
		t.Fatalf("state sequence mismatch: got %d want 2", update.Seq)
	}
	system, role, key := decodeJSONRatchetKey(t, json.RawMessage(update.State), "send_key")
	if system != kdfStateSystemID || role != chainSendKeyRole {
		t.Fatalf(
			"state key tags mismatch: got [%d,%d] want [%d,%d]",
			system,
			role,
			kdfStateSystemID,
			chainSendKeyRole,
		)
	}
	if len(key) != ratchetStateBytes {
		t.Fatalf("state key length mismatch: got %d want %d", len(key), ratchetStateBytes)
	}
	plaintext, err := beacon.DecryptServerMessage(update.Data)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("server-to-beacon decrypt mismatch: got %q want %q", plaintext, message)
	}
}

func TestServerDecryptAndUpdateReturnsSerializedRatchetSnapshot(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)
	message := []byte("beacon to server with snapshot")

	ciphertext, err := beacon.EncryptToServer(message)
	if err != nil {
		t.Fatal(err)
	}
	update, err := server.DecryptAndUpdate(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if update.KeyID != registration.KeyID {
		t.Fatalf("state key ID mismatch: got %d want %d", update.KeyID, registration.KeyID)
	}
	if update.Seq != 1 {
		t.Fatalf("state sequence mismatch: got %d want 1", update.Seq)
	}
	system, role, key := decodeJSONRatchetKey(t, json.RawMessage(update.State), "recv_key")
	if system != kdfStateSystemID || role != chainReceiveRole {
		t.Fatalf(
			"state key tags mismatch: got [%d,%d] want [%d,%d]",
			system,
			role,
			kdfStateSystemID,
			chainReceiveRole,
		)
	}
	if len(key) != ratchetStateBytes {
		t.Fatalf("state key length mismatch: got %d want %d", len(key), ratchetStateBytes)
	}
	if !bytes.Equal(update.Data, message) {
		t.Fatalf("beacon-to-server decrypt mismatch: got %q want %q", update.Data, message)
	}
}

func TestServerEncryptAndUpdateJSONReturnsDirectionalRatchetSnapshot(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)
	message := []byte("server to beacon with JSON snapshot")

	serialized, err := server.EncryptAndUpdateJSON(registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	update := decodeJSONStateUpdate(t, serialized, "send_key")
	if update.KID != registration.KeyID {
		t.Fatalf("state key ID mismatch: got %d want %d", update.KID, registration.KeyID)
	}
	if update.Seq != 2 {
		t.Fatalf("state sequence mismatch: got %d want 2", update.Seq)
	}
	if update.KeySystem != kdfStateSystemID || update.KeyRole != chainSendKeyRole {
		t.Fatalf(
			"state key tags mismatch: got [%d,%d] want [%d,%d]",
			update.KeySystem,
			update.KeyRole,
			kdfStateSystemID,
			chainSendKeyRole,
		)
	}
	if len(update.Key) != ratchetStateBytes {
		t.Fatalf("state key length mismatch: got %d want %d", len(update.Key), ratchetStateBytes)
	}
	plaintext, err := beacon.DecryptServerMessage(update.Data)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("server-to-beacon decrypt mismatch: got %q want %q", plaintext, message)
	}
}

func TestServerDecryptAndUpdateJSONReturnsDirectionalRatchetSnapshot(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)
	message := []byte("beacon to server with JSON snapshot")

	ciphertext, err := beacon.EncryptToServer(message)
	if err != nil {
		t.Fatal(err)
	}
	serialized, err := server.DecryptAndUpdateJSON(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	update := decodeJSONStateUpdate(t, serialized, "recv_key")
	if update.KID != registration.KeyID {
		t.Fatalf("state key ID mismatch: got %d want %d", update.KID, registration.KeyID)
	}
	if update.Seq != 1 {
		t.Fatalf("state sequence mismatch: got %d want 1", update.Seq)
	}
	if update.KeySystem != kdfStateSystemID || update.KeyRole != chainReceiveRole {
		t.Fatalf(
			"state key tags mismatch: got [%d,%d] want [%d,%d]",
			update.KeySystem,
			update.KeyRole,
			kdfStateSystemID,
			chainReceiveRole,
		)
	}
	if len(update.Key) != ratchetStateBytes {
		t.Fatalf("state key length mismatch: got %d want %d", len(update.Key), ratchetStateBytes)
	}
	if !bytes.Equal(update.Data, message) {
		t.Fatalf("beacon-to-server decrypt mismatch: got %q want %q", update.Data, message)
	}
}

func TestServerJSONUpdateFailures(t *testing.T) {
	server := newServer(t)

	if _, err := server.EncryptAndUpdateJSON(^uint64(0), []byte("message")); !errors.Is(err, ErrCrypto) {
		t.Fatalf("invalid key ID error mismatch: got %v want %v", err, ErrCrypto)
	}
	if _, err := server.DecryptAndUpdateJSON([]byte("not a frame")); !errors.Is(err, ErrCrypto) {
		t.Fatalf("invalid frame error mismatch: got %v want %v", err, ErrCrypto)
	}
	if _, err := server.EncryptAndUpdateJSON(1, nil); !errors.Is(err, ErrEmptyData) {
		t.Fatalf("empty encrypt input error mismatch: got %v want %v", err, ErrEmptyData)
	}
	if _, err := server.DecryptAndUpdateJSON(nil); !errors.Is(err, ErrEmptyData) {
		t.Fatalf("empty decrypt input error mismatch: got %v want %v", err, ErrEmptyData)
	}

	server.Close()
	if _, err := server.EncryptAndUpdateJSON(1, []byte("message")); !errors.Is(err, ErrClosed) {
		t.Fatalf("closed encrypt error mismatch: got %v want %v", err, ErrClosed)
	}
	if _, err := server.DecryptAndUpdateJSON([]byte("frame")); !errors.Is(err, ErrClosed) {
		t.Fatalf("closed decrypt error mismatch: got %v want %v", err, ErrClosed)
	}
}

func TestAuthenticatedBeaconMessageRejectsTampering(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)

	registerBeacon(t, server, beacon)
	ciphertext, err := beacon.EncryptToServer([]byte("beacon to server"))
	if err != nil {
		t.Fatal(err)
	}
	ciphertext[len(ciphertext)-1] ^= 0x01

	if _, err := server.DecryptBeaconMessage(ciphertext); err == nil {
		t.Fatal("expected tampered authenticated beacon message to be rejected")
	}
}

func TestAuthenticatedServerMessageRejectsTampering(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)

	registration := registerBeacon(t, server, beacon)
	ciphertext, err := server.EncryptToBeacon(registration.KeyID, []byte("server to beacon"))
	if err != nil {
		t.Fatal(err)
	}
	ciphertext[len(ciphertext)-1] ^= 0x01

	if _, err := beacon.DecryptServerMessage(ciphertext); err == nil {
		t.Fatal("expected tampered authenticated message to be rejected")
	}
}

func TestDecryptRejectsWrongDirection(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)

	registration := registerBeacon(t, server, beacon)
	serverToBeacon, err := server.EncryptToBeacon(registration.KeyID, []byte("server to beacon"))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := server.DecryptBeaconMessage(serverToBeacon); err == nil {
		t.Fatal("expected server-to-beacon ciphertext to be rejected by beacon-message decryptor")
	}

	beaconToServer, err := beacon.EncryptToServer([]byte("beacon to server"))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := beacon.DecryptServerMessage(beaconToServer); err == nil {
		t.Fatal("expected beacon-to-server ciphertext to be rejected by server-message decryptor")
	}
}

func TestBeaconCannotDecryptMessageForDifferentBeacon(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	b1 := newBeacon(t, serverPK)
	b2 := newBeacon(t, serverPK)

	b1Registration := registerBeacon(t, server, b1)
	registerBeacon(t, server, b2)
	ciphertext, err := server.EncryptToBeacon(b1Registration.KeyID, []byte("for b1 only"))
	if err != nil {
		t.Fatal(err)
	}

	if _, err := b2.DecryptServerMessage(ciphertext); err == nil {
		t.Fatal("expected message for another beacon to be rejected")
	}
}

func TestCiphertextCannotBeReplayed(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	message := []byte("one shot")

	registration := registerBeacon(t, server, beacon)
	ciphertext, err := server.EncryptToBeacon(registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err := beacon.DecryptServerMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("replay setup decrypt mismatch: got %x want %x", plaintext, message)
	}
	if _, err := beacon.DecryptServerMessage(ciphertext); err == nil {
		t.Fatal("expected replayed ciphertext to be rejected")
	}
}

func TestBeaconCanRetryDecryptionAfterCorruptedAEADMessage(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	message := bytes.Repeat([]byte{0x01}, 32)

	registration := registerBeacon(t, server, beacon)
	ciphertext, err := server.EncryptToBeacon(registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	corrupted := corruptAEADCiphertext(t, ciphertext)

	if _, err := beacon.DecryptServerMessage(corrupted); err == nil {
		t.Fatal("expected corrupted ciphertext to be rejected")
	}
	plaintext, err := beacon.DecryptServerMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("retry decrypt mismatch: got %x want %x", plaintext, message)
	}
}

func TestServerCanRetryDecryptionAfterCorruptedAEADMessage(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	message := bytes.Repeat([]byte{0x01}, 32)

	registerBeacon(t, server, beacon)
	ciphertext, err := beacon.EncryptToServer(message)
	if err != nil {
		t.Fatal(err)
	}
	corrupted := corruptAEADCiphertext(t, ciphertext)

	if _, err := server.DecryptBeaconMessage(corrupted); err == nil {
		t.Fatal("expected corrupted ciphertext to be rejected")
	}
	plaintext, err := server.DecryptBeaconMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("retry decrypt mismatch: got %x want %x", plaintext, message)
	}
}

func TestRejectedReceiveLeavesServerCheckpointUnchanged(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	message := bytes.Repeat([]byte{0x5A}, 32)

	registerBeacon(t, server, beacon)
	ciphertext, err := beacon.EncryptToServer(message)
	if err != nil {
		t.Fatal(err)
	}
	corrupted := corruptAEADCiphertext(t, ciphertext)
	checkpoint, err := server.ExportState()
	if err != nil {
		t.Fatal(err)
	}

	if _, err := server.DecryptBeaconMessage(corrupted); err == nil {
		t.Fatal("expected corrupted ciphertext to be rejected")
	}
	afterRejection, err := server.ExportState()
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(afterRejection, checkpoint) {
		t.Fatal("rejected receive changed the exported checkpoint")
	}

	plaintext, err := server.DecryptBeaconMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("accepted plaintext mismatch: got %x want %x", plaintext, message)
	}
	afterSuccess, err := server.ExportState()
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(afterSuccess, checkpoint) {
		t.Fatal("accepted receive did not change the exported checkpoint")
	}
}

func TestConcurrentHandleUseIsSerialized(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)

	const workers = 16
	errs := make(chan error, workers*2)
	var wg sync.WaitGroup
	for range workers {
		wg.Add(2)
		go func() {
			defer wg.Done()
			_, err := server.EncryptToBeacon(registration.KeyID, []byte("server message"))
			errs <- err
		}()
		go func() {
			defer wg.Done()
			_, err := beacon.EncryptToServer([]byte("beacon message"))
			errs <- err
		}()
	}
	wg.Wait()
	close(errs)

	for err := range errs {
		if err != nil {
			t.Errorf("concurrent operation failed: %v", err)
		}
	}
}

func TestConcurrentCloseIsSafe(t *testing.T) {
	server, err := NewServer(0)
	if err != nil {
		t.Fatal(err)
	}
	serverPK, err := server.IdentityPK()
	if err != nil {
		server.Close()
		t.Fatal(err)
	}
	beacon, err := NewBeacon(0, serverPK)
	if err != nil {
		server.Close()
		t.Fatal(err)
	}

	const workers = 16
	var wg sync.WaitGroup
	for range workers {
		wg.Add(2)
		go func() {
			defer wg.Done()
			server.Close()
		}()
		go func() {
			defer wg.Done()
			beacon.Close()
		}()
	}
	wg.Wait()

	if _, err := server.IdentityPK(); !errors.Is(err, ErrClosed) {
		t.Fatalf("server operation after concurrent Close returned %v, want ErrClosed", err)
	}
	if _, err := beacon.GenerateRegistration(); !errors.Is(err, ErrClosed) {
		t.Fatalf("beacon operation after concurrent Close returned %v, want ErrClosed", err)
	}
}
