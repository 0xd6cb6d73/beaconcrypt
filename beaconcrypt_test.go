// SPDX-License-Identifier: 0BSD

package beaconcrypt

import (
	"bytes"
	"encoding/json"
	"errors"
	"reflect"
	"strconv"
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
	State     json.RawMessage
	KeySystem uint8
	KeyRole   uint8
	Key       []byte
	Data      []byte
}

func decodeJSONStateUpdate(t *testing.T, serialized string, keyField string) jsonStateUpdate {
	t.Helper()

	var encoded struct {
		KID   uint64          `json:"kid"`
		Seq   uint64          `json:"seq"`
		State json.RawMessage `json:"state"`
		Data  []byte          `json:"data"`
	}
	if err := json.Unmarshal([]byte(serialized), &encoded); err != nil {
		t.Fatalf("state update is not valid JSON: %v", err)
	}
	system, role, keyBytes := decodeJSONRatchetKey(t, encoded.State, keyField)
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

func assertJSONEqual(t *testing.T, left, right string) {
	t.Helper()

	var leftValue, rightValue any
	if err := json.Unmarshal([]byte(left), &leftValue); err != nil {
		t.Fatalf("left value is not valid JSON: %v", err)
	}
	if err := json.Unmarshal([]byte(right), &rightValue); err != nil {
		t.Fatalf("right value is not valid JSON: %v", err)
	}
	if !reflect.DeepEqual(leftValue, rightValue) {
		t.Fatalf("JSON values differ:\nleft:  %s\nright: %s", left, right)
	}
}

func mutateJSONObject(t *testing.T, serialized string, mutate func(map[string]any)) string {
	t.Helper()

	var value map[string]any
	if err := json.Unmarshal([]byte(serialized), &value); err != nil {
		t.Fatal(err)
	}
	mutate(value)
	mutated, err := json.Marshal(value)
	if err != nil {
		t.Fatal(err)
	}
	return string(mutated)
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

func TestServerEncryptAndUpdateReturnsRatchetState(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)
	message := []byte("server to beacon with updated state")

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

func TestServerDecryptAndUpdateReturnsRatchetState(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)
	message := []byte("beacon to server with updated state")

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

func TestStructuredAndJSONUpdatesMatchAcrossTheCGoBoundary(t *testing.T) {
	seed := bytes.Repeat([]byte{0x31}, 32)
	server, err := NewServerFromSeed(0, seed)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)
	initialState, err := server.ExportState()
	if err != nil {
		t.Fatal(err)
	}

	structuredServer, err := NewServerFromState(0, seed, initialState)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(structuredServer.Close)
	jsonServer, err := NewServerFromState(0, seed, initialState)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(jsonServer.Close)

	outbound := []byte("compare structured and JSON encryption updates")
	structuredSend, err := structuredServer.EncryptAndUpdate(registration.KeyID, outbound)
	if err != nil {
		t.Fatal(err)
	}
	serializedSend, err := jsonServer.EncryptAndUpdateJSON(registration.KeyID, outbound)
	if err != nil {
		t.Fatal(err)
	}
	jsonSend := decodeJSONStateUpdate(t, serializedSend, "send_key")
	if structuredSend.KeyID != jsonSend.KID || structuredSend.Seq != jsonSend.Seq {
		t.Fatalf(
			"send update metadata mismatch: structured [%d,%d] JSON [%d,%d]",
			structuredSend.KeyID,
			structuredSend.Seq,
			jsonSend.KID,
			jsonSend.Seq,
		)
	}
	if !bytes.Equal(structuredSend.Data, jsonSend.Data) {
		t.Fatalf("send update data mismatch: got %x want %x", structuredSend.Data, jsonSend.Data)
	}
	assertJSONEqual(t, structuredSend.State, string(jsonSend.State))

	inbound := []byte("compare structured and JSON decryption updates")
	ciphertext, err := beacon.EncryptToServer(inbound)
	if err != nil {
		t.Fatal(err)
	}
	structuredRecv, err := structuredServer.DecryptAndUpdate(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	serializedRecv, err := jsonServer.DecryptAndUpdateJSON(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	jsonRecv := decodeJSONStateUpdate(t, serializedRecv, "recv_key")
	if structuredRecv.KeyID != jsonRecv.KID || structuredRecv.Seq != jsonRecv.Seq {
		t.Fatalf(
			"receive update metadata mismatch: structured [%d,%d] JSON [%d,%d]",
			structuredRecv.KeyID,
			structuredRecv.Seq,
			jsonRecv.KID,
			jsonRecv.Seq,
		)
	}
	if !bytes.Equal(structuredRecv.Data, jsonRecv.Data) {
		t.Fatalf("receive update data mismatch: got %x want %x", structuredRecv.Data, jsonRecv.Data)
	}
	assertJSONEqual(t, structuredRecv.State, string(jsonRecv.State))
}

func TestServerEncryptAndUpdateJSONReturnsDirectionalRatchetState(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)
	message := []byte("server to beacon with JSON state")

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

func TestServerDecryptAndUpdateJSONReturnsDirectionalRatchetState(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)
	message := []byte("beacon to server with JSON state")

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
	if _, err := server.ExportState(); !errors.Is(err, ErrClosed) {
		t.Fatalf("closed export error mismatch: got %v want %v", err, ErrClosed)
	}
}

func TestServerStateRoundTripContinuesSessionsAndKeyIDs(t *testing.T) {
	seed := bytes.Repeat([]byte{0x51}, 32)
	server, err := NewServerFromSeed(0, seed)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beaconA := newBeacon(t, serverPK)
	registrationA := registerBeacon(t, server, beaconA)

	beforeRestoreToBeacon := []byte("server message before restore")
	ciphertext, err := server.EncryptToBeacon(registrationA.KeyID, beforeRestoreToBeacon)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err := beaconA.DecryptServerMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, beforeRestoreToBeacon) {
		t.Fatalf("pre-restore server message mismatch: got %q want %q", plaintext, beforeRestoreToBeacon)
	}

	beforeRestoreToServer := []byte("beacon message before restore")
	ciphertext, err = beaconA.EncryptToServer(beforeRestoreToServer)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err = server.DecryptBeaconMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, beforeRestoreToServer) {
		t.Fatalf("pre-restore beacon message mismatch: got %q want %q", plaintext, beforeRestoreToServer)
	}

	state, err := server.ExportState()
	if err != nil {
		t.Fatal(err)
	}
	if !json.Valid([]byte(state)) {
		t.Fatalf("exported state is not valid JSON: %q", state)
	}
	server.Close()

	restored, err := NewServerFromState(0, seed, state)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(restored.Close)
	restoredPK, err := restored.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(restoredPK, serverPK) {
		t.Fatalf("restored server identity mismatch: got %x want %x", restoredPK, serverPK)
	}

	afterRestoreToBeacon := []byte("server message after restore")
	ciphertext, err = restored.EncryptToBeacon(registrationA.KeyID, afterRestoreToBeacon)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err = beaconA.DecryptServerMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, afterRestoreToBeacon) {
		t.Fatalf("restored server message mismatch: got %q want %q", plaintext, afterRestoreToBeacon)
	}

	afterRestoreToServer := []byte("beacon message after restore")
	ciphertext, err = beaconA.EncryptToServer(afterRestoreToServer)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err = restored.DecryptBeaconMessage(ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, afterRestoreToServer) {
		t.Fatalf("restored beacon message mismatch: got %q want %q", plaintext, afterRestoreToServer)
	}

	beaconB := newBeacon(t, restoredPK)
	registrationB := registerBeacon(t, restored, beaconB)
	if registrationB.KeyID != registrationA.KeyID+1 {
		t.Fatalf(
			"restored next key ID mismatch: got %d want %d",
			registrationB.KeyID,
			registrationA.KeyID+1,
		)
	}
}

func TestServerStateRoundTripPreservesCachedOutOfOrderReceiveKeys(t *testing.T) {
	seed := bytes.Repeat([]byte{0x71}, 32)
	server, err := NewServerFromSeed(0, seed)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registration := registerBeacon(t, server, beacon)

	messages := [][]byte{[]byte("first"), []byte("second"), []byte("third")}
	ciphertexts := make([][]byte, len(messages))
	for index, message := range messages {
		ciphertexts[index], err = beacon.EncryptToServer(message)
		if err != nil {
			t.Fatal(err)
		}
	}
	plaintext, err := server.DecryptBeaconMessage(ciphertexts[2])
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, messages[2]) {
		t.Fatalf("out-of-order plaintext mismatch: got %q want %q", plaintext, messages[2])
	}

	state, err := server.ExportState()
	if err != nil {
		t.Fatal(err)
	}
	var encoded map[string]struct {
		Ratchet struct {
			RecvPast map[string]json.RawMessage `json:"recv_past"`
		} `json:"ratchet"`
	}
	if err := json.Unmarshal([]byte(state), &encoded); err != nil {
		t.Fatal(err)
	}
	cached := encoded[strconv.FormatUint(registration.KeyID, 10)].Ratchet.RecvPast
	if len(cached) != 2 || cached["1"] == nil || cached["2"] == nil {
		t.Fatalf("cached receive keys mismatch: got keys %v want [1 2]", reflect.ValueOf(cached).MapKeys())
	}

	restored, err := NewServerFromState(0, seed, state)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(restored.Close)
	for index := 0; index < 2; index++ {
		plaintext, err = restored.DecryptBeaconMessage(ciphertexts[index])
		if err != nil {
			t.Fatal(err)
		}
		if !bytes.Equal(plaintext, messages[index]) {
			t.Fatalf(
				"restored cached plaintext %d mismatch: got %q want %q",
				index,
				plaintext,
				messages[index],
			)
		}
	}
}

func TestServerFromEmptyStateAllowsNilSeed(t *testing.T) {
	const serverKID = 7

	server, err := NewServerFromState(serverKID, nil, "{}")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	state, err := server.ExportState()
	if err != nil {
		t.Fatal(err)
	}
	if state != "{}" {
		t.Fatalf("empty state mismatch: got %q want %q", state, "{}")
	}

	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon, err := NewBeacon(serverKID, serverPK)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(beacon.Close)
	registration := registerBeacon(t, server, beacon)
	if registration.KeyID != serverKID+1 {
		t.Fatalf("first key ID mismatch: got %d want %d", registration.KeyID, serverKID+1)
	}
}

func TestNewServerFromStateRejectsInvalidInput(t *testing.T) {
	seed := bytes.Repeat([]byte{0x61}, 32)
	if _, err := NewServerFromState(0, seed[:31], "{}"); !errors.Is(err, ErrSeedSize) {
		t.Fatalf("invalid seed error mismatch: got %v want %v", err, ErrSeedSize)
	}
	if _, err := NewServerFromState(0, seed, ""); !errors.Is(err, ErrEmptyData) {
		t.Fatalf("empty state error mismatch: got %v want %v", err, ErrEmptyData)
	}

	invalidStates := []string{
		"not JSON",
		string([]byte{0xff}),
		`{"1":{"pk":[],"ratchet":{}}}`,
	}
	for _, state := range invalidStates {
		if server, err := NewServerFromState(0, seed, state); !errors.Is(err, ErrCrypto) {
			if server != nil {
				server.Close()
			}
			t.Fatalf("invalid state %q error mismatch: got %v want %v", state, err, ErrCrypto)
		}
	}
}

func TestNewServerFromStateRejectsTamperedExportedState(t *testing.T) {
	seed := bytes.Repeat([]byte{0x61}, 32)
	server, err := NewServerFromSeed(0, seed)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	registerBeacon(t, server, beacon)
	state, err := server.ExportState()
	if err != nil {
		t.Fatal(err)
	}

	wrongKeyType := mutateJSONObject(t, state, func(value map[string]any) {
		value["1"].(map[string]any)["pk"].([]any)[0] = float64(2)
	})
	shortKey := mutateJSONObject(t, state, func(value map[string]any) {
		principal := value["1"].(map[string]any)
		publicKey := principal["pk"].([]any)
		principal["pk"] = publicKey[:len(publicKey)-1]
	})
	malformedRatchet := mutateJSONObject(t, state, func(value map[string]any) {
		principal := value["1"].(map[string]any)
		ratchet := principal["ratchet"].(map[string]any)
		ratchet["send_key"].([]any)[0] = float64(0)
	})
	entry := state[1 : len(state)-1]
	duplicateKID := "{" + entry + "," + entry + "}"

	for _, malformed := range []string{
		wrongKeyType,
		shortKey,
		malformedRatchet,
		duplicateKID,
	} {
		restored, err := NewServerFromState(0, seed, malformed)
		if restored != nil {
			restored.Close()
		}
		if !errors.Is(err, ErrCrypto) {
			t.Fatalf("tampered state was not rejected: state %q error %v", malformed, err)
		}
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
