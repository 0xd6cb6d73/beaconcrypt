// SPDX-License-Identifier: 0BSD

package beaconcrypt

import (
	"bytes"
	"testing"
)

func registerBeacon(t *testing.T, server *Server, beacon *Beacon) []byte {
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
	return phase2
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

func TestRegisterWithoutInitialMessage(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)

	regOut := registerBeaconWithInitial(t, server, beacon, nil)
	phase2, err := beacon.ProcessInitialMessage(regOut.Serialized)
	if err != nil {
		t.Fatal(err)
	}
	if len(phase2) != 0 {
		t.Fatalf("expected empty initial message, got %x", phase2)
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

	b1Initial := registerBeacon(t, server, b1)
	b2Initial := registerBeacon(t, server, b2)
	if !bytes.Equal(b2Initial, b1Initial) {
		t.Fatalf("initial messages differ: got %x want %x", b2Initial, b1Initial)
	}

	b1M1, err := server.EncryptToBeacon(1, message)
	if err != nil {
		t.Fatal(err)
	}
	b2M1, err := server.EncryptToBeacon(2, message)
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(b1M1, b2M1) {
		t.Fatal("expected different ciphertexts for different beacons")
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

	registerBeacon(t, server, b1)

	b1M1, err := server.EncryptToBeacon(1, message)
	if err != nil {
		t.Fatal(err)
	}
	b1M2, err := server.EncryptToBeacon(1, message)
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

	registerBeacon(t, server, beacon)
	m1, err := server.EncryptToBeacon(1, message)
	if err != nil {
		t.Fatal(err)
	}
	m2, err := server.EncryptToBeacon(1, message)
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

func TestDecryptMultipleSigned(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	message := bytes.Repeat([]byte{0x01}, 32)

	registerBeacon(t, server, beacon)
	m1, err := server.EncryptToBeaconSigned(1, message)
	if err != nil {
		t.Fatal(err)
	}
	m2, err := server.EncryptToBeaconSigned(1, message)
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(m1, m2) {
		t.Fatal("expected different signed ciphertexts")
	}

	plain1, err := beacon.DecryptServerMessageSigned(m1)
	if err != nil {
		t.Fatal(err)
	}
	plain2, err := beacon.DecryptServerMessageSigned(m2)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plain1, message) || !bytes.Equal(plain2, message) {
		t.Fatalf("decrypted signed messages mismatch: got %x and %x want %x", plain1, plain2, message)
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

	registerBeacon(t, server, beacon)
	m1, err := server.EncryptToBeacon(1, message)
	if err != nil {
		t.Fatal(err)
	}
	m2, err := server.EncryptToBeacon(1, message)
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
	plaintext, err := server.DecryptBeaconMessage(1, ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("beacon-to-server decrypt mismatch: got %x want %x", plaintext, message)
	}
}

func TestBeaconEncryptsToServerSigned(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	message := []byte("signed beacon to server")

	registerBeacon(t, server, beacon)
	signed, err := beacon.EncryptToServerSigned(message)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err := server.DecryptBeaconMessageSigned(signed)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("signed beacon-to-server decrypt mismatch: got %x want %x", plaintext, message)
	}
}

func TestSignedServerMessageRejectsTampering(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)

	registerBeacon(t, server, beacon)
	signed, err := server.EncryptToBeaconSigned(1, []byte("server to beacon"))
	if err != nil {
		t.Fatal(err)
	}
	signed[len(signed)-1] ^= 0x01

	if _, err := beacon.DecryptServerMessageSigned(signed); err == nil {
		t.Fatal("expected tampered signed message to be rejected")
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

	registerBeacon(t, server, b1)
	registerBeacon(t, server, b2)
	ciphertext, err := server.EncryptToBeacon(1, []byte("for b1 only"))
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

	registerBeacon(t, server, beacon)
	ciphertext, err := server.EncryptToBeacon(1, message)
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
