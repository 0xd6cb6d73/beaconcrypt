// SPDX-License-Identifier: 0BSD

package beaconcrypt

import (
	"bytes"
	"testing"
)

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

func TestRegisterWithoutInitialMessage(t *testing.T) {
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
	if len(phase2) != 0 {
		t.Fatalf("expected empty initial message, got %x", phase2)
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
	plainFromB1, err := server.DecryptBeaconMessage(b1Registration.KeyID, fromB1)
	if err != nil {
		t.Fatal(err)
	}
	plainFromB2, err := server.DecryptBeaconMessage(b2Registration.KeyID, fromB2)
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

	beaconARegistration := registerBeacon(t, server, beaconA)
	registerBeacon(t, server, beaconB)

	message := []byte("beacon A to server after registering beacon B")
	ciphertext, err := beaconA.EncryptToServer(message)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err := server.DecryptBeaconMessage(beaconARegistration.KeyID, ciphertext)
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

	beaconARegistration := registerBeacon(t, server, beaconA)
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
	plainFromBeaconA, err := server.DecryptBeaconMessage(beaconARegistration.KeyID, fromBeaconA)
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

func TestDecryptMultipleSigned(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)
	message := bytes.Repeat([]byte{0x01}, 32)

	registration := registerBeacon(t, server, beacon)
	m1, err := server.EncryptToBeaconSigned(registration.KeyID, message)
	if err != nil {
		t.Fatal(err)
	}
	m2, err := server.EncryptToBeaconSigned(registration.KeyID, message)
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

	registration := registerBeacon(t, server, beacon)
	ciphertext, err := beacon.EncryptToServer(message)
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err := server.DecryptBeaconMessage(registration.KeyID, ciphertext)
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

func TestSignedBeaconMessageRejectsTampering(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)

	registerBeacon(t, server, beacon)
	signed, err := beacon.EncryptToServerSigned([]byte("beacon to server"))
	if err != nil {
		t.Fatal(err)
	}
	signed[len(signed)-1] ^= 0x01

	if _, err := server.DecryptBeaconMessageSigned(signed); err == nil {
		t.Fatal("expected tampered signed beacon message to be rejected")
	}
}

func TestSignedServerMessageRejectsTampering(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, serverPK)

	registration := registerBeacon(t, server, beacon)
	signed, err := server.EncryptToBeaconSigned(registration.KeyID, []byte("server to beacon"))
	if err != nil {
		t.Fatal(err)
	}
	signed[len(signed)-1] ^= 0x01

	if _, err := beacon.DecryptServerMessageSigned(signed); err == nil {
		t.Fatal("expected tampered signed message to be rejected")
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
	if _, err := server.DecryptBeaconMessage(registration.KeyID, serverToBeacon); err == nil {
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

	registration := registerBeacon(t, server, beacon)
	ciphertext, err := beacon.EncryptToServer(message)
	if err != nil {
		t.Fatal(err)
	}
	corrupted := corruptAEADCiphertext(t, ciphertext)

	if _, err := server.DecryptBeaconMessage(registration.KeyID, corrupted); err == nil {
		t.Fatal("expected corrupted ciphertext to be rejected")
	}
	plaintext, err := server.DecryptBeaconMessage(registration.KeyID, ciphertext)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(plaintext, message) {
		t.Fatalf("retry decrypt mismatch: got %x want %x", plaintext, message)
	}
}
