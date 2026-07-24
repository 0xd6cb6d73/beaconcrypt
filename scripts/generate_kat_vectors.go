// Command generate_kat_vectors reproduces the fixed cryptographic vectors used
// by the Rust tests independently from the Python generator.
//
// Cryptographic operations are delegated to Go's crypto packages. ChaCha20-
// Poly1305, BLAKE2b, and HKDF come from the Go team's golang.org/x/crypto
// module because the repository supports Go 1.23, where they are not all
// available in the standard library. The multi-opening values are derived by
// scripts/derive_multi_opening.py and documented in
// doc/multi-opening-fixture.md.
package main

import (
	"bytes"
	"crypto/sha256"
	"crypto/sha512"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"

	"golang.org/x/crypto/blake2b"
	"golang.org/x/crypto/chacha20poly1305"
	"golang.org/x/crypto/hkdf"
)

const (
	aeadKeyLen     = chacha20poly1305.KeySize
	aeadNonceLen   = chacha20poly1305.NonceSize
	aeadTagLen     = chacha20poly1305.Overhead
	kdfStateLen    = 32
	kdfOutputLen   = aeadKeyLen + kdfStateLen + aeadNonceLen
	symRatchetInfo = "SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305"
	pqxdhInfo      = "BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768"
)

func require(condition bool, message string) {
	if !condition {
		panic(message)
	}
}

func mustHex(value string) []byte {
	decoded, err := hex.DecodeString(value)
	if err != nil {
		panic(err)
	}
	return decoded
}

func repeat(value byte, count int) []byte {
	return bytes.Repeat([]byte{value}, count)
}

func hkdfSHA512(ikm []byte, info string, length int) []byte {
	output := make([]byte, length)
	if _, err := io.ReadFull(hkdf.New(sha512.New, ikm, nil, []byte(info)), output); err != nil {
		panic(err)
	}
	return output
}

func commitment(
	key []byte,
	nonce []byte,
	associatedData []byte,
	tag []byte,
	sequence uint64,
	keyID uint64,
) []byte {
	require(len(key) == aeadKeyLen, "invalid AEAD key length")
	require(len(nonce) == aeadNonceLen, "invalid AEAD nonce length")
	require(len(tag) == aeadTagLen, "invalid AEAD tag length")

	transcript := make(
		[]byte,
		0,
		len(key)+len(nonce)+len(associatedData)+len(tag)+2*8,
	)
	transcript = append(transcript, key...)
	transcript = append(transcript, nonce...)
	transcript = append(transcript, associatedData...)
	transcript = append(transcript, tag...)

	var encodedUint64 [8]byte
	binary.LittleEndian.PutUint64(encodedUint64[:], sequence)
	transcript = append(transcript, encodedUint64[:]...)
	binary.LittleEndian.PutUint64(encodedUint64[:], keyID)
	transcript = append(transcript, encodedUint64[:]...)

	digest := blake2b.Sum512(transcript)
	return digest[:]
}

func chacha20Poly1305Encrypt(
	key []byte,
	nonce []byte,
	associatedData []byte,
	plaintext []byte,
) ([]byte, []byte) {
	aead, err := chacha20poly1305.New(key)
	if err != nil {
		panic(err)
	}
	sealed := aead.Seal(nil, nonce, plaintext, associatedData)
	tagOffset := len(sealed) - aead.Overhead()
	return sealed[:tagOffset], sealed[tagOffset:]
}

func chacha20Poly1305Decrypt(
	key []byte,
	nonce []byte,
	associatedData []byte,
	ciphertext []byte,
	tag []byte,
) []byte {
	aead, err := chacha20poly1305.New(key)
	if err != nil {
		panic(err)
	}
	sealed := make([]byte, 0, len(ciphertext)+len(tag))
	sealed = append(sealed, ciphertext...)
	sealed = append(sealed, tag...)
	plaintext, err := aead.Open(nil, nonce, sealed, associatedData)
	if err != nil {
		panic(err)
	}
	return plaintext
}

func printValue(name string, value []byte) {
	fmt.Printf("%s=%x\n", name, value)
}

func commitmentKnownAnswer() {
	key := repeat(0x11, aeadKeyLen)
	nonce := repeat(0x22, aeadNonceLen)
	associatedData := []byte("beaconcrypt-test-associated-data")
	tag := repeat(0x33, aeadTagLen)
	result := commitment(key, nonce, associatedData, tag, 0x44, 0x55)

	fmt.Println("[commitment]")
	printValue("digest", result)
}

func ratchetKnownAnswer() {
	state := repeat(0x24, kdfStateLen)

	fmt.Println("[ratchet]")
	for step := 1; step <= 2; step++ {
		output := hkdfSHA512(state, symRatchetInfo, kdfOutputLen)
		key := output[:aeadKeyLen]
		state = output[aeadKeyLen : aeadKeyLen+kdfStateLen]
		nonce := output[len(output)-aeadNonceLen:]
		printValue(fmt.Sprintf("step%d.key", step), key)
		printValue(fmt.Sprintf("step%d.state", step), state)
		printValue(fmt.Sprintf("step%d.nonce", step), nonce)
	}
}

func pqxdhRootKeyKnownAnswer() {
	ikm := make([]byte, 0, 6*32)
	for _, value := range []byte{0xff, 0x11, 0x22, 0x33, 0x44, 0x55} {
		ikm = append(ikm, repeat(value, 32)...)
	}
	result := hkdfSHA512(ikm, pqxdhInfo, kdfStateLen)

	fmt.Println("[pqxdh-root-key]")
	printValue("derived-secret", result)
}

func rfc8439AndCommitmentKnownAnswer() {
	key := mustHex(
		"808182838485868788898a8b8c8d8e8f" +
			"909192939495969798999a9b9c9d9e9f",
	)
	nonce := mustHex("070000004041424344454647")
	associatedData := mustHex("50515253c0c1c2c3c4c5c6c7")
	plaintext := []byte(
		"Ladies and Gentlemen of the class of '99: If I could offer you only " +
			"one tip for the future, sunscreen would be it.",
	)
	expectedCiphertext := mustHex(
		"d31a8d34648e60db7b86afbc53ef7ec2" +
			"a4aded51296e08fea9e2b5a736ee62d6" +
			"3dbea45e8ca9671282fafb69da92728b" +
			"1a71de0a9e060b2905d6a5b67ecd3b36" +
			"92ddbd7f2d778b8c9803aee328091b58" +
			"fab324e4fad675945585808b4831d7bc" +
			"3ff4def08e4b7a9de576d26586cec64b" +
			"6116",
	)
	expectedTag := mustHex("1ae10b594f09e26a7e902ecbd0600691")
	ciphertext, tag := chacha20Poly1305Encrypt(
		key,
		nonce,
		associatedData,
		plaintext,
	)
	require(bytes.Equal(ciphertext, expectedCiphertext), "RFC 8439 ciphertext mismatch")
	require(bytes.Equal(tag, expectedTag), "RFC 8439 tag mismatch")
	outerCommitment := commitment(
		key,
		nonce,
		associatedData,
		tag,
		0x0123456789abcdef,
		0xfedcba9876543210,
	)

	fmt.Println("[rfc8439-and-commitment]")
	printValue("ciphertext", ciphertext)
	printValue("tag", tag)
	printValue("commitment", outerCommitment)
}

func chacha20Poly1305MultiOpeningFixture() {
	const (
		attempt = uint32(1)
		carry   = 0
	)

	keyOne := make([]byte, aeadKeyLen)
	for index := range keyOne {
		keyOne[index] = byte(index)
	}
	keyTwoSeed := []byte("beaconcrypt-ctx-fixture-")
	var encodedAttempt [4]byte
	binary.LittleEndian.PutUint32(encodedAttempt[:], attempt)
	keyTwoDigest := sha256.Sum256(append(keyTwoSeed, encodedAttempt[:]...))
	keyTwo := keyTwoDigest[:]

	nonce := make([]byte, aeadNonceLen)
	for index := range nonce {
		nonce[index] = byte(index)
	}
	associatedDataOne := make([]byte, 16)
	for index := range associatedDataOne {
		associatedDataOne[index] = byte(0xf0 + index)
	}
	associatedDataTwo := mustHex("3a09eec3daf672a00f13351df1986203")
	plaintextOne := mustHex("89ea2a336d42c3373f1a954854c0e09c")
	expectedCiphertext := mustHex("00112233445566778899aabbccddeeff")
	expectedTag := mustHex("8867608090128f8c1a4711d553773215")

	ciphertext, tag := chacha20Poly1305Encrypt(
		keyOne,
		nonce,
		associatedDataOne,
		plaintextOne,
	)
	require(bytes.Equal(ciphertext, expectedCiphertext), "fixture ciphertext mismatch")
	require(bytes.Equal(tag, expectedTag), "fixture tag mismatch")
	openedPlaintextOne := chacha20Poly1305Decrypt(
		keyOne,
		nonce,
		associatedDataOne,
		ciphertext,
		tag,
	)
	require(bytes.Equal(openedPlaintextOne, plaintextOne), "first fixture plaintext mismatch")
	plaintextTwo := chacha20Poly1305Decrypt(
		keyTwo,
		nonce,
		associatedDataTwo,
		ciphertext,
		tag,
	)
	require(!bytes.Equal(plaintextOne, plaintextTwo), "fixture plaintexts must differ")
	secondCiphertext, secondTag := chacha20Poly1305Encrypt(
		keyTwo,
		nonce,
		associatedDataTwo,
		plaintextTwo,
	)
	require(bytes.Equal(secondCiphertext, ciphertext), "second fixture ciphertext mismatch")
	require(bytes.Equal(secondTag, tag), "second fixture tag mismatch")
	commitmentOne := commitment(
		keyOne,
		nonce,
		associatedDataOne,
		tag,
		1,
		7,
	)
	commitmentTwo := commitment(
		keyTwo,
		nonce,
		associatedDataTwo,
		tag,
		1,
		7,
	)
	require(!bytes.Equal(commitmentOne, commitmentTwo), "fixture commitments must differ")

	fmt.Println("[chacha20poly1305-multi-opening]")
	fmt.Printf("attempt=%d\n", attempt)
	fmt.Printf("carry=%d\n", carry)
	printValue("key1", keyOne)
	printValue("key2", keyTwo)
	printValue("nonce", nonce)
	printValue("ad1", associatedDataOne)
	printValue("ad2", associatedDataTwo)
	printValue("ciphertext", ciphertext)
	printValue("tag", tag)
	printValue("plaintext1", plaintextOne)
	printValue("plaintext2", plaintextTwo)
	printValue("commitment1", commitmentOne)
	printValue("commitment2", commitmentTwo)
}

func main() {
	commitmentKnownAnswer()
	ratchetKnownAnswer()
	pqxdhRootKeyKnownAnswer()
	rfc8439AndCommitmentKnownAnswer()
	chacha20Poly1305MultiOpeningFixture()
}
