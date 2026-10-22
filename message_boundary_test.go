// SPDX-License-Identifier: 0BSD

package beaconcrypt

import (
	"bytes"
	"encoding/binary"
	"testing"
)

func encodedIntegerWidth(value uint64) int {
	switch {
	case value < 24:
		return 1
	case value <= 0xff:
		return 2
	case value <= 0xffff:
		return 3
	case value <= 0xffffffff:
		return 5
	default:
		return 9
	}
}

func encodedFrameSequence(t *testing.T, frame []byte) uint64 {
	t.Helper()
	// Array, version and message-type headers are each one byte in protocol v1.
	if len(frame) < 4 || frame[0] != 0x85 || frame[3]>>5 != 0 {
		t.Fatal("unexpected transport frame header")
	}
	switch argument := frame[3] & 31; argument {
	case 24:
		return uint64(frame[4])
	case 25:
		return uint64(binary.BigEndian.Uint16(frame[4:]))
	case 26:
		return uint64(binary.BigEndian.Uint32(frame[4:]))
	case 27:
		return binary.BigEndian.Uint64(frame[4:])
	default:
		if argument >= 24 {
			t.Fatal("invalid transport sequence")
		}
		return uint64(argument)
	}
}

func TestMessageLimitIncludesWiderSequenceMetadata(t *testing.T) {
	for _, toServer := range []bool{true, false} {
		name := "server-to-beacon"
		if toServer {
			name = "beacon-to-server"
		}
		t.Run(name, func(t *testing.T) {
			server := newServer(t)
			publicKey, err := server.IdentityPK()
			if err != nil {
				t.Fatal(err)
			}
			beacon := newBeacon(t, server, publicKey)
			registration := registerBeacon(t, server, beacon)
			sender, sequence := uint64(0), uint64(2)
			encrypt := func(message []byte) ([]byte, error) {
				return server.EncryptToBeacon(registration.KeyID, message)
			}
			decrypt := beacon.DecryptServerMessage
			if toServer {
				sender, sequence = registration.KeyID, 1
				encrypt, decrypt = beacon.EncryptToServer, server.DecryptBeaconMessage
			}
			// Sequence 24 is the first frame whose canonical sequence metadata
			// occupies two bytes rather than one.
			for ; sequence < 24; sequence++ {
				frame, err := encrypt([]byte("advance metadata width"))
				if err != nil {
					t.Fatal(err)
				}
				if _, err := decrypt(frame); err != nil {
					t.Fatal(err)
				}
			}
			// Authentication contributes 80 bytes, the array/version/type three,
			// and this ciphertext's CBOR byte-string length five.
			maximum := MaxMessageSize - 80 - 3 - 5 - encodedIntegerWidth(sequence) - encodedIntegerWidth(sender)
			message := bytes.Repeat([]byte{0x6d}, maximum+1)
			before, err := server.ExportState()
			if err != nil {
				t.Fatal(err)
			}
			if output, err := encrypt(message); output != nil || err == nil {
				t.Fatalf("oversized plaintext returned %d bytes, error %v", len(output), err)
			}
			after, err := server.ExportState()
			if err != nil || !bytes.Equal(before, after) {
				t.Fatalf("oversized send changed checkpoint: %v", err)
			}
			frame, err := encrypt(message[:maximum])
			if err != nil {
				t.Fatal(err)
			}
			if len(frame) != MaxMessageSize || encodedFrameSequence(t, frame) != sequence {
				t.Fatal("maximum frame has an incorrect size or consumed the oversized send's sequence")
			}
			oversized := make([]byte, len(frame)+1)
			copy(oversized, frame)
			before, err = server.ExportState()
			if err != nil {
				t.Fatal(err)
			}
			if output, err := decrypt(oversized); output != nil || err == nil {
				t.Fatalf("oversized frame returned %d bytes, error %v", len(output), err)
			}
			after, err = server.ExportState()
			if err != nil || !bytes.Equal(before, after) {
				t.Fatalf("oversized receive changed checkpoint: %v", err)
			}
			plaintext, err := decrypt(frame)
			if err != nil || !bytes.Equal(plaintext, message[:maximum]) {
				t.Fatalf("valid maximum frame failed after oversized input: %v", err)
			}
		})
	}
}
