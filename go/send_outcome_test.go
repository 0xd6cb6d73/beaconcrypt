// SPDX-License-Identifier: 0BSD

package beaconcrypt

import (
	"bytes"
	"errors"
	"testing"
)

func requireSendOutcome(t *testing.T, result *SendResult, err error, want SendOutcome) *SendResult {
	t.Helper()
	if err != nil || result == nil || result.Outcome != want {
		t.Fatalf("send result %+v, error %v, want outcome %d", result, err, want)
	}
	if result.Changed() != (want != SendRejected) {
		t.Fatal("send outcome lost its consumption effect")
	}
	return result
}

func TestRegistrationOptionalPayloadParity(t *testing.T) {
	for _, initial := range []struct {
		name string
		data []byte
	}{
		{"omitted", nil},
		{"explicit-empty", []byte{}},
		{"provided", []byte("registration application")},
	} {
		t.Run(initial.name, func(t *testing.T) {
			store := &testSnapshotStore{}
			server, err := NewServerWithStore(0, nil, nil, store)
			if err != nil {
				t.Fatal(err)
			}
			defer server.Close()
			pk, err := server.IdentityPK()
			if err != nil {
				t.Fatal(err)
			}
			beacon := newBeacon(t, server, pk)
			request, err := beacon.GenerateRegistration()
			if err != nil {
				t.Fatal(err)
			}
			_, before, calls := store.current()
			response, err := server.RegisterBeacon(request, initial.data)
			_, after, afterCalls := store.current()
			if initial.data != nil && len(initial.data) == 0 {
				if response != nil || !errors.Is(err, ErrCrypto) || server.IsPoisoned() {
					t.Fatalf("explicit empty payload did not reject normally: %+v, %v", response, err)
				}
				if after.Generation != before.Generation+1 || afterCalls != calls+1 {
					t.Fatal("empty completion lost acceptance or committed a failed response")
				}
				restored, err := RestoreServer(store)
				if err != nil {
					t.Fatal(err)
				}
				defer restored.Close()
				_, replayHead, replayCalls := store.current()
				if response, err := restored.RegisterBeacon(request, nil); response != nil || !errors.Is(err, ErrCrypto) {
					t.Fatalf("empty completion's accepted request became replayable: %+v %v", response, err)
				}
				_, finalHead, finalCalls := store.current()
				if finalHead != replayHead || finalCalls != replayCalls {
					t.Fatal("replay of empty completion created another generation")
				}
				return
			}
			if err != nil || response == nil {
				t.Fatalf("registration failed: %v", err)
			}
			plaintext, err := beacon.ProcessInitialMessage(response.Serialized)
			want := initial.data
			if want == nil {
				want = []byte{0xff}
			}
			if err != nil || !bytes.Equal(plaintext, want) {
				t.Fatalf("optional payload changed: %x, %v", plaintext, err)
			}
			if after.Generation != before.Generation+2 || afterCalls != calls+2 {
				t.Fatal("successful registration did not confirm both phases")
			}
		})
	}
}

func TestExplicitSendOutcomesAcrossBindings(t *testing.T) {
	server, beacon, kid, store := newPersistentPair(t)
	_, before, calls := store.current()
	for _, send := range []func() (*SendResult, error){
		func() (*SendResult, error) { return server.EncryptToBeaconOutcome(kid, nil) },
		func() (*SendResult, error) { return server.EncryptAndUpdateOutcome(kid, []byte{}) },
		func() (*SendResult, error) { return server.EncryptAndUpdateJSONOutcome(kid, nil) },
		func() (*SendResult, error) { return server.EncryptToBeaconOutcome(kid+500, []byte("unknown peer")) },
		func() (*SendResult, error) { return beacon.EncryptToServerOutcome(nil) },
	} {
		result, err := send()
		requireSendOutcome(t, result, err, SendRejected)
		if len(result.Data) != 0 || result.State != "" || result.KeyID != 0 || result.Seq != 0 {
			t.Fatal("rejection exposed output or metadata")
		}
	}
	_, after, afterCalls := store.current()
	if before != after || calls != afterCalls {
		t.Fatal("explicit rejection created a durable write")
	}
	for _, variant := range []string{"raw", "update", "json"} {
		var result *SendResult
		var err error
		switch variant {
		case "raw":
			result, err = server.EncryptToBeaconOutcome(kid, []byte(variant))
		case "update":
			result, err = server.EncryptAndUpdateOutcome(kid, []byte(variant))
		case "json":
			result, err = server.EncryptAndUpdateJSONOutcome(kid, []byte(variant))
		}
		requireSendOutcome(t, result, err, SendSent)
		if result.KeyID != kid || result.Seq == 0 || (variant == "update" && result.State == "") {
			t.Fatal("successful outcome lost its metadata or observation")
		}
		frame := result.Data
		if variant == "json" {
			update := decodeJSONStateUpdate(t, string(result.Data), "send_key")
			frame = update.Data
			if update.KID != result.KeyID || update.Seq != result.Seq || result.State != "" {
				t.Fatal("JSON outcome metadata does not describe its message")
			}
		}
		plaintext, err := beacon.DecryptServerMessage(frame)
		if err != nil || string(plaintext) != variant {
			t.Fatalf("outcome ciphertext failed: %q %v", plaintext, err)
		}
	}
	result, err := beacon.EncryptToServerOutcome([]byte("beacon outcome"))
	requireSendOutcome(t, result, err, SendSent)
	if result.KeyID != 0 || result.Seq != 1 {
		t.Fatal("beacon result changed destination or consumed sequence")
	}
	if plaintext, err := server.DecryptBeaconMessage(result.Data); err != nil || string(plaintext) != "beacon outcome" {
		t.Fatalf("beacon outcome was not usable: %q %v", plaintext, err)
	}
}

func TestExplicitSendOutcomesWithholdFailedCommits(t *testing.T) {
	for _, variant := range []string{"raw", "update", "json"} {
		for _, published := range []bool{false, true} {
			t.Run(variant+map[bool]string{false: "/unpublished", true: "/published"}[published], func(t *testing.T) {
				server, beacon, kid, store := newPersistentPair(t)
				sentinel := errors.New("lost send commit acknowledgement")
				_, before, _ := store.current()
				store.mu.Lock()
				if published {
					store.postCommitError = sentinel
				} else {
					store.casError = sentinel
				}
				store.mu.Unlock()
				var result *SendResult
				var err error
				switch variant {
				case "raw":
					result, err = server.EncryptToBeaconOutcome(kid, []byte("withheld"))
				case "update":
					result, err = server.EncryptAndUpdateOutcome(kid, []byte("withheld"))
				case "json":
					result, err = server.EncryptAndUpdateJSONOutcome(kid, []byte("withheld"))
				}
				requirePersistenceStatus(t, err, StatusCommitUnknown)
				if result != nil || !errors.Is(err, sentinel) || !server.IsPoisoned() {
					t.Fatalf("failed commit published an outcome or lost fencing/cause: %+v %v", result, err)
				}
				_, after, _ := store.current()
				if (after.Generation == before.Generation+1) != published {
					t.Fatal("test store publication did not match the uncertain outcome")
				}
				store.mu.Lock()
				store.casError, store.postCommitError = nil, nil
				store.mu.Unlock()
				restored, err := RestoreServer(store)
				if err != nil {
					t.Fatal(err)
				}
				defer restored.Close()
				result, err = restored.EncryptToBeaconOutcome(kid, []byte("recovered"))
				requireSendOutcome(t, result, err, SendSent)
				if plaintext, err := beacon.DecryptServerMessage(result.Data); err != nil || string(plaintext) != "recovered" {
					t.Fatalf("authoritative restoration did not recover a valid send: %q %v", plaintext, err)
				}
			})
		}
	}
}

func TestExplicitSendResultValidation(t *testing.T) {
	result, err := makeSendResult(SendConsumedWithoutOutput, nil, nil, 0, 0)
	requireSendOutcome(t, result, err, SendConsumedWithoutOutput)
	for _, invalid := range []struct {
		kind  SendOutcome
		data  []byte
		state []byte
		kid   uint64
		seq   uint64
	}{
		{3, nil, nil, 0, 0},
		{SendRejected, []byte{1}, nil, 0, 0},
		{SendConsumedWithoutOutput, nil, []byte("secret"), 0, 0},
		{SendConsumedWithoutOutput, nil, nil, 1, 1},
		{SendSent, nil, nil, 1, 1},
		{SendSent, []byte{1}, nil, 1, 0},
	} {
		if result, err := makeSendResult(invalid.kind, invalid.data, invalid.state, invalid.kid, invalid.seq); result != nil || !errors.Is(err, ErrCrypto) {
			t.Fatal("malformed foreign send outcome was accepted")
		}
	}
	var missing *SendResult
	if missing.Changed() {
		t.Fatal("missing result reported key consumption")
	}
}
