// SPDX-License-Identifier: 0BSD

package beaconcrypt

import (
	"errors"
	"testing"
)

func TestServerRetirePeerCountsAndLimit(t *testing.T) {
	server := newServer(t)
	serverPK, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	retiredBeacon := newBeacon(t, server, serverPK)
	retired := registerBeacon(t, server, retiredBeacon)
	keptBeacon := newBeacon(t, server, serverPK)
	kept := registerBeacon(t, server, keptBeacon)
	inbound, err := retiredBeacon.EncryptToServer([]byte("after retirement"))
	if err != nil {
		t.Fatal(err)
	}

	if removed, err := server.RetirePeer(retired.KeyID); err != nil || !removed {
		t.Fatalf("retire: %v %v", removed, err)
	}
	if removed, err := server.RetirePeer(retired.KeyID); err != nil || removed {
		t.Fatalf("second retire: %v %v", removed, err)
	}
	if peers, markers, err := server.PeerCounts(); err != nil || peers != 1 || markers != 2 {
		t.Fatalf("counts: %d %d %v", peers, markers, err)
	}
	if _, err := server.DecryptBeaconMessage(inbound); !errors.Is(err, ErrCrypto) {
		t.Fatalf("retired inbound: %v", err)
	}
	if _, err := server.EncryptToBeacon(retired.KeyID, []byte("tasking")); !errors.Is(err, ErrCrypto) {
		t.Fatalf("retired outbound: %v", err)
	}
	frame, err := server.EncryptToBeacon(kept.KeyID, []byte("kept"))
	if err != nil {
		t.Fatal(err)
	}
	if plain, err := keptBeacon.DecryptServerMessage(frame); err != nil || string(plain) != "kept" {
		t.Fatalf("kept peer: %q %v", plain, err)
	}

	if err := server.SetMaxPeers(1); err != nil {
		t.Fatal(err)
	}
	waiting := newBeacon(t, server, serverPK)
	bundle, err := waiting.GenerateRegistration()
	if err != nil {
		t.Fatal(err)
	}
	var persistence *PersistenceError
	if _, err := server.RegisterBeacon(bundle, nil); !errors.As(err, &persistence) || persistence.Code != StatusCapacity {
		t.Fatalf("limit: %v", err)
	}
	if server.IsPoisoned() {
		t.Fatal("capacity refusal poisoned the server")
	}
	if err := server.SetMaxPeers(0); err != nil {
		t.Fatal(err)
	}
	// The refused registration consumed nothing and can be retried unchanged.
	response, err := server.RegisterBeacon(bundle, []byte("late"))
	if err != nil || response.KeyID <= kept.KeyID {
		t.Fatalf("retry after limit: %+v %v", response, err)
	}
	if plain, err := waiting.ProcessInitialMessage(response.Serialized); err != nil || string(plain) != "late" {
		t.Fatalf("late registration: %q %v", plain, err)
	}
	if peers, markers, err := server.PeerCounts(); err != nil || peers != 2 || markers != 3 {
		t.Fatalf("final counts: %d %d %v", peers, markers, err)
	}
	server.Close()
	if _, _, err := server.PeerCounts(); !errors.Is(err, ErrClosed) {
		t.Fatalf("closed counts: %v", err)
	}
	if _, err := server.RetirePeer(kept.KeyID); !errors.Is(err, ErrClosed) {
		t.Fatalf("closed retire: %v", err)
	}
}
