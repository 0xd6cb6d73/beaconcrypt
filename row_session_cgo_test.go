// SPDX-License-Identifier: 0BSD
//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

import (
	"bytes"
	"errors"
	"reflect"
	"testing"
)

func TestRowTransactionAtomicResultRecoveryAndExpiredSession(t *testing.T) {
	server, store, _ := newRowTestServer(t)
	beacon, kid, _ := registerRowBeacon(t, server)
	frame, err := beacon.EncryptToServer([]byte("inbound"))
	if err != nil {
		t.Fatal(err)
	}
	var retained *RowSession
	transitions := 0
	operation := func(session *RowSession) ([]byte, error) {
		retained = session
		cached, err := session.Load([]byte("result"))
		if err != nil || cached != nil {
			return cached, err
		}
		value, err := session.DecryptBeaconMessage(frame)
		if err != nil {
			return nil, err
		}
		transitions++
		if !value.Changed || value.Message == nil || value.Message.KeyID != kid || value.Message.Seq != 1 {
			t.Fatalf("pending receive: %+v", value)
		}
		response := append([]byte("exact application response: "), value.Message.Data...)
		if err := session.Store([]byte("result"), response); err != nil {
			return nil, err
		}
		if err := session.Store(nil, []byte{}); err != nil {
			return nil, err
		}
		empty, err := session.Load(nil)
		if err != nil || empty == nil || len(empty) != 0 {
			t.Fatalf("present empty application row: %v %v", empty, err)
		}
		return response, nil
	}
	store.failAfterCommit = true
	if output, err := server.Transaction(operation); output != nil || !errors.Is(err, errRowCommit) {
		t.Fatalf("unknown commit: %q %v", output, err)
	}
	for key, value := range store.database.rows {
		if value == nil {
			t.Fatalf("present row %q reached the store as nil", key)
		}
	}
	if _, err := retained.Load(nil); !errors.Is(err, ErrRowSessionExpired) {
		t.Fatalf("retained session: %v", err)
	}
	store.failAfterCommit = false
	output, err := server.Transaction(operation)
	if err != nil || string(output) != "exact application response: inbound" || transitions != 1 {
		t.Fatalf("recovery: %q %v, transitions=%d", output, err, transitions)
	}
	if _, err := server.DecryptBeaconMessage(frame); !errors.Is(err, ErrCrypto) {
		t.Fatalf("receive replay: %v", err)
	}
	if empty, err := server.Transaction(func(*RowSession) ([]byte, error) { return nil, nil }); err != nil || empty == nil || len(empty) != 0 {
		t.Fatalf("empty callback result: %v %v", empty, err)
	}
}

func TestRowTransactionCallbackFailureAndCaughtSessionErrorRollback(t *testing.T) {
	server, store, _ := newRowTestServer(t)
	_, kid, _ := registerRowBeacon(t, server)
	before := store.database.rows
	callbackFailure := errors.New("application encoding failed")
	output, err := server.Transaction(func(session *RowSession) ([]byte, error) {
		if err := session.Store([]byte("pending"), []byte("metadata")); err != nil {
			return nil, err
		}
		if _, err := session.EncryptToBeacon(kid, []byte("pending")); err != nil {
			return nil, err
		}
		return nil, callbackFailure
	})
	if output != nil || !errors.Is(err, callbackFailure) || !reflect.DeepEqual(before, store.database.rows) {
		t.Fatalf("callback rollback: %q %v", output, err)
	}
	output, err = server.Transaction(func(session *RowSession) ([]byte, error) {
		if _, err := session.EncryptToBeacon(kid, []byte("first")); err != nil {
			return nil, err
		}
		if _, err := session.EncryptToBeacon(kid, []byte("second")); err == nil {
			t.Fatal("second native attempt accepted")
		}
		return []byte("ignored failure"), nil
	})
	var persistence *PersistenceError
	if output != nil || !errors.As(err, &persistence) || persistence.Code != StatusInvalidSession || !reflect.DeepEqual(before, store.database.rows) {
		t.Fatalf("caught session error committed: %q %v", output, err)
	}
	output, err = server.Transaction(func(*RowSession) ([]byte, error) { panic("application panic") })
	if output != nil || !errors.As(err, &persistence) || persistence.Cause == nil {
		t.Fatalf("callback panic: %q %v", output, err)
	}
	next, err := server.EncryptToBeaconWithMetadata(kid, []byte("retry"))
	if err != nil || next.Seq != 2 {
		t.Fatalf("failed transition consumed sequence: %+v %v", next, err)
	}
}

func TestRowRegistrationTransactionPhasesAndCachedResult(t *testing.T) {
	server, store, _ := newRowTestServer(t)
	pk, _ := server.IdentityPK()
	ml, _ := server.MLDSAPublicKey()
	beacon, err := NewBeacon(19, pk, ml)
	if err != nil {
		t.Fatal(err)
	}
	defer beacon.Close()
	request, err := beacon.GenerateRegistration()
	if err != nil {
		t.Fatal(err)
	}
	var retained *RowSession
	accept := func(session *RowSession) (RowRegistrationDecision, error) {
		retained = session
		cached, err := session.Load([]byte("response"))
		if err != nil || cached != nil {
			return RowRegistrationDecision{Data: cached}, err
		}
		accepted, err := session.AcceptRegistration(request)
		if err != nil {
			return RowRegistrationDecision{}, err
		}
		if !accepted {
			return RowRegistrationDecision{}, errors.New("registration already accepted without result")
		}
		if err := session.Store([]byte("status"), []byte("accepted")); err != nil {
			return RowRegistrationDecision{}, err
		}
		return RowRegistrationDecision{Continue: true, Data: []byte("initial")}, nil
	}
	completions := 0
	finish := func(session *RowSession, input []byte) ([]byte, error) {
		completions++
		if _, err := retained.Load(nil); !errors.Is(err, ErrRowSessionExpired) {
			t.Fatalf("acceptance session remains active: %v", err)
		}
		accepted, err := session.Load([]byte("status"))
		if err != nil || !bytes.Equal(accepted, []byte("accepted")) {
			t.Fatalf("acceptance not visible: %q %v", accepted, err)
		}
		value, err := session.CompleteRegistration(input)
		if err != nil {
			return nil, err
		}
		if !value.Changed || value.Message == nil || value.Message.Seq != 1 {
			t.Fatalf("completion: %+v", value)
		}
		if err := session.Store([]byte("response"), value.Message.Data); err != nil {
			return nil, err
		}
		return value.Message.Data, nil
	}
	output, err := server.RegistrationTransaction(accept, finish)
	if err != nil {
		t.Fatal(err)
	}
	plain, err := beacon.ProcessInitialMessage(output)
	if err != nil || string(plain) != "initial" {
		t.Fatalf("registration response: %q %v", plain, err)
	}
	cached, err := server.RegistrationTransaction(accept, finish)
	if err != nil || !bytes.Equal(cached, output) || completions != 1 {
		t.Fatalf("cached registration: %v, completions=%d", err, completions)
	}

	store.failCommit = true
	_, err = server.RegistrationTransaction(func(*RowSession) (RowRegistrationDecision, error) {
		return RowRegistrationDecision{Data: []byte("cached")}, nil
	}, finish)
	var phase *RowRegistrationError
	if !errors.As(err, &phase) || phase.Phase != RowAcceptance || !errors.Is(err, errRowCommit) {
		t.Fatalf("acceptance phase: %v", err)
	}
}

func TestRowRegistrationCompletionFailurePreservesAcceptedApplicationRow(t *testing.T) {
	server, _, _ := newRowTestServer(t)
	pk, _ := server.IdentityPK()
	ml, _ := server.MLDSAPublicKey()
	beacon, err := NewBeacon(19, pk, ml)
	if err != nil {
		t.Fatal(err)
	}
	defer beacon.Close()
	request, err := beacon.GenerateRegistration()
	if err != nil {
		t.Fatal(err)
	}
	failure := errors.New("completion encoding failed")
	_, err = server.RegistrationTransaction(func(session *RowSession) (RowRegistrationDecision, error) {
		accepted, err := session.AcceptRegistration(request)
		if err != nil {
			return RowRegistrationDecision{}, err
		}
		if !accepted {
			t.Fatal("fresh registration rejected")
		}
		if err := session.Store([]byte("incomplete"), []byte("accepted")); err != nil {
			return RowRegistrationDecision{}, err
		}
		return RowRegistrationDecision{Continue: true}, nil
	}, func(session *RowSession, _ []byte) ([]byte, error) {
		if _, err := session.CompleteRegistration([]byte("pending")); err != nil {
			return nil, err
		}
		return nil, failure
	})
	var phase *RowRegistrationError
	if !errors.As(err, &phase) || phase.Phase != RowCompletion || !errors.Is(err, failure) {
		t.Fatalf("completion phase: %v", err)
	}
	value, err := server.Transaction(func(session *RowSession) ([]byte, error) { return session.Load([]byte("incomplete")) })
	if err != nil || string(value) != "accepted" {
		t.Fatalf("acceptance record lost: %q %v", value, err)
	}
	if _, err := server.RegisterBeacon(request, nil); !errors.Is(err, ErrCrypto) {
		t.Fatalf("acceptance marker lost: %v", err)
	}
}

func TestRowRegistrationExplicitEmptyPayloadRecordsTerminalFailure(t *testing.T) {
	server, _, _ := newRowTestServer(t)
	pk, _ := server.IdentityPK()
	ml, _ := server.MLDSAPublicKey()
	beacon, err := NewBeacon(19, pk, ml)
	if err != nil {
		t.Fatal(err)
	}
	defer beacon.Close()
	request, err := beacon.GenerateRegistration()
	if err != nil {
		t.Fatal(err)
	}
	output, err := server.RegistrationTransaction(func(session *RowSession) (RowRegistrationDecision, error) {
		accepted, err := session.AcceptRegistration(request)
		if err != nil {
			return RowRegistrationDecision{}, err
		}
		if !accepted {
			t.Fatal("fresh registration rejected")
		}
		return RowRegistrationDecision{Continue: true, Data: []byte{}}, nil
	}, func(session *RowSession, context []byte) ([]byte, error) {
		if len(context) != 0 {
			t.Fatal("empty context changed")
		}
		value, err := session.CompleteRegistration([]byte{})
		if err != nil {
			return nil, err
		}
		if value.Message != nil || value.Changed {
			t.Fatalf("empty payload became absent payload: %+v", value)
		}
		if err := session.Store([]byte("outcome"), []byte("terminal failure")); err != nil {
			return nil, err
		}
		return []byte("terminal failure"), nil
	})
	if err != nil || string(output) != "terminal failure" {
		t.Fatalf("terminal result: %q %v", output, err)
	}
	if _, err := server.RegisterBeacon(request, []byte("retry")); !errors.Is(err, ErrCrypto) {
		t.Fatalf("registration marker lost: %v", err)
	}
}

type reentrantRowStore struct {
	*rowTestStore
	session   *RowSession
	attempted bool
	writes    int
}

func (s *reentrantRowStore) Store(key, value []byte) error {
	s.writes++
	return s.rowTestStore.Store(key, value)
}

func (s *reentrantRowStore) Load(key []byte) ([]byte, error) {
	if s.session != nil && !s.attempted {
		s.attempted = true
		if err := s.session.Store([]byte("recursive"), []byte("discarded")); err == nil {
			return nil, errors.New("recursive session call was accepted")
		}
		// Deliberately swallow the recursion error; the outer bridge must still abort.
	}
	return s.rowTestStore.Load(key)
}

func TestRowTransactionRejectsRecursiveSessionWithoutDeadlock(t *testing.T) {
	_, base, lineage := newRowTestServer(t)
	store := &reentrantRowStore{rowTestStore: &rowTestStore{database: base.database}}
	server, err := OpenRowServer(store, lineage)
	if err != nil {
		t.Fatal(err)
	}
	defer server.Close()
	before := base.database.rows
	output, err := server.Transaction(func(session *RowSession) ([]byte, error) {
		store.session = session
		if err := session.Store([]byte("pending"), []byte("discarded")); err != nil {
			return nil, err
		}
		if _, err := session.Load([]byte("trigger")); err != nil {
			return nil, err
		}
		if err := session.Store([]byte("after recursion"), []byte("must not reach storage")); err == nil {
			return nil, errors.New("session ignored its earlier recursion failure")
		}
		return []byte("must not commit"), nil
	})
	var outer, cause *PersistenceError
	if !store.attempted || output != nil || !errors.As(err, &outer) || !errors.As(outer.Cause, &cause) || cause.Code != StatusInvalidSession {
		t.Fatalf("recursive callback outcome: %q %v", output, err)
	}
	if !reflect.DeepEqual(before, base.database.rows) {
		t.Fatal("recursive callback committed application writes")
	}
	if store.writes != 1 {
		t.Fatalf("storage writes after recursion failure: got %d, want only the preceding write", store.writes)
	}
	if _, err := store.session.Load(nil); !errors.Is(err, ErrRowSessionExpired) {
		t.Fatalf("recursive callback retained session: %v", err)
	}
}
