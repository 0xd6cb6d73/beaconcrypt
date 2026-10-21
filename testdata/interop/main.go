// SPDX-License-Identifier: 0BSD

// Interop is a newline-JSON test fixture for crossing independently built Go
// backends. Byte fields use encoding/json's base64 representation. Its trusted
// checkpoint restoration is only for tests; production callers need an
// authoritative SnapshotStore and must coordinate ownership before restoring.
package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"

	beaconcrypt "github.com/0xd6cb6d73/beaconcrypt"
)

type command struct {
	Op     string `json:"op"`
	Handle uint64 `json:"handle"`
	KID    uint64 `json:"kid"`
	Data   []byte `json:"data"`
	Extra  []byte `json:"extra"`
	Seed   []byte `json:"seed"`
}

type response struct {
	Handle uint64                         `json:"handle,omitempty"`
	KID    uint64                         `json:"kid,omitempty"`
	Data   []byte                         `json:"data,omitempty"`
	Head   *beaconcrypt.SnapshotHead      `json:"head,omitempty"`
	Error  string                         `json:"error,omitempty"`
	Class  string                         `json:"class,omitempty"`
	Status *beaconcrypt.PersistenceStatus `json:"status,omitempty"`
}

type object struct {
	server *beaconcrypt.Server
	beacon *beaconcrypt.Beacon
}

func (object object) close() {
	if object.server != nil {
		object.server.Close()
	}
	if object.beacon != nil {
		object.beacon.Close()
	}
}

type fixture struct {
	next    uint64
	objects map[uint64]object
}

func main() {
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run() error {
	fixture := fixture{objects: make(map[uint64]object)}
	defer func() {
		for _, object := range fixture.objects {
			object.close()
		}
	}()
	decoder, encoder := json.NewDecoder(os.Stdin), json.NewEncoder(os.Stdout)
	for {
		var command command
		if err := decoder.Decode(&command); err != nil {
			if errors.Is(err, io.EOF) {
				return nil
			}
			return err
		}
		response, err := fixture.call(command)
		if err != nil {
			response = errorResponse(err)
		}
		if err := encoder.Encode(response); err != nil {
			return err
		}
	}
}

func (fixture *fixture) insert(object object, err error) (response, error) {
	if err != nil {
		return response{}, err
	}
	fixture.next++
	fixture.objects[fixture.next] = object
	return response{Handle: fixture.next}, nil
}

func (fixture *fixture) call(command command) (response, error) {
	switch command.Op {
	case "server-new":
		var server *beaconcrypt.Server
		var err error
		if len(command.Seed) == 0 {
			server, err = beaconcrypt.NewServer(command.KID)
		} else {
			server, err = beaconcrypt.NewServerFromSeed(command.KID, command.Seed)
		}
		return fixture.insert(object{server: server}, err)
	case "beacon-new":
		beacon, err := beaconcrypt.NewBeacon(command.KID, command.Data)
		return fixture.insert(object{beacon: beacon}, err)
	case "restore":
		server, err := beaconcrypt.NewServerFromState(command.Data)
		return fixture.insert(object{server: server}, err)
	}
	object, ok := fixture.objects[command.Handle]
	if !ok {
		return response{}, beaconcrypt.ErrClosed
	}
	var result response
	var err error
	switch command.Op {
	case "identity":
		result.Data, err = object.server.IdentityPK()
	case "registration":
		result.Data, err = object.beacon.GenerateRegistration()
	case "register":
		var registration *beaconcrypt.RegistrationResponse
		registration, err = object.server.RegisterBeacon(command.Data, command.Extra)
		if err == nil {
			result.Data, result.KID = registration.Serialized, registration.KeyID
		}
	case "finish":
		result.Data, err = object.beacon.ProcessInitialMessage(command.Data)
	case "encrypt":
		if object.server != nil {
			result.Data, err = object.server.EncryptToBeacon(command.KID, command.Data)
		} else {
			result.Data, err = object.beacon.EncryptToServer(command.Data)
		}
	case "decrypt":
		if object.server != nil {
			result.Data, err = object.server.DecryptBeaconMessage(command.Data)
		} else {
			result.Data, err = object.beacon.DecryptServerMessage(command.Data)
		}
	case "snapshot":
		result.Data, err = object.server.ExportState()
	case "head":
		var head beaconcrypt.SnapshotHead
		head, err = object.server.Head()
		if err == nil {
			result.Head = &head
		}
	case "close":
		object.close()
		delete(fixture.objects, command.Handle)
	default:
		err = fmt.Errorf("unknown operation %q", command.Op)
	}
	return result, err
}

func errorResponse(err error) response {
	result := response{Error: err.Error(), Class: "unknown"}
	var persistenceError *beaconcrypt.PersistenceError
	switch {
	case errors.As(err, &persistenceError):
		result.Class, result.Status = "persistence", &persistenceError.Code
	case errors.Is(err, beaconcrypt.ErrClosed):
		result.Class = "closed"
	case errors.Is(err, beaconcrypt.ErrCrypto):
		result.Class = "crypto"
	case errors.Is(err, beaconcrypt.ErrEmptyData):
		result.Class = "empty"
	case errors.Is(err, beaconcrypt.ErrSeedSize):
		result.Class = "seed"
	}
	return result
}
