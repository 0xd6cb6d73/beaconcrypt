// SPDX-License-Identifier: 0BSD

package main

import (
	"crypto/rand"
	"fmt"
	"os"

	"github.com/0xd6cb6d73/beaconcrypt"
)

const (
	serverKID     uint64 = 0
	transportPath        = "transport"
	statePath            = "server-state.bin"
)

var registrationMessage = []byte("registration ok")

func main() {
	if err := run(); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
}

func run() error {
	serverSeed := make([]byte, 32)
	if _, err := rand.Read(serverSeed); err != nil {
		return err
	}

	server, err := beaconcrypt.NewServerFromSeed(serverKID, serverSeed)
	if err != nil {
		return err
	}
	defer server.Close()
	if err := saveServer(server); err != nil {
		return err
	}

	// It is assumed that the server's public key is compiled into beacons.
	serverPK, err := server.IdentityPK()
	if err != nil {
		return err
	}
	beacon, err := beaconcrypt.NewBeacon(serverKID, serverPK)
	if err != nil {
		return err
	}
	defer beacon.Close()
	defer os.Remove(transportPath)
	defer os.Remove(statePath)

	// The beacon is run and registers.
	bReg1, err := beacon.GenerateRegistration()
	if err != nil {
		return err
	}
	// Ship the registration bytes over whichever transport you like.
	if err := writeTransport(bReg1); err != nil {
		return err
	}
	sReg1, err := readTransport()
	if err != nil {
		return err
	}

	// Now the server has the registration message and can send an initial message if needed.
	sRegResp, err := server.RegisterBeacon(sReg1, registrationMessage)
	if err != nil {
		return err
	}
	if err := saveServer(server); err != nil {
		return err
	}
	// Ship the response back over your transport.
	if err := writeTransport(sRegResp.Serialized); err != nil {
		return err
	}
	bReg1, err = readTransport()
	if err != nil {
		return err
	}

	// Do whatever you like with the initial message.
	firstMessage, err := beacon.ProcessInitialMessage(bReg1)
	if err != nil {
		return err
	}
	fmt.Printf("Beacon got initial message: %q\n", firstMessage)

	// Simulate a restart. NewServerFromState trusts these bytes as the current
	// checkpoint; they do not authenticate themselves or prevent stale rollback.
	server.Close()
	serializedState, err := os.ReadFile(statePath)
	if err != nil {
		return err
	}
	server, err = beaconcrypt.NewServerFromState(serializedState)
	if err != nil {
		return err
	}
	defer server.Close()
	if err := saveServer(server); err != nil { // Save the activation generation.
		return err
	}
	fmt.Printf("Restored server state from %s\n", statePath)

	bPing, err := beacon.EncryptToServer([]byte("ping"))
	if err != nil {
		return err
	}
	if err := writeTransport(bPing); err != nil {
		return err
	}
	sPing, err := readTransport()
	if err != nil {
		return err
	}

	// Got the ping, maybe there's a task to send now.
	ping, err := server.DecryptAndUpdate(sPing)
	if err != nil {
		return err
	}
	if err := saveServer(server); err != nil {
		return err
	}
	fmt.Printf("Server got ping: %q\n", ping.Data)
	fmt.Printf("Key ID: %d\n", ping.KeyID)
	fmt.Printf("Consumed key sequence: %d\n", ping.Seq)
	fmt.Printf("Ratchet state: %s\n", ping.State)

	// The C2 needs to know what the beacon's ID is so it can encrypt to it.
	sTask0, err := server.EncryptAndUpdate(sRegResp.KeyID, []byte("task contents"))
	if err != nil {
		return err
	}
	if err := saveServer(server); err != nil {
		return err
	}
	fmt.Printf("Key ID: %d\n", sTask0.KeyID)
	fmt.Printf("Consumed key sequence: %d\n", sTask0.Seq)
	fmt.Printf("Ratchet state: %s\n", sTask0.State)
	if err := writeTransport(sTask0.Data); err != nil {
		return err
	}
	bTask0, err := readTransport()
	if err != nil {
		return err
	}

	task0, err := beacon.DecryptServerMessage(bTask0)
	if err != nil {
		return err
	}
	fmt.Printf("Beacon got first task: %q\n", task0)

	// Process task and send the response.
	bTask1, err := beacon.EncryptToServer([]byte("task response"))
	if err != nil {
		return err
	}
	if err := writeTransport(bTask1); err != nil {
		return err
	}
	sTask1, err := readTransport()
	if err != nil {
		return err
	}

	task1, err := server.DecryptAndUpdate(sTask1)
	if err != nil {
		return err
	}
	if err := saveServer(server); err != nil {
		return err
	}
	fmt.Printf("Server got response to first task: %q\n", task1.Data)
	fmt.Printf("Key ID: %d\n", task1.KeyID)
	fmt.Printf("Consumed key sequence: %d\n", task1.Seq)
	fmt.Printf("Ratchet state: %s\n", task1.State)

	return nil
}

func saveServer(server *beaconcrypt.Server) error {
	// Checkpoints are plaintext secret material. Save immediately after every
	// state-changing call and before using its output. A production store must
	// also reject stale rollback and coordinate concurrent owners.
	state, err := server.ExportState()
	if err != nil {
		return err
	}
	return os.WriteFile(statePath, state, 0o600)
}

func writeTransport(data []byte) error {
	return os.WriteFile(transportPath, data, 0o600)
}

func readTransport() ([]byte, error) {
	return os.ReadFile(transportPath)
}
