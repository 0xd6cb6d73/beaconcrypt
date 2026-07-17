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

	bPing, err := beacon.EncryptToServerSigned([]byte("ping"))
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
	ping, err := server.DecryptBeaconMessageSigned(sPing)
	if err != nil {
		return err
	}
	fmt.Printf("Server got ping: %q\n", ping)

	// The C2 needs to know what the beacon's ID is so it can encrypt to it.
	sTask0, err := server.EncryptToBeaconSigned(sRegResp.KeyID, []byte("task contents"))
	if err != nil {
		return err
	}
	if err := writeTransport(sTask0); err != nil {
		return err
	}
	bTask0, err := readTransport()
	if err != nil {
		return err
	}

	task0, err := beacon.DecryptServerMessageSigned(bTask0)
	if err != nil {
		return err
	}
	fmt.Printf("Beacon got first task: %q\n", task0)

	// Process task and send the response.
	bTask1, err := beacon.EncryptToServerSigned([]byte("task response"))
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

	task1, err := server.DecryptBeaconMessageSigned(sTask1)
	if err != nil {
		return err
	}
	fmt.Printf("Server got response to first task: %q\n", task1)

	return nil
}

func writeTransport(data []byte) error {
	return os.WriteFile(transportPath, data, 0o600)
}

func readTransport() ([]byte, error) {
	return os.ReadFile(transportPath)
}
