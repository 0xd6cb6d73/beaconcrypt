import json
import os
from secrets import token_bytes

from beaconcrypt import BeaconCryptBeacon, BeaconCryptServer

SERVER_KID = 0
REGISTRATION_MESSAGE = b"registration ok"
STATE_PATH = "server-state.bin"


def save_server(server):
    # Checkpoints are plaintext secret material. Write immediately after every
    # state-changing call and before using its output. A production store must
    # also reject stale rollback and coordinate concurrent owners.
    with open(STATE_PATH, "wb") as state_file:
        state_file.write(server.export_state())


def main():
    server_seed = token_bytes(32)
    server = BeaconCryptServer(SERVER_KID, server_seed)
    save_server(server)
    # it is assumed that the server's public key is compiled into beacons
    beacon = BeaconCryptBeacon(SERVER_KID, server.id_pk())

    # the beacon is run and registers
    b_reg_1 = beacon.generate_registration()
    # ship the registration bytes over whichever transport you like
    with open("transport", "wb") as f:
        f.write(b_reg_1)
    with open("transport", "rb") as f:
        s_reg_1 = f.read()
    # now the server has the registration message and can send some initial message if needed
    s_reg_resp = server.register_beacon(s_reg_1, REGISTRATION_MESSAGE)
    save_server(server)
    # ship the response back over your transport
    with open("transport", "wb") as f:
        f.write(s_reg_resp.serialized())
    with open("transport", "rb") as f:
        b_reg_1 = f.read()
    # do whatever you like with the initial message
    first_message = beacon.process_initial_message(b_reg_1)
    print(f"Beacon got initial message: {first_message}")

    # Simulate a restart. from_state trusts these bytes as the authoritative
    # current checkpoint; the bytes do not authenticate themselves or prevent
    # rollback to an older exported file.
    del server
    with open(STATE_PATH, "rb") as state_file:
        server = BeaconCryptServer.from_state(state_file.read())
    save_server(server)  # Persist the generation advanced by activation.
    print(f"Restored server state from {STATE_PATH}")
    b_ping = beacon.encrypt_message_to_server(b"ping")
    with open("transport", "wb") as f:
        f.write(b_ping)
    with open("transport", "rb") as f:
        s_ping = f.read()
    # got the ping, maybe there's a task to send now
    ping = server.decrypt_and_update(s_ping)
    save_server(server)
    print(f"Server got ping: {ping.data()}")
    print(f"Key ID: {ping.key_id()}")
    print(f"Consumed key sequence: {ping.seq()}")
    print(f"Ratchet state: {json.loads(ping.state())}")
    # The C2 needs to know what the beacon's ID is so it can encrypt to it
    s_task_0 = server.encrypt_and_update(b"task contents", s_reg_resp.key_id())
    save_server(server)
    print(f"Key ID: {s_task_0.key_id()}")
    print(f"Consumed key sequence: {s_task_0.seq()}")
    print(f"Ratchet state: {json.loads(s_task_0.state())}")
    with open("transport", "wb") as f:
        f.write(s_task_0.data())
    with open("transport", "rb") as f:
        b_task_0 = f.read()
    task_0 = beacon.decrypt_server_message(b_task_0)
    print(f"Beacon got first task: {task_0}")
    # process task and send the response
    b_task_1 = beacon.encrypt_message_to_server(b"task response")
    with open("transport", "wb") as f:
        f.write(b_task_1)
    with open("transport", "rb") as f:
        s_task_1 = f.read()
    task_1 = server.decrypt_and_update(s_task_1)
    save_server(server)
    print(f"Server got response to first task: {task_1.data()}")
    print(f"Key ID: {task_1.key_id()}")
    print(f"Consumed key sequence: {task_1.seq()}")
    print(f"Ratchet state: {json.loads(task_1.state())}")
    os.remove("transport")
    os.remove(STATE_PATH)


if __name__ == "__main__":
    main()
