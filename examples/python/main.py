import base64

from beaconcrypt import BeaconCryptBeacon, BeaconCryptServer
from nacl.utils import random

SERVER_KID = 0
REGISTRATION_MESSAGE = b"registration ok"


def main():
    server_seed = random(32)
    server = BeaconCryptServer(SERVER_KID, server_seed)
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
    # ship the response back over your transport
    with open("transport", "wb") as f:
        f.write(s_reg_resp.serialized())
    with open("transport", "rb") as f:
        b_reg_1 = f.read()
    # do whatever you like with the initial message
    first_message = beacon.process_initial_message(b_reg_1)
    print(f"Beacon got intial message: {first_message}")
    b_ping = beacon.encrypt_to_server_signed(b"ping")
    with open("transport", "wb") as f:
        f.write(b_ping)
    with open("transport", "rb") as f:
        s_ping = f.read()
    # got the ping, maybe there's a task to send now
    ping = server.decrypt_and_update(s_ping)
    print(f"Server got ping: {ping.data()}")
    print(f"Key ID: {ping.key_id()}")
    print(f"Ratchet state: {base64.b64encode(ping.key())}")
    # The C2 needs to know what the beacon's ID is so it can encrypt to it
    s_task_0 = server.encrypt_and_update(b"task contents", s_reg_resp.key_id())
    print(f"Key ID: {s_task_0.key_id()}")
    print(f"Ratchet state: {base64.b64encode(s_task_0.key())}")
    with open("transport", "wb") as f:
        f.write(s_task_0.data())
    with open("transport", "rb") as f:
        b_task_0 = f.read()
    task_0 = beacon.decrypt_server_message_signed(b_task_0)
    print(f"Beacon got first task: {task_0}")
    # process task and send the response
    b_task_1 = beacon.encrypt_to_server_signed(b"task response")
    with open("transport", "wb") as f:
        f.write(b_task_1)
    with open("transport", "rb") as f:
        s_task_1 = f.read()
    task_1 = server.decrypt_and_update(s_task_1)
    print(f"Server got response to first task: {task_1.data()}")
    print(f"Key ID: {task_1.key_id()}")
    print(f"Ratchet state: {base64.b64encode(task_1.key())}")


if __name__ == "__main__":
    main()
