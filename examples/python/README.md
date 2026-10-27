Small demo of how to use the beaconcrypt library from python.

The server uses independent Ed25519 and ML-DSA-65 identity seeds. The beacon constructor requires both server public keys: `BeaconCryptBeacon(kid, server.id_pk(), server.mldsa_public_key())`.

Run with:

```bash
uv run main.py
```
