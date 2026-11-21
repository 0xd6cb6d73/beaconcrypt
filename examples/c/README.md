Small demo of how to use the beaconcrypt library from C with CMake.

The example generates independent 32-byte Ed25519 and ML-DSA-65 seeds and provisions both server public keys to the beacon. `beaconcrypt_beacon_new` requires both key buffers, including the 1,952-byte ML-DSA public key returned by `beaconcrypt_server_mldsa_public_key`.

Run with:

```bash
cmake -S . -B build
cmake --build build
./build/beaconcrypt_c_example
```

On Windows, the executable may be under a configuration directory:

```powershell
.\build\Debug\beaconcrypt_c_example.exe
```

If you build with the Visual Studio/MSVC CMake toolchain, use the Rust MSVC
toolchain too. If you build with MinGW, use the Rust GNU toolchain.
