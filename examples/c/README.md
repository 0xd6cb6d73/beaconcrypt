Small demo of how to use the beaconcrypt library from C with CMake. Run with:

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
