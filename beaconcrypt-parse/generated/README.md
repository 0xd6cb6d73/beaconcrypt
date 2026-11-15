<!-- SPDX-License-Identifier: 0BSD -->

# Generated Rust provenance

`src/generated/{cbordetver.rs,cbordetveraux.rs,transport.rs}` are unmodified EverCDDL/KaRaMeL output from [EverParse v2026.08.21](https://github.com/project-everest/everparse/tree/v2026.08.21), commit `1c9559ad1c59e1d2c511c7c4ac7cb1b162f59c3f`. They use [Apache-2.0](LICENSE); crate glue is handwritten 0BSD code.

Use Python 3.12+ on Linux x86_64 with the [release archive](https://github.com/project-everest/everparse/releases/download/v2026.08.21/everparse_v2026.08.21_Linux_x86_64.tar.gz), SHA-256 `b96f5de71df42f5ea861bd4115a892371f10dac9b1249e08a6a92bca180b46a5`. From the repository root:

```sh
python3 beaconcrypt-parse/scripts/regenerate.py /path/to/everparse_v2026.08.21_Linux_x86_64.tar.gz --check
python3 beaconcrypt-parse/scripts/regenerate.py /path/to/everparse_v2026.08.21_Linux_x86_64.tar.gz --write
```

The script verifies the archive checksum and invokes `cddl.exe --rust --mname Transport --odir <temporary-output> <absolute-path-to-beaconcrypt-parse/schema/transport.cddl>` without `--admit`. `--check` compares all three files byte for byte; `--write` replaces only those files, whose diffs must be reviewed.

| File under `src/generated/` | Bytes | SHA-256 |
| --- | ---: | --- |
| `cbordetver.rs` | 20,416 | `e60e27d58b3fe7eeaca202e9751b596c88884b4a76d5bf57a345a21861066d6c` |
| `cbordetveraux.rs` | 194,647 | `36420e78b9feed0a4c4a1b6a57b28aeba16ae38be9c61f5ff8165fa088ac3589` |
| `transport.rs` | 200,745 | `c271a30fe4aa35fb90782c7cec8755c50148fdab139fa7e1eadafd5e4b373b66` |

The registration version `3` schema removes the Beacon ML-DSA public key and signature from requests while retaining the fixed 3,309-byte Server signature in responses. The request is now a six-element CBOR array containing version, kind, and the four remaining key buffers; its complete encoding is 1,490 bytes. Regeneration changed only `transport.rs`; both imported generic CBOR runtime files retain the hashes above. Data-frame schema and encoding are unchanged. Review the generated diff together with the schema and the independent codec fixtures.

Generation verifies the schema-specific F* module against shipped prechecked dependencies. This does not prove extracted Rust, handwritten wrappers, the compiler, or end-to-end protocol behavior.
