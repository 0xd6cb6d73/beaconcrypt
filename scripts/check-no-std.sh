#!/usr/bin/env bash
# SPDX-License-Identifier: 0BSD
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd -- "$script_dir/.." && pwd)"
cd -- "$repo_dir"

target="${BEACONCRYPT_NO_STD_TARGET:-thumbv7em-none-eabihf}"
consumer_dir="$(mktemp -d "${TMPDIR:-/tmp}/beaconcrypt-no-std-consumer.XXXXXX")"
trap 'rm -rf -- "$consumer_dir"' EXIT

# The consumer is outside the workspace and selects the library exactly as a
# downstream application would. Artifact types come from dependency manifests.
python3 - "$repo_dir" "$consumer_dir" <<'PY'
import json
from pathlib import Path
import shutil
import sys

repo = Path(sys.argv[1])
consumer = Path(sys.argv[2])
(consumer / "src").mkdir()
(consumer / "Cargo.toml").write_text(
    '[package]\nname = "beaconcrypt-no-std-consumer"\nversion = "0.0.0"\n'
    'edition = "2024"\npublish = false\n\n'
    '[dependencies]\nbeaconcrypt = { path = '
    + json.dumps(str(repo / "beaconcrypt"))
    + ', default-features = false }\n\n'
    '[features]\nbeacon = ["beaconcrypt/beacon"]\n'
    'server = ["beaconcrypt/server"]\n\n[workspace]\n'
)
(consumer / "src/lib.rs").write_text('''#![no_std]

pub const MAX_MESSAGE_SIZE: usize = beaconcrypt::MAX_MESSAGE_SIZE;

#[cfg(feature = "beacon")]
pub fn make_beacon<R: beaconcrypt::crypto::TryCryptoRng + ?Sized>(
    rng: &mut R,
    server_id: &[u8],
    server_mldsa: &[u8],
) -> Result<beaconcrypt::Beacon, beaconcrypt::KeyGenError> {
    beaconcrypt::Beacon::try_new_with_rng(7, server_id, server_mldsa, rng)
}

#[cfg(feature = "server")]
pub fn make_server<R: beaconcrypt::crypto::TryCryptoRng + ?Sized>(
    rng: &mut R,
) -> Result<beaconcrypt::Server, beaconcrypt::KeyGenError> {
    beaconcrypt::Server::try_new_with_rng(7, None, None, rng)
}

#[cfg(feature = "server")]
pub fn make_rows<S: beaconcrypt::RowStore, R: beaconcrypt::crypto::TryCryptoRng + ?Sized>(
    store: S, lineage: beaconcrypt::SnapshotLineage, request: &[u8], rng: &mut R,
) -> Result<beaconcrypt::RowServer<S>, beaconcrypt::RowError> {
    let mut server = beaconcrypt::RowServer::create_with_rng(7, None, None, store, lineage, rng)?;
    server.register_beacon_with_rng(request, None, rng)?;
    Ok(server)
}

#[cfg(feature = "server")]
pub fn make_cached_rows<S: beaconcrypt::RowStore, R: beaconcrypt::crypto::TryCryptoRng + ?Sized>(
    store: S, lineage: beaconcrypt::SnapshotLineage, request: &[u8], rng: &mut R,
) -> Result<beaconcrypt::CachedRowServer<S>, beaconcrypt::RowError> {
    let mut server = beaconcrypt::CachedRowServer::create_with_rng(7, None, None, store, lineage, 4, rng)?;
    server.register_beacon_with_rng(request, None, rng)?;
    Ok(server)
}

#[cfg(feature = "server")]
pub fn accept_row_registration<R: beaconcrypt::crypto::TryCryptoRng + ?Sized>(
    session: &mut beaconcrypt::RowSession<'_>, request: &[u8], rng: &mut R,
) -> Result<bool, beaconcrypt::RowError> {
    session.accept_registration_with_rng(request, rng)
}

#[cfg(feature = "server")]
pub fn open_rows<S: beaconcrypt::RowStore>(
    store: S, lineage: beaconcrypt::SnapshotLineage,
) -> Result<beaconcrypt::CachedRowServer<S>, beaconcrypt::RowError> {
    let server = beaconcrypt::RowServer::open(store, lineage)?;
    Ok(beaconcrypt::CachedRowServer::from_server(server, 4))
}

#[cfg(all(feature = "beacon", feature = "server"))]
pub fn establish<R: beaconcrypt::crypto::TryCryptoRng + ?Sized>(
    rng: &mut R,
) -> Option<(beaconcrypt::Beacon, beaconcrypt::Server)> {
    use beaconcrypt::{ProviderBeacon, ProviderServer};
    let mut server = make_server(rng).ok()?;
    let mut beacon = make_beacon(rng, server.identity_pk().as_bytes(), &server.mldsa_public_key()).ok()?;
    let bundle = beacon.get_registration_bundle_with_rng(rng)?;
    let pending = server.get_shared_secret_with_rng(&bundle, rng)?;
    let response = server.build_registration_response(pending, None)?;
    beacon.finish_registration(&response.serialized)?;
    Some((beacon, server))
}
''')
# Preserve reviewed dependency versions while Cargo adds the consumer root.
shutil.copyfile(repo / "Cargo.lock", consumer / "Cargo.lock")
PY

export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$repo_dir/target/no-std-consumer}"
cargo metadata --manifest-path "$consumer_dir/Cargo.toml" --all-features --format-version 1 > /dev/null
for features in "" beacon server beacon,server; do
  printf 'Building independent no_std consumer for %s (%s)\n' "$target" "${features:-no roles}"
  args=(build --manifest-path "$consumer_dir/Cargo.toml" --lib --locked --no-default-features --target "$target")
  if [[ -n "$features" ]]; then
    args+=(--features "$features")
  fi
  cargo "${args[@]}"
done
