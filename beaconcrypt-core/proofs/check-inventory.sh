#!/usr/bin/env bash
# SPDX-License-Identifier: 0BSD

set -euo pipefail

core_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
repo_dir="$(cd -- "$core_dir/.." && pwd)"
adapter_dir="$repo_dir/beaconcrypt"
cd "$core_dir"

manifest="proofs/reviewed-inventory.txt"
generated_proverif="proofs/pro-verif/extraction/lib.pvl"
tmp_dir="$(mktemp -d)"
trap 'rm -rf -- "$tmp_dir"' EXIT

fail() {
	printf 'formal-verification inventory check failed: %s\n' "$*" >&2
	exit 1
}

[[ -f "$manifest" ]] || fail "missing $manifest"

declare -A seen_paths=()
declare -A category_counts=()

while IFS=$'\t' read -r category expected path extra ||
	[[ -n "${category:-}${expected:-}${path:-}${extra:-}" ]]; do
	[[ -z "${category:-}" || "$category" == \#* ]] && continue
	[[ -z "${extra:-}" ]] || fail "malformed manifest entry for $path"
	[[ "$category" =~ ^(adapter-rust|adapter-schema|core-rust|control|generated-lean|generated-proverif|handwritten-lean|handwritten-proverif|handwritten-ssprove|historical-generated-fstar|historical-handwritten-fstar|inventory|lean-control|validation)$ ]] ||
		fail "unknown manifest category: $category"
	[[ "$expected" =~ ^[0-9a-f]{64}$ ]] || fail "invalid SHA-256 for $path"
	[[ -n "$path" && -f "$path" ]] || fail "missing reviewed file: $path"
	[[ ! -L "$path" ]] || fail "reviewed path must not be a symlink: $path"
	[[ -z "${seen_paths[$path]:-}" ]] || fail "duplicate manifest path: $path"
	seen_paths[$path]=1
	category_counts[$category]=$((${category_counts[$category]:-0} + 1))
	actual="$(sha256sum -- "$path")"
	actual="${actual%% *}"
	[[ "$actual" == "$expected" ]] ||
		fail "$category drift in $path (expected $expected, got $actual)"
done < "$manifest"

declare -A expected_category_counts=(
	[adapter-rust]=13
	[adapter-schema]=3
	[core-rust]=9
	[control]=12
	[generated-lean]=5
	[generated-proverif]=1
	[handwritten-lean]=81
	[handwritten-proverif]=64
	[handwritten-ssprove]=18
	[historical-generated-fstar]=5
	[historical-handwritten-fstar]=8
	[inventory]=2
	[lean-control]=12
	[validation]=3
)
for category in "${!expected_category_counts[@]}"; do
	expected="${expected_category_counts[$category]}"
	actual="${category_counts[$category]:-0}"
	[[ "$actual" == "$expected" ]] ||
		fail "$category manifest count changed (expected $expected, got $actual)"
done

compare_set() {
	local category="$1"
	local actual_file="$2"
	local expected_file="$tmp_dir/expected-$category"
	awk -F '\t' -v category="$category" '$1 == category { print $3 }' "$manifest" |
		LC_ALL=C sort -u > "$expected_file"
	LC_ALL=C sort -u -o "$actual_file" "$actual_file"
	if ! cmp -s "$expected_file" "$actual_file"; then
		printf 'reviewed %s file set changed:\n' "$category" >&2
		diff -u "$expected_file" "$actual_file" >&2 || true
		fail "unreviewed $category file-set drift"
	fi
}

symlink_path="$(find "$adapter_dir/src" "$core_dir/src" -type l -print -quit)"
[[ -z "$symlink_path" ]] || fail "symlink in monitored tree: $symlink_path"
tracked_proof_symlink="$(git -C "$repo_dir" ls-files -s -- beaconcrypt-core/proofs |
	awk '$1 == "120000" { print $4; exit }')"
[[ -z "$tracked_proof_symlink" ]] ||
	fail "symlink in monitored proof tree: $tracked_proof_symlink"

printf '%s\n' \
	../.cargo/config.toml \
	../.github/workflows/formal-verification.yml \
	../.gitignore \
	../Cargo.lock \
	../Cargo.toml \
	../beaconcrypt/Cargo.toml \
	../flake.lock \
	../flake.nix \
	Cargo.toml \
	Makefile \
	README.md \
	proofs/fstar/Makefile > "$tmp_dir/control"
compare_set control "$tmp_dir/control"

printf '%s\n' proofs/check-inventory.sh proofs/trusted-boundary.md \
	> "$tmp_dir/inventory"
compare_set inventory "$tmp_dir/inventory"

printf '%s\n' ../beaconcrypt/tests/protocol.rs ../beaconcrypt/tests/server.rs \
	tests/proverif_transcript_fidelity.rs \
	> "$tmp_dir/validation"
compare_set validation "$tmp_dir/validation"

awk -F '\t' '$3 ~ /^proofs\// { print "beaconcrypt-core/" $3 }' "$manifest" \
	> "$tmp_dir/expected-all-proof-files"
printf '%s\n' "$manifest" >> "$tmp_dir/expected-all-proof-files"
sed -i 's|^proofs/reviewed-inventory.txt$|beaconcrypt-core/proofs/reviewed-inventory.txt|' \
	"$tmp_dir/expected-all-proof-files"
git -C "$repo_dir" ls-files -- beaconcrypt-core/proofs \
	> "$tmp_dir/all-proof-files"
LC_ALL=C sort -u -o "$tmp_dir/expected-all-proof-files" \
	"$tmp_dir/expected-all-proof-files"
LC_ALL=C sort -u -o "$tmp_dir/all-proof-files" "$tmp_dir/all-proof-files"
if comm -23 "$tmp_dir/all-proof-files" "$tmp_dir/expected-all-proof-files" \
	> "$tmp_dir/unreviewed-tracked-proof-files" &&
	[[ -s "$tmp_dir/unreviewed-tracked-proof-files" ]]; then
	printf 'reviewed proof/control file set changed:\n' >&2
	cat "$tmp_dir/unreviewed-tracked-proof-files" >&2
	fail "unreviewed tracked file under proofs"
fi

find "$adapter_dir/src" -type f -name '*.rs' \
	-printf '../beaconcrypt/src/%P\n' > "$tmp_dir/adapter-rust"
printf '%s\n' ../beaconcrypt/build.rs >> "$tmp_dir/adapter-rust"
compare_set adapter-rust "$tmp_dir/adapter-rust"

find "$adapter_dir/src/schema" -type f -name '*.capnp' \
	-printf '../beaconcrypt/src/schema/%f\n' > "$tmp_dir/adapter-schema"
compare_set adapter-schema "$tmp_dir/adapter-schema"

find src -type f -name '*.rs' -printf '%p\n' > "$tmp_dir/core-rust"
compare_set core-rust "$tmp_dir/core-rust"

find proofs/fstar -type f \( -name '*.fst' -o -name '*.fsti' \) \
	! -path 'proofs/fstar/extraction/*' ! -path '*/.cache/*' \
	-printf '%p\n' > "$tmp_dir/historical-handwritten-fstar"
compare_set historical-handwritten-fstar "$tmp_dir/historical-handwritten-fstar"

find proofs/pro-verif -type f \
	\( -name '*.pv' -o -name '*.pvl' -o -name '*.awk' \) \
	! -path 'proofs/pro-verif/extraction/*' \
	-printf '%p\n' > "$tmp_dir/handwritten-proverif"
compare_set handwritten-proverif "$tmp_dir/handwritten-proverif"

find proofs/ssprove -type f -printf '%p\n' \
	> "$tmp_dir/handwritten-ssprove"
compare_set handwritten-ssprove "$tmp_dir/handwritten-ssprove"

find proofs/fstar/extraction -type f \
	\( -name '*.fst' -o -name '*.fsti' \) \
	-printf '%p\n' > "$tmp_dir/historical-generated-fstar"
compare_set historical-generated-fstar "$tmp_dir/historical-generated-fstar"

find proofs/pro-verif/extraction -type f \
	\( -name '*.pv' -o -name '*.pvl' \) -printf '%p\n' > "$tmp_dir/generated-proverif"
compare_set generated-proverif "$tmp_dir/generated-proverif"

printf '%s\n' \
	proofs/lean/BeaconcryptCore/Extraction.lean \
	proofs/lean/BeaconcryptCore/Extraction/Funs.lean \
	proofs/lean/BeaconcryptCore/Extraction/FunsExternal.lean \
	proofs/lean/BeaconcryptCore/Extraction/FunsExternal_Template.lean \
	proofs/lean/BeaconcryptCore/Extraction/Types.lean \
	> "$tmp_dir/generated-lean"
compare_set generated-lean "$tmp_dir/generated-lean"

printf '%s\n' \
	proofs/lean/BeaconcryptCore.lean \
	proofs/lean/BeaconcryptCore/Assumptions/FunsExternal.lean \
	proofs/lean/BeaconcryptCore/Verification/PqxdhCommitmentRefinement.lean \
	proofs/lean/BeaconcryptCore/Verification/ProofObligations.lean \
	> "$tmp_dir/handwritten-lean"
for lean_proof_dir in Model Refinement Computational PanicFreedom; do
	find "proofs/lean/BeaconcryptCore/$lean_proof_dir" -type f -name '*.lean' \
		-printf '%p\n' >> "$tmp_dir/handwritten-lean"
done
compare_set handwritten-lean "$tmp_dir/handwritten-lean"

printf '%s\n' \
	../scripts/check_lean_panic_freedom.py \
	../scripts/test_check_lean_panic_freedom.py \
	proofs/lean/panic-freedom.json \
	proofs/lean/.gitignore \
	proofs/lean/ARISTOTLE_SUMMARY.md \
	proofs/lean/PQXDH_IDEAL_MODEL.md \
	proofs/lean/PQXDH_REFINEMENT.md \
	proofs/lean/README.md \
	proofs/lean/lake-manifest.json \
	proofs/lean/lakefile.toml \
	proofs/lean/lean-toolchain \
	proofs/lean/pqxdh_spec.md > "$tmp_dir/lean-control"
compare_set lean-control "$tmp_dir/lean-control"

require_line_count() {
	local expected="$1"
	local pattern="$2"
	local path="$3"
	local label="$4"
	local actual
	rg_allow_no_match -c -- "$pattern" "$path"
	actual="$RG_OUTPUT"
	actual="${actual:-0}"
	[[ "$actual" == "$expected" ]] ||
		fail "$label count changed in $path (expected $expected, got $actual)"
}

require_occurrence_count() {
	local expected="$1"
	local pattern="$2"
	shift 2
	local label="$1"
	shift
	local actual
	rg_allow_no_match --count-matches --multiline --pcre2 "$pattern" "$@"
	if [[ -n "$RG_OUTPUT" ]]; then
		actual="$(printf '%s\n' "$RG_OUTPUT" | awk -F ':' '{ total += $NF } END { print total + 0 }')"
	else
		actual=0
	fi
	actual="${actual//[[:space:]]/}"
	[[ "$actual" == "$expected" ]] ||
		fail "$label count changed (expected $expected, got $actual)"
}

rg_allow_no_match() {
	local status
	set +e
	RG_OUTPUT="$(rg --no-ignore "$@" 2>&1)"
	status=$?
	set -e
	case "$status" in
		0 | 1) ;;
		*) fail "ripgrep scan failed: $RG_OUTPUT" ;;
	esac
}

reject_matches() {
	local label="$1"
	shift
	rg_allow_no_match -n --multiline --pcre2 "$@"
	if [[ -n "$RG_OUTPUT" ]]; then
		printf '%s\n' "$RG_OUTPUT" >&2
		fail "$label"
	fi
}

reject_matches "new hax opaque annotation requires inventory review" \
	'hax_lib\s*::\s*(?:opaque|opaque_type)\b' src
require_occurrence_count 1 \
	'hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"noeq"\s*\)' \
	"reviewed F* noeq insertion" src
require_occurrence_count 3 \
	'hax_lib\s*::\s*fstar\s*::\s*before\s*\(' \
	"complete F* before-annotation allowlist" src
require_occurrence_count 1 \
	'#\[cfg_attr\(feature\s*=\s*"proverif",\s*hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"noeq"\s*\)\)\]\s*pub\s+struct\s+InitialRatchetChains\b' \
	"reviewed noeq target InitialRatchetChains" src/pqxdh.rs
require_occurrence_count 1 \
	'hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"friend Beaconcrypt_core\.Ratchet\.Refined"\s*\)' \
	"reviewed Ratchet-to-Refined friend edge" src/ratchet.rs
require_occurrence_count 1 \
	'hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"friend Beaconcrypt_core\.Ratchet\.Control"\s*\)' \
	"reviewed Refined-to-Control friend edge" src/ratchet/refined.rs

# The checked-in F* files intentionally archive the predecessor executor/callback implementation.
# They are reviewed historical evidence from a previously checked snapshot, but canonical regeneration does not currently verify them or establish correspondence with the current Rust effect machine.
# These markers make that migration gap explicit and force an inventory review when the six-module current extraction replaces it.
[[ ! -e proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Concrete.fst ]] ||
	fail "current-effect F* extraction appeared; reclassify the historical F* inventory"
require_line_count 1 '^type t_ConcreteRatchetChain = ' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.fst \
	"historical executor-bearing F* snapshot marker"
require_line_count 1 '^let concrete_ratchet_step ' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.fst \
	"historical callback-era F* snapshot marker"

replacement_pattern='hax_lib\s*::\s*proverif\s*::\s*replace\s*\('
require_occurrence_count 3 "$replacement_pattern" \
	"ProVerif Rust replacement" src
rg_allow_no_match -l --multiline --pcre2 "$replacement_pattern" src
replacement_files=()
if [[ -n "$RG_OUTPUT" ]]; then
	mapfile -t replacement_files <<< "$RG_OUTPUT"
fi
[[ "${#replacement_files[@]}" == 1 && "${replacement_files[0]}" == src/pqxdh.rs ]] ||
	fail "ProVerif Rust replacements moved outside the reviewed src/pqxdh.rs boundary"
for replacement in registration_id build_root_key_input build_associated_data; do
	rg --no-ignore -q "^pub (const )?fn ${replacement}\\b" src/pqxdh.rs ||
		fail "missing reviewed ProVerif replacement target: $replacement"
	require_occurrence_count 1 "\\$\\{${replacement}\\}" \
		"ProVerif replacement placeholder for $replacement" src/pqxdh.rs
	rg --no-ignore -q "beaconcrypt_core__pqxdh__${replacement}\\b" "$generated_proverif" ||
		fail "missing generated ProVerif replacement: $replacement"
done

require_line_count 6 '^type beaconcrypt_core' "$generated_proverif" \
	"generated ProVerif selected type"
require_line_count 12 '^fun beaconcrypt_core.*_(to|from)_bitstring' "$generated_proverif" \
	"generated ProVerif type converter"
require_line_count 6 '^const beaconcrypt_core.*_default_value' "$generated_proverif" \
	"generated ProVerif record default"
require_line_count 9 '^letfun .*_err\(\)' "$generated_proverif" \
	"generated ProVerif error helper"
require_line_count 22 '^fun ' "$generated_proverif" \
	"generated ProVerif constructor/function"
require_line_count 20 '^reduc ' "$generated_proverif" \
	"generated ProVerif reduction"
require_occurrence_count 11 'construct_fail\(\)' \
	"generated ProVerif construct_fail" "$generated_proverif"
require_line_count 1 \
	'^  beaconcrypt_core__pqxdh__build_associated_data\(server_identity, beacon_identity\) = beaconcrypt_associated_data\(tag_ed25519\(server_identity\), tag_ed25519\(beacon_identity\), pqxdh_domain\(\), symmetric_ratchet_domain\(\)\)\.$' \
	"$generated_proverif" "generated exact associated-data replacement"

mapfile -t handwritten_proverif < <(
	awk -F '\t' '$1 == "handwritten-proverif" && $3 ~ /\.(pv|pvl)$/ { print $3 }' "$manifest"
)
reject_matches "handwritten ProVerif uses a forbidden generated helper" \
	'(construct_fail|_from_bitstring|_default_value|_(?:default|err)\s*\(|nat_to_bitstring)' \
	"${handwritten_proverif[@]}"
require_occurrence_count 8 \
	'beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring' \
	"allowed generated ProVerif converter" "${handwritten_proverif[@]}"
require_occurrence_count 11 '_to_bitstring' \
	"all handwritten _to_bitstring tokens including three initial-ratchet manifest facts" \
	"${handwritten_proverif[@]}"

transcript_interface=proofs/pro-verif/production-transcript-interface.pvl
require_line_count 465 '^\(\* @beaconcrypt-fidelity-v1 ' "$transcript_interface" \
	"canonical production transcript fact"
require_line_count 18 '^\(\* @beaconcrypt-fidelity-v1 phase1\.' \
	"$transcript_interface" "Phase-1 InitKex transcript fact"
require_line_count 42 '^\(\* @beaconcrypt-fidelity-v1 cryptoframe\.' \
	"$transcript_interface" "CryptoFrame wire transcript fact"
require_line_count 56 '^\(\* @beaconcrypt-fidelity-v1 endpoint\.' \
	"$transcript_interface" "endpoint frame-context transcript fact"
require_line_count 38 '^\(\* @beaconcrypt-fidelity-v1 ratchet\.driver\.' \
	"$transcript_interface" "ratchet effect-driver transcript fact"
require_line_count 46 '^\(\* @beaconcrypt-fidelity-v1 ratchet\.receive_fixture\.' \
	"$transcript_interface" "finite receive-state fixture transcript fact"
require_line_count 60 '^\(\* @beaconcrypt-fidelity-v1 registration\.lifecycle\.' \
	"$transcript_interface" "registration lifecycle transcript fact"
require_line_count 71 '^\(\* @beaconcrypt-fidelity-v1 initial_ratchet\.' \
	"$transcript_interface" "initial-ratchet fidelity fact"
require_line_count 68 '^\(\* @beaconcrypt-fidelity-v1 later_registration\.' \
	"$transcript_interface" "later-sequence registration fidelity fact"
require_line_count 5 '^type ' "$transcript_interface" \
	"canonical ProVerif interface type"
require_line_count 19 '^fun ' "$transcript_interface" \
	"canonical ProVerif interface constructor/function"
require_line_count 2 '^letfun ' "$transcript_interface" \
	"canonical ProVerif interface helper"
require_line_count 2 '^type ' proofs/pro-verif/crypto.pvl \
	"handwritten primitive internal type"
require_line_count 16 '^fun ' proofs/pro-verif/crypto.pvl \
	"handwritten primitive constructor/function"
require_line_count 8 '^reduc ' proofs/pro-verif/crypto.pvl \
	"handwritten primitive reduction"
require_line_count 6 '^letfun ' proofs/pro-verif/crypto.pvl \
	"handwritten primitive helper"
require_line_count 1 '^\(\* @beaconcrypt-cryptoframe-v1 crypto_frame\.fields=ciphertext,retained_aead_tag,commitment,sequence,sender_id \*\)$' \
	proofs/pro-verif/crypto.pvl "CryptoFrame symbolic semantic order"
require_line_count 1 '^fun pqxdh_domain\(\): kdf_domain \[data\]\.$' \
	"$transcript_interface" "PQXDH HKDF domain"
require_line_count 1 '^fun symmetric_ratchet_domain\(\): kdf_domain \[data\]\.$' \
	"$transcript_interface" "symmetric-ratchet HKDF domain"
require_line_count 1 '^fun hkdf_sha512_no_salt\(bitstring, kdf_domain\): hkdf_stream\.$' \
	"$transcript_interface" "shared no-salt HKDF stream"
require_line_count 3 '^fun hkdf_(first_32|second_32|final_12)\(' \
	"$transcript_interface" "shared HKDF projection"
require_occurrence_count 2 \
	'pqxdh_root_input\(pqxdh_ff32_padding\(\), dh1, dh2, dh3, dh4, kem\)' \
	"explicit ordered ProVerif root transcript" src/pqxdh.rs "$generated_proverif"
require_line_count 1 '^fun sequence_le64\(sequence\): bitstring \[data\]\.$' \
	"$transcript_interface" "symbolic sequence LE64 encoding"
require_line_count 1 '^fun sender_id_le64\(key_id\): bitstring \[data\]\.$' \
	"$transcript_interface" "symbolic sender-ID LE64 encoding"
require_line_count 1 \
	'^letfun key_id_encoding\(identifier: key_id\) = sender_id_le64\(identifier\)\.$' \
	"$transcript_interface" "registration key-ID encoding compatibility"
require_line_count 4 \
	'^fun tag_(ed25519|x25519_prekey|x25519_one_time|mlkem768)\(bitstring\): bitstring \[data\]\.$' \
	"$transcript_interface" "symbolic production key encoding"
require_occurrence_count 1 \
	'fun beaconcrypt_associated_data\(\s*bitstring,\s*bitstring,\s*kdf_domain,\s*kdf_domain\s*\): bitstring \[data\]\.' \
	"exact associated-data constructor arity" "$transcript_interface"
require_occurrence_count 2 \
	'fun aead_(?:cipher|tag)\(\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring\s*\): bitstring\.' \
	"exact base AEAD input arity" "$transcript_interface"
require_occurrence_count 1 \
	'fun ctx_preimage\(\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring\s*\): bitstring \[data\]\.' \
	"exact six-field CTX preimage" "$transcript_interface"
require_line_count 1 '^fun blake2b512\(bitstring\): bitstring\.$' \
	"$transcript_interface" "symbolic BLAKE2b-512 constructor"
require_occurrence_count 1 \
	'letfun ctx_commitment\(\s*key: bitstring,\s*nonce: bitstring,\s*associated_data: bitstring,\s*retained_aead_tag: bitstring,\s*message_sequence: sequence,\s*sender_id: key_id\s*\)\s*=\s*blake2b512\(\s*ctx_preimage\(\s*key,\s*nonce,\s*associated_data,\s*retained_aead_tag,\s*sequence_le64\(message_sequence\),\s*sender_id_le64\(sender_id\)\s*\)\s*\)\.' \
	"exact ordered CTX commitment" "$transcript_interface"
reject_matches "invented AEAD or CTX label constructor" \
	'(?m)^(?:fun|letfun) (?:aead|ctx)_[A-Za-z0-9_]*(?:label|domain)\(' \
	"$transcript_interface" proofs/pro-verif/crypto.pvl
reject_matches "production transcript declaration duplicated outside canonical interface" \
	'(?m)^(?:type (?:key_id|sequence|kdf_domain|hkdf_stream|establishment_transcript_t)|fun (?:sequence_le64|sender_id_le64|tag_ed25519|tag_x25519_prekey|tag_x25519_one_time|tag_mlkem768|pqxdh_ff32_padding|pqxdh_root_input|pqxdh_domain|symmetric_ratchet_domain|hkdf_sha512_no_salt|hkdf_first_32|hkdf_second_32|hkdf_final_12|beaconcrypt_associated_data|aead_cipher|aead_tag|ctx_preimage|blake2b512)\b|letfun (?:key_id_encoding|ctx_commitment)\b)' \
	proofs/pro-verif/crypto.pvl
require_line_count 3 '^type ' proofs/pro-verif/environment.pvl \
	"handwritten protocol-state type"
require_line_count 14 '^fun ' proofs/pro-verif/environment.pvl \
	"handwritten protocol constructor/function"
require_line_count 1 \
	'^\(\* @beaconcrypt-phase1-v1 signed_init_kex\.fields=encoded_identity,signed_prekey,signed_one_time,signed_pq \*\)$' \
	proofs/pro-verif/environment.pvl \
	"Phase-1 symbolic signed InitKex semantic order"
require_line_count 1 '^type establishment_transcript_t\.$' \
	"$transcript_interface" "canonical establishment transcript type"
require_occurrence_count 1 \
	'fun establishment_transcript\(\s*bitstring,\s*bitstring,\s*beaconcrypt_core__pqxdh__t_InitKex,\s*beaconcrypt_core__pqxdh__t_RegistrationId,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*beaconcrypt_core__pqxdh__t_RootKeyInput,\s*bitstring,\s*bitstring,\s*key_id,\s*key_id,\s*bitstring,\s*bitstring\s*\): establishment_transcript_t \[data\]\.' \
	"exact 18-field establishment transcript declaration" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'type authenticated_init_bundle_t\.\s*fun authenticated_init_bundle\(\s*bitstring,\s*bitstring,\s*beaconcrypt_core__pqxdh__t_InitKex,\s*beaconcrypt_core__pqxdh__t_RegistrationId,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring\s*\): authenticated_init_bundle_t \[data\]\.' \
	"exact authenticated registration-bundle declaration" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 3 \
	'let\s+(?:beacon|server|malicious)_establishment\s*=\s*establishment_transcript\(\s*server_identity,\s*beacon_identity,\s*core_init,\s*registration_id,\s*beacon_prekey,\s*beacon_one_time,\s*beacon_pq,\s*server_ephemeral,\s*kem_ciphertext,\s*initial_frame,\s*response,\s*root_input,\s*root,\s*associated_data,\s*assigned_key_id,\s*SERVER_KEY_ID,\s*session,\s*registration_session\s*\)\s+in' \
	"exact establishment transcript emitter argument order" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 2 \
	'let\s+(?:initiated|accepted)_bundle\s*=\s*authenticated_init_bundle\(\s*server_identity,\s*beacon_identity,\s*core_init,\s*registration_id,\s*beacon_prekey,\s*beacon_one_time,\s*beacon_pq,\s*registration_session\s*\)\s+in' \
	"exact authenticated registration-bundle emitter argument order" \
	proofs/pro-verif/environment.pvl
require_line_count 1 '^event ServerCommitted\(establishment_transcript_t\)\.$' \
	proofs/pro-verif/environment.pvl "typed server commitment event"
require_line_count 1 '^event BeaconCommitted\(establishment_transcript_t\)\.$' \
	proofs/pro-verif/environment.pvl "typed beacon commitment event"
require_line_count 1 \
	'^event BeaconBundleInitiated\(authenticated_init_bundle_t\)\.$' \
	proofs/pro-verif/environment.pvl "typed beacon bundle-initiation event"
require_line_count 1 \
	'^event ServerBundleAccepted\(authenticated_init_bundle_t\)\.$' \
	proofs/pro-verif/environment.pvl "typed server bundle-acceptance event"
require_occurrence_count 1 \
	'event MaliciousRegistrationCommitted\(\s*establishment_transcript_t,\s*bitstring\s*\)\.' \
	"typed malicious-registration commitment event" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 'event\s+BeaconCommitted\(beacon_establishment\)' \
	"beacon establishment transcript emitter" proofs/pro-verif/environment.pvl
require_occurrence_count 1 'event\s+ServerCommitted\(server_establishment\)' \
	"server establishment transcript emitter" proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'event\s+MaliciousRegistrationCommitted\(\s*malicious_establishment,\s*MALICIOUS_TASK_SECRET\s*\)' \
	"malicious establishment transcript emitter" proofs/pro-verif/environment.pvl
require_occurrence_count 1 'event\s+BeaconBundleInitiated\(initiated_bundle\)' \
	"beacon authenticated-bundle emitter" proofs/pro-verif/environment.pvl
require_occurrence_count 1 'event\s+ServerBundleAccepted\(accepted_bundle\)' \
	"server authenticated-bundle emitter" proofs/pro-verif/environment.pvl
require_line_count 26 '^event ' proofs/pro-verif/environment.pvl \
	"handwritten event"
require_line_count 2 '^table ' proofs/pro-verif/environment.pvl \
	"handwritten table"
require_line_count 17 '^free ' proofs/pro-verif/environment.pvl \
	"handwritten free name/channel"
require_line_count 12 '^let [A-Z]' proofs/pro-verif/environment.pvl \
	"handwritten process"
require_line_count 12 '^query ' proofs/pro-verif/queries.pvl \
	"baseline query"
require_occurrence_count 1 \
	'query\s+transcript: establishment_transcript_t;\s*inj-event\(BeaconCommitted\(transcript\)\)\s*==>\s*inj-event\(ServerCommitted\(transcript\)\)\.' \
	"complete establishment transcript correspondence query" \
	proofs/pro-verif/queries.pvl
require_occurrence_count 1 \
	'query\s+bundle: authenticated_init_bundle_t;\s*inj-event\(ServerBundleAccepted\(bundle\)\)\s*==>\s*inj-event\(BeaconBundleInitiated\(bundle\)\)\.' \
	"exact authenticated registration-bundle correspondence query" \
	proofs/pro-verif/queries.pvl
require_line_count 8 '^query ' proofs/pro-verif/reachability-queries.pvl \
	"reachability query"
require_occurrence_count 1 \
	'query\s+bundle: authenticated_init_bundle_t;\s*event\(ServerBundleAccepted\(bundle\)\)\.' \
	"authenticated registration-bundle reachability query" \
	proofs/pro-verif/reachability-queries.pvl
require_occurrence_count 1 \
	'query\s+transcript: establishment_transcript_t;\s*event\(BeaconCommitted\(transcript\)\)\.' \
	"establishment transcript reachability query" \
	proofs/pro-verif/reachability-queries.pvl
require_occurrence_count 1 \
	'query\s+transcript: establishment_transcript_t,\s*plaintext: bitstring;\s*event\(MaliciousRegistrationCommitted\(transcript,\s*plaintext\)\)\.' \
	"malicious establishment transcript reachability query" \
	proofs/pro-verif/reachability-queries.pvl
require_line_count 5 '^query ' proofs/pro-verif/compromise-queries.pvl \
	"compromise query"
require_line_count 17 '^query ' proofs/pro-verif/failed-receive-queries.pvl \
	"state-neutral receive query"
require_line_count 12 '^query ' \
	proofs/pro-verif/failed-receive-reachability-queries.pvl \
	"state-neutral receive reachability query"
require_occurrence_count 1 \
	'query\s+transcript: establishment_transcript_t,\s*plaintext: bitstring;\s*event\(MaliciousRegistrationCommitted\(transcript,\s*plaintext\)\)\.' \
	"state-neutral malicious establishment reachability query" \
	proofs/pro-verif/failed-receive-reachability-queries.pvl
require_line_count 9 '^query ' \
	proofs/pro-verif/failed-receive-compromise-queries.pvl \
	"state-neutral receive compromise query"
require_line_count 2 '^query ' \
	proofs/pro-verif/failed-receive-compromise-reachability-queries.pvl \
	"state-neutral receive compromise reachability query"
require_line_count 7 '^query ' \
	proofs/pro-verif/aead-commitment-negative-control-queries.pvl \
	"AEAD commitment negative-control query"
require_line_count 2 '^event ' \
	proofs/pro-verif/aead-commitment-negative-control.pvl \
	"AEAD commitment negative-control event"
require_line_count 3 '^let [A-Z]' \
	proofs/pro-verif/aead-commitment-negative-control.pvl \
	"AEAD commitment negative-control process"
require_line_count 1 '^process$' proofs/pro-verif/baseline.pv \
	"baseline top-level process"
require_line_count 1 '^process$' proofs/pro-verif/compromise.pv \
	"compromise top-level process"
require_line_count 1 '^process$' proofs/pro-verif/failed-receive.pv \
	"failed-receive top-level process"
require_line_count 1 '^process$' \
	proofs/pro-verif/failed-receive-compromise.pv \
	"failed-receive compromise top-level process"
require_line_count 1 '^process$' proofs/pro-verif/aead-commitment.pv \
	"AEAD with-commitment top-level process"
require_line_count 1 '^process$' proofs/pro-verif/aead-no-commitment.pv \
	"AEAD no-commitment top-level process"
require_line_count 5 '^query ' proofs/pro-verif/passive-queries.pvl \
	"passive secrecy query"
require_line_count 6 '^query ' \
	proofs/pro-verif/passive-reachability-queries.pvl \
	"passive progress-control query"
require_occurrence_count 1 \
	'query\s+transcript: establishment_transcript_t;\s*event\(BeaconCommitted\(transcript\)\)\.' \
	"passive establishment transcript reachability query" \
	proofs/pro-verif/passive-reachability-queries.pvl
require_line_count 4 '^query ' proofs/pro-verif/active-quantum-queries.pvl \
	"active-quantum attack query"
require_occurrence_count 1 \
	'query\s+selected_pq_public_key: bitstring,\s*server_ephemeral: bitstring,\s*kem_ciphertext: bitstring,\s*initial_frame: bitstring,\s*response: bitstring,\s*root_input: beaconcrypt_core__pqxdh__t_RootKeyInput,\s*root: bitstring;\s*event\(QuantumInitialSecretRecovered\(\s*selected_pq_public_key,\s*server_ephemeral,\s*kem_ciphertext,\s*initial_frame,\s*response,\s*root_input,\s*root,\s*INITIAL_SECRET\s*\)\)\.' \
	"exact active-quantum transcript recovery query" \
	proofs/pro-verif/active-quantum-queries.pvl
require_occurrence_count 1 \
	'query\s+bundle: authenticated_init_bundle_t;\s*inj-event\(ServerBundleAccepted\(bundle\)\)\s*==>\s*inj-event\(BeaconBundleInitiated\(bundle\)\)\.' \
	"active-quantum authenticated-bundle failure query" \
	proofs/pro-verif/active-quantum-queries.pvl
require_line_count 2 '^reduc ' proofs/pro-verif/quantum-capabilities.pvl \
	"public symbolic quantum recovery rule"
require_line_count 2 '^query ' \
	proofs/pro-verif/quantum-capability-control-queries.pvl \
	"quantum capability-control query"
require_line_count 1 '^reduc ' \
	proofs/pro-verif/quantum-mlkem-recovery.pvl \
	"public symbolic ML-KEM recovery rule"
require_line_count 1 '^query ' \
	proofs/pro-verif/quantum-mlkem-recovery-queries.pvl \
	"ML-KEM capability-control query"
require_line_count 5 'choice\[' \
	proofs/pro-verif/passive-strong-secrecy.pv \
	"passive strong-secrecy challenge"
require_line_count 2 '^query ' \
	proofs/pro-verif/hkdf-prefix-conformance-queries.pvl \
	"shared-HKDF prefix conformance query"
require_line_count 2 '^event ' \
	proofs/pro-verif/hkdf-prefix-conformance.pvl \
	"shared-HKDF prefix conformance event"
require_line_count 8 '^query ' \
	proofs/pro-verif/hkdf-endpoint-controls-queries.pvl \
	"HKDF endpoint-control query"
require_line_count 8 '^event ' \
	proofs/pro-verif/hkdf-endpoint-controls.pvl \
	"HKDF endpoint-control event"
require_line_count 5 '^let Hkdf' \
	proofs/pro-verif/hkdf-endpoint-controls.pvl \
	"HKDF endpoint-control process"
require_line_count 2 '^query ' \
	proofs/pro-verif/hkdf-domain-alias-control-queries.pvl \
	"HKDF domain differential query"
require_line_count 1 '^letfun deliberately_aliased_domain' \
	proofs/pro-verif/hkdf-domain-alias-control.pvl \
	"deliberate HKDF domain-alias helper"
require_line_count 2 '^let Hkdf.*DomainControl' \
	proofs/pro-verif/hkdf-domain-alias-control.pvl \
	"HKDF domain differential process"
require_line_count 2 '^fun .*\[private\]' \
	proofs/pro-verif/active-quantum-witness.pvl \
	"bounded private quantum recovery operation"
require_line_count 2 '^equation ' \
	proofs/pro-verif/active-quantum-witness.pvl \
	"bounded quantum recovery equation"
require_line_count 1 '^let ActiveQuantumMitm' \
	proofs/pro-verif/active-quantum-witness.pvl \
	"bounded active-quantum witness process"
require_occurrence_count 1 \
	'event QuantumInitialSecretRecovered\(\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*beaconcrypt_core__pqxdh__t_RootKeyInput,\s*bitstring,\s*bitstring\s*\)\.' \
	"exact active-quantum transcript recovery event" \
	proofs/pro-verif/active-quantum-witness.pvl
require_occurrence_count 1 \
	'event\s+QuantumInitialSecretRecovered\(\s*forged_pq,\s*server_ephemeral,\s*kem_ciphertext,\s*initial_frame,\s*response,\s*root_input,\s*root,\s*stolen_plaintext\s*\)' \
	"exact active-quantum transcript recovery emitter" \
	proofs/pro-verif/active-quantum-witness.pvl
require_line_count 3 '^reduc ' \
	proofs/pro-verif/public-key-confusion-control.pvl \
	"production key-confusion parser"
require_line_count 6 '^free ' \
	proofs/pro-verif/public-key-confusion-control.pvl \
	"key-confusion witness"
require_line_count 8 '^event ' \
	proofs/pro-verif/public-key-confusion-control.pvl \
	"key-confusion event"
require_line_count 2 '^let Strong' \
	proofs/pro-verif/public-key-confusion-control.pvl \
	"strong key-confusion process"
require_line_count 8 '^query ' \
	proofs/pro-verif/public-key-confusion-control-queries.pvl \
	"key-confusion query"
require_line_count 2 '^fun ' \
	proofs/pro-verif/public-key-confusion-weak-theory.pvl \
	"weak key-confusion encoding"
require_line_count 4 '^reduc ' \
	proofs/pro-verif/public-key-confusion-weak-theory.pvl \
	"weak key-confusion parser"
require_line_count 4 '^letfun ' \
	proofs/pro-verif/public-key-confusion-weak-theory.pvl \
	"weak key-confusion tag"
require_line_count 2 '^let Weak' \
	proofs/pro-verif/public-key-confusion-weak-theory.pvl \
	"weak key-confusion process"
require_line_count 3 '^fun phase2_.*_binding' \
	proofs/pro-verif/phase2-response-binding-control.pvl \
	"Phase-2 response-binding comparison term"
require_line_count 4 '^free PHASE2_.*_WITNESS' \
	proofs/pro-verif/phase2-response-binding-control.pvl \
	"Phase-2 response-binding witness"
require_line_count 13 '^event Phase2' \
	proofs/pro-verif/phase2-response-binding-control.pvl \
	"Phase-2 response-binding event"
require_line_count 2 '^let Phase2' \
	proofs/pro-verif/phase2-response-binding-control.pvl \
	"Phase-2 response-binding process"
require_line_count 18 '^query ' \
	proofs/pro-verif/phase2-response-binding-queries.pvl \
	"Phase-2 response-binding query"
require_line_count 13 '^query ' \
	proofs/pro-verif/phase2-assigned-id-weak-queries.pvl \
	"weak Phase-2 assigned-ID query"
require_line_count 1 '^free PHASE2_ASSIGNED_ID_BINDING_CANARY: bitstring \[private\]\.$' \
	proofs/pro-verif/phase2-response-binding-control.pvl \
	"Phase-2 assigned-ID differential canary"
reject_matches "primitive rule in Phase-2 response-binding control" \
	'(?m)^(?:reduc|equation) ' \
	proofs/pro-verif/phase2-response-binding-control.pvl
for assigned_id_theory in strong weak; do
	require_line_count 1 '^fun phase2_assigned_id_binding_gate' \
		"proofs/pro-verif/phase2-assigned-id-${assigned_id_theory}-theory.pvl" \
		"${assigned_id_theory} Phase-2 assigned-ID gate declaration"
	require_line_count 1 '^reduc ' \
		"proofs/pro-verif/phase2-assigned-id-${assigned_id_theory}-theory.pvl" \
		"${assigned_id_theory} Phase-2 assigned-ID gate rule"
	reject_matches "extra declaration in ${assigned_id_theory} Phase-2 assigned-ID theory" \
		'(?m)^(?:equation|event|free|let|letfun|process|table|type)\b' \
		"proofs/pro-verif/phase2-assigned-id-${assigned_id_theory}-theory.pvl"
done
require_occurrence_count 1 \
	'phase2_assigned_id_binding_gate\(\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding,\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding\s*\):\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding\s+reduc\s+forall\s+binding:\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding;\s*phase2_assigned_id_binding_gate\(binding,\s*binding\)\s*=\s*binding\.' \
	"exact production Phase-2 assigned-ID equality gate" \
	proofs/pro-verif/phase2-assigned-id-strong-theory.pvl
require_occurrence_count 1 \
	'phase2_assigned_id_binding_gate\(\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding,\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding\s*\):\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding\s+reduc\s+forall\s+authenticated_binding:\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding,\s*outer_binding:\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding;\s*phase2_assigned_id_binding_gate\(\s*authenticated_binding,\s*outer_binding\s*\)\s*=\s*authenticated_binding\.' \
	"exact weakened Phase-2 assigned-ID-only gate" \
	proofs/pro-verif/phase2-assigned-id-weak-theory.pvl
require_occurrence_count 1 \
	'let\s+kex_response\(\s*response_server_identity,\s*server_ephemeral,\s*kem_ciphertext,\s*initial_frame,\s*assigned_key_id\s*\)\s*=\s*response\s+in' \
	"exact Phase-2 response-binding destructure order" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 1 \
	'let\s+wrong_outer_identity_response\s*=\s*kex_response\(\s*wrong_outer_identity,\s*server_ephemeral,\s*kem_ciphertext,\s*initial_frame,\s*assigned_key_id\s*\)\s+in' \
	"wrong outer identity changes only the Phase-2 identity field" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 1 \
	'let\s+relabeled_assigned_id_response\s*=\s*kex_response\(\s*server_identity,\s*server_ephemeral,\s*kem_ciphertext,\s*initial_frame,\s*relabeled_assigned_key_id\s*\)\s+in' \
	"relabeled Phase-2 assigned ID retains the genuine frame" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 1 \
	'new\s+assigned_key_id:\s*key_id;\s*new\s+relabeled_assigned_key_id:\s*key_id;' \
	"fresh distinct original and relabeled Phase-2 assigned IDs" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 1 \
	'let\s+wrong_inner_sender_frame\s*=\s*seal_frame\(\s*server_material,\s*associated_data,\s*first_sequence\(\),\s*wrong_inner_sender_key_id,\s*initial_payload\s*\)\s+in' \
	"wrong inner sender seals an otherwise genuine frame" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 1 \
	'if\s+response_server_identity\s*=\s*expected_server_identity\s+then[\s\S]*?beaconcrypt_core__pqxdh__build_associated_data\(\s*expected_server_identity,\s*beacon_identity\s*\)[\s\S]*?if\s+authenticated_server_key_id\s*=\s*expected_server_key_id\s+then[\s\S]*?open_frame\(\s*server_material,\s*associated_data,\s*frame_sequence,\s*expected_server_key_id,\s*initial_frame\s*\)[\s\S]*?beaconcrypt_core__pqxdh__RegistrationKeyIdBinding\(\s*key_id_encoding\(assigned_key_id\)\s*\)[\s\S]*?phase2_assigned_id_binding_gate\(\s*authenticated_binding,\s*expected_binding\s*\)[\s\S]*?event Phase2ResponseCommitted\(witness\)' \
	"ordered production Phase-2 acceptance gates" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 1 \
	'event\s+Phase2OuterIdentityGateReached\(witness\);\s*if\s+response_server_identity\s*=\s*expected_server_identity\s+then' \
	"internal Phase-2 outer-identity gate witness" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 1 \
	'event\s+Phase2InnerSenderGateReached\(witness\);\s*if\s+authenticated_server_key_id\s*=\s*expected_server_key_id\s+then' \
	"internal Phase-2 inner-sender gate witness" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 1 \
	'let\s+registration_payload\(\s*authenticated_binding,\s*initial_plaintext\s*\)\s*=\s*opened_initial\s+in[\s\S]*?if\s+authenticated_binding\s*=\s*genuine_assigned_binding\s+then\s*event\s+Phase2GenuineAssignedPrefixObserved\(witness\)' \
	"internal Phase-2 original authenticated-prefix witness" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 1 \
	'let\s+admitted_binding\s*=\s*phase2_assigned_id_binding_gate\(\s*authenticated_binding,\s*expected_binding\s*\)\s+in\s*event\s+Phase2AcceptedOuterIdentity\([\s\S]*?\);\s*event\s+Phase2AcceptedAssignedPrefix\([\s\S]*?\);\s*event\s+Phase2AcceptedInnerSender\([\s\S]*?\);\s*event\s+Phase2ResponseCommitted\(witness\);' \
	"sole Phase-2 commit follows all binding antecedents" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 2 \
	'event\s+Phase2ResponseCommitted\(' \
	"one Phase-2 commit declaration and one emission" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_occurrence_count 1 \
	'query\s+event\(Phase2OuterIdentityGateReached\(PHASE2_WRONG_OUTER_IDENTITY_WITNESS\)\)\.' \
	"wrong outer-identity internal-gate witness" \
	proofs/pro-verif/phase2-response-binding-queries.pvl
require_occurrence_count 1 \
	'query\s+event\(Phase2InnerSenderGateReached\(PHASE2_WRONG_INNER_SENDER_WITNESS\)\)\.' \
	"wrong inner-sender internal-gate witness" \
	proofs/pro-verif/phase2-response-binding-queries.pvl
require_occurrence_count 1 \
	'query\s+event\(Phase2AuthenticatedFrameOpened\(PHASE2_RELABELED_ASSIGNED_ID_WITNESS\)\)\.' \
	"relabeled assigned-ID genuine-frame opening witness" \
	proofs/pro-verif/phase2-response-binding-queries.pvl
require_occurrence_count 1 \
	'query\s+event\(Phase2GenuineAssignedPrefixObserved\(PHASE2_RELABELED_ASSIGNED_ID_WITNESS\)\)\.' \
	"relabeled assigned-ID original authenticated-prefix witness" \
	proofs/pro-verif/phase2-response-binding-queries.pvl
require_occurrence_count 3 \
	'query\s+binding: bitstring;\s*event\(Phase2Accepted(?:OuterIdentity|AssignedPrefix|InnerSender)\(binding\)\)\.' \
	"non-vacuous Phase-2 binding antecedent" \
	proofs/pro-verif/phase2-response-binding-queries.pvl
require_occurrence_count 3 \
	'query\s+binding: bitstring;\s*inj-event\(Phase2Accepted(?:OuterIdentity|AssignedPrefix|InnerSender)\(binding\)\)\s*==>\s*inj-event\(Phase2(?:PinnedOuterIdentity|AuthenticatedAssignedPrefix|PinnedInnerSender)\(binding\)\)\.' \
	"Phase-2 response binding correspondence" \
	proofs/pro-verif/phase2-response-binding-queries.pvl
require_occurrence_count 1 \
	'query\s+attacker\(PHASE2_ASSIGNED_ID_BINDING_CANARY\)\.' \
	"production Phase-2 assigned-ID canary secrecy query" \
	proofs/pro-verif/phase2-response-binding-queries.pvl
require_occurrence_count 1 \
	'query\s+queried_authenticated_binding:\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding,\s*queried_outer_binding:\s*beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding;\s*event\(Phase2RelabeledAssignedIdCommitted\(\s*PHASE2_RELABELED_ASSIGNED_ID_WITNESS,\s*queried_authenticated_binding,\s*queried_outer_binding\s*\)\)\.' \
	"weak Phase-2 relabeled-ID commit witness" \
	proofs/pro-verif/phase2-assigned-id-weak-queries.pvl
require_occurrence_count 1 \
	'query\s+attacker\(PHASE2_ASSIGNED_ID_BINDING_CANARY\)\.' \
	"weak Phase-2 assigned-ID canary disclosure query" \
	proofs/pro-verif/phase2-assigned-id-weak-queries.pvl
require_occurrence_count 1 \
	'event\s+Phase2ResponseCommitted\(witness\);\s*if\s+witness\s*=\s*PHASE2_RELABELED_ASSIGNED_ID_WITNESS\s+then\s*event\s+Phase2RelabeledAssignedIdCommitted\(\s*witness,\s*authenticated_binding,\s*expected_binding\s*\);\s*out\(c,\s*PHASE2_ASSIGNED_ID_BINDING_CANARY\)\.' \
	"relabeled Phase-2 commit canary release" \
	proofs/pro-verif/phase2-response-binding-control.pvl
require_line_count 8 '^query ' \
	proofs/pro-verif/mlkem-reencapsulation-control-queries.pvl \
	"ML-KEM re-encapsulation control query"
require_line_count 7 '^free KEM_' \
	proofs/pro-verif/mlkem-reencapsulation-control.pvl \
	"ML-KEM re-encapsulation witness"
require_line_count 8 '^event Kem' \
	proofs/pro-verif/mlkem-reencapsulation-control.pvl \
	"ML-KEM re-encapsulation event"
require_line_count 2 '^let Kem' \
	proofs/pro-verif/mlkem-reencapsulation-control.pvl \
	"ML-KEM re-encapsulation process"
require_occurrence_count 1 \
	'fun kem_control_commit_transcript\(\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*bitstring,\s*key_id,\s*key_id,\s*bitstring,\s*bitstring\s*\): bitstring \[data\]\.' \
	"exact ML-KEM control transcript arity" \
	proofs/pro-verif/mlkem-reencapsulation-control.pvl
require_occurrence_count 1 \
	'out\(kem_multi_epoch_channel, pqsk_old\);\s*event KemOldKeyCompromised\(KEM_OLD_KEY_COMPROMISE_WITNESS\)' \
	"old-only ML-KEM compromise emitter" \
	proofs/pro-verif/mlkem-reencapsulation-control.pvl
reject_matches "new ML-KEM secret key disclosed by re-encapsulation control" \
	'out\([^\n]*pqsk_new' \
	proofs/pro-verif/mlkem-reencapsulation-control.pvl
require_occurrence_count 1 \
	'candidate_ciphertext\s*=\s*reencapsulate\(\s*old_shared_secret,\s*pqpk_new\s*\)' \
	"exact cross-key ciphertext substitution" \
	proofs/pro-verif/mlkem-reencapsulation-control.pvl
require_occurrence_count 1 \
	'kem_control_commit_transcript\(\s*server_identity,\s*beacon_identity,\s*bundle_old,\s*beacon_prekey,\s*beacon_one_time,\s*pqpk_old,\s*old_ciphertext,' \
	"old-bundle server control transcript" \
	proofs/pro-verif/mlkem-reencapsulation-control.pvl
require_occurrence_count 1 \
	'kem_control_commit_transcript\(\s*server_identity,\s*beacon_identity,\s*bundle_new,\s*beacon_prekey,\s*beacon_one_time,\s*pqpk_new,\s*candidate_ciphertext,' \
	"new-bundle beacon control transcript" \
	proofs/pro-verif/mlkem-reencapsulation-control.pvl
require_line_count 1 '^reduc ' \
	proofs/pro-verif/mlkem-reencapsulation-strong-theory.pvl \
	"strong ML-KEM control decapsulation rule"
require_line_count 1 '^reduc ' \
	proofs/pro-verif/mlkem-reencapsulation-weak-theory.pvl \
	"weak ML-KEM control reduction block"
require_occurrence_count 1 \
	'otherwise\s+forall shared_secret: bitstring, new_secret_key: bitstring;\s*kem_control_decapsulate\(\s*reencapsulate\(shared_secret, mlkem_public\(new_secret_key\)\),\s*new_secret_key\s*\) = shared_secret\.' \
	"public weak-KEM re-encapsulation rule" \
	proofs/pro-verif/mlkem-reencapsulation-weak-theory.pvl
for scenario_process in \
	passive \
	passive-strong-secrecy \
	hkdf-prefix-conformance \
	hkdf-endpoint-controls \
	hkdf-domain-alias-control \
	hkdf-domain-distinct-control \
	active-quantum \
	quantum-capability-control \
	quantum-mlkem-control \
	mlkem-reencapsulation-control \
	public-key-confusion-strong \
	public-key-confusion-weak \
	phase2-response-binding \
	phase2-assigned-id-weak \
	later-sequence-registration; do
	require_line_count 1 '^process$' \
		"proofs/pro-verif/${scenario_process}.pv" \
			"${scenario_process} top-level process"
done

fidelity_test=tests/proverif_transcript_fidelity.rs
require_line_count 34 \
	'^const (INTERFACE|CRYPTO_MODEL|ENVIRONMENT_MODEL|ACTIVE_QUANTUM_WITNESS|EXTRACTION_MODEL|CORE_MAKEFILE|ADAPTER_PQXDH|ADAPTER_RATCHET|ADAPTER_SHARED|ADAPTER_SERVER|ADAPTER_BEACON|CORE_COMMITMENT|CORE_PQXDH|CORE_PQXDH_CONCRETE|CORE_RATCHET|CORE_RATCHET_CONCRETE|CORE_RATCHET_CONTROL|CORE_RATCHET_REFINED|LEAN_PQXDH_KDF|CRYPTOFRAME_SCHEMA|PHASE1_SCHEMA|PHASE2_SCHEMA|FAILED_RECEIVE_QUERIES|PROVERIF_RESULT_CHECKER): &str = include_str!|^const (MLKEM_REENCAPSULATION_CONTROL|LEAN_RATCHET_EFFECT|LEAN_RATCHET_EFFECT_REFINEMENT|LEAN_PQXDH_THEOREMS|FAILED_RECEIVE_REACHABILITY_QUERIES|LATER_REGISTRATION_CONTROL|LATER_REGISTRATION_QUERIES|LATER_REGISTRATION_MAIN|LEAN_RATCHET_CONTROL|LEAN_RATCHET_REFINEMENT): &str =$' \
	"$fidelity_test" "transcript-fidelity synchronized input"
require_line_count 1 '^const EXPECTED_FACTS: &\[&str\] = &\[$' \
	"$fidelity_test" "transcript-fidelity exact fact allowlist"
require_line_count 1 '^struct Snapshot \{$' \
	"$fidelity_test" "transcript-fidelity mutable snapshot"
require_line_count 13 '^#\[test\]$' \
	"$fidelity_test" "transcript-fidelity test"
for fidelity_test_name in \
	production_manifest_symbolic_model_and_adapters_are_exact \
	compiled_core_matches_the_canonical_transcript \
	cryptoframe_wire_mutation_matrix_is_complete_and_rejected \
	endpoint_frame_context_mutation_matrix_is_complete_and_rejected \
	ratchet_effect_driver_mutation_matrix_is_complete_and_rejected \
	finite_receive_state_fixture_mutation_matrix_is_complete_and_rejected \
	registration_lifecycle_mutation_matrix_is_complete_and_rejected \
	initial_ratchet_source_model_fidelity_is_exact_and_nonvacuous \
	initial_ratchet_mutation_matrix_is_complete_and_rejected \
	later_registration_sequence_three_poststate_is_exact_and_nonvacuous \
	later_registration_mutation_matrix_is_complete_and_rejected \
	phase1_registration_mutation_matrix_is_complete_and_rejected \
	requested_transcript_mutations_are_rejected; do
	require_line_count 1 "^fn ${fidelity_test_name}\\(\\) \\{\$" \
		"$fidelity_test" "transcript-fidelity ${fidelity_test_name} test"
done
require_occurrence_count 1 \
	'fn production_manifest_symbolic_model_and_adapters_are_exact\(\) \{\s*validate\(&Snapshot::production\(\)\)\.unwrap\(\);\s*validate_adapters\(\)\.unwrap\(\);\s*\}' \
	"transcript-fidelity model and adapter composition" "$fidelity_test"
require_occurrence_count 1 \
	'fn validate\(snapshot: &Snapshot\) -> Result<\(\), String> \{\s*validate_manifest\(&snapshot\.interface\)\?;\s*validate_pv\(snapshot\)\?;\s*validate_phase1_source\(snapshot\)\?;\s*validate_phase2_source\(snapshot\)\?;\s*validate_cryptoframe_source\(snapshot\)\?;\s*validate_endpoint_frame_context_wiring\(snapshot\)\?;\s*validate_ratchet_effect_driver\(snapshot\)\?;\s*validate_finite_receive_state_fixture\(snapshot\)\?;\s*validate_registration_lifecycle\(snapshot\)\?;\s*validate_initial_ratchet_fidelity\(snapshot\)\?;\s*validate_later_registration_fidelity\(snapshot\)\?;\s*validate_makefile\(&snapshot\.makefile\)\s*\}' \
	"transcript-fidelity combined validator" "$fidelity_test"
require_line_count 1 '^const CRYPTOFRAME_WIRE_MUTATION_COUNT: usize = 223;$' \
	"$fidelity_test" "CryptoFrame exact mutation count"
require_occurrence_count 1 \
	'(?s)fn cryptoframe_wire_mutation_matrix_is_complete_and_rejected\(\) \{.*?assert_eq!\(mutation_count, CRYPTOFRAME_WIRE_MUTATION_COUNT\);\s*\}' \
	"CryptoFrame mutation matrix count assertion" "$fidelity_test"
for cryptoframe_mutation_family in \
	cryptoframe_schema_declaration_permutation_ \
	cryptoframe_schema_ordinal_permutation_ \
	cryptoframe_schema_omits_field_ \
	cryptoframe_schema_renames_field_ \
	cryptoframe_payload_permutation_ \
	cryptoframe_payload_omits_field_ \
	cryptoframe_payload_duplicate_ \
	cryptoframe_builder_order_permutation_ \
	cryptoframe_getter_permutation_ \
	cryptoframe_open_tag_slice_starts_late \
	cryptoframe_open_commitment_slice_starts_late \
	cryptoframe_open_decrypts_before_commitment_equality \
	cryptoframe_core_le64_uses_big_endian_order \
	cryptoframe_core_reorders_tag_and_sequence_branches \
	cryptoframe_symbolic_annotation_permutation_ \
	cryptoframe_symbolic_seal_argument_permutation_ \
	cryptoframe_symbolic_seal_field_permutation_ \
	cryptoframe_symbolic_open_field_permutation_ \
	cryptoframe_symbolic_open_argument_permutation_ \
	cryptoframe_ctx_pair_transposition_ \
	cryptoframe_ctx_omits_and_duplicates_field_; do
	require_occurrence_count 1 "$cryptoframe_mutation_family" \
		"CryptoFrame ${cryptoframe_mutation_family} mutation family" "$fidelity_test"
done
require_line_count 1 '^const PHASE1_REGISTRATION_MUTATION_COUNT: usize = 163;$' \
	"$fidelity_test" "Phase-1 exact mutation count"
require_occurrence_count 1 \
	'(?s)fn phase1_registration_mutation_matrix_is_complete_and_rejected\(\) \{.*?assert_eq!\(mutation_count, PHASE1_REGISTRATION_MUTATION_COUNT\);\s*\}' \
	"Phase-1 mutation matrix count assertion" "$fidelity_test"
for phase1_mutation_family in \
	phase1_schema_same_typed_permutation_ \
	phase1_schema_omits_field_ \
	phase1_schema_renames_ \
	phase1_schema_ordinal_drift_ \
	phase1_beacon_setter_ \
	phase1_beacon_signature_ \
	phase1_server_consumer_ \
	phase1_from_encoded_swaps_x25519_roles \
	phase1_symbolic_declaration_transposition_ \
	phase1_symbolic_active_quantum_producer_transposition_ \
	phase1_symbolic_active_quantum_consumer_transposition_ \
	phase1_core_prekey_uses_one_time_role \
	phase1_core_prekey_validates_one_time_role \
	phase1_server_accepts_mlkem_identity_tag \
	phase1_server_decodes_identity_with_tag \
	phase1_symbolic_signature_verifies_under_x25519_key \
	phase1_server_reorders_pq_and_prekey_verification \
	phase1_symbolic_reorders_prekey_and_one_time_gates \
	phase1_beacon_serializes_identity_after_prekey_signature \
	phase1_core_reorders_prekey_and_one_time_fields \
	phase1_core_reorders_prekey_and_one_time_validation; do
	require_occurrence_count 1 "$phase1_mutation_family" \
		"Phase-1 ${phase1_mutation_family} mutation family" "$fidelity_test"
done
require_line_count 1 '^const ENDPOINT_FRAME_CONTEXT_MUTATION_COUNT: usize = 242;$' \
	"$fidelity_test" "endpoint frame-context exact mutation count"
require_occurrence_count 1 \
	'(?s)fn endpoint_frame_context_mutation_matrix_is_complete_and_rejected\(\) \{.*?assert_eq!\(mutation_count, ENDPOINT_FRAME_CONTEXT_MUTATION_COUNT\);\s*\}' \
	"endpoint frame-context mutation matrix count assertion" "$fidelity_test"
for endpoint_mutation_family in \
	endpoint_fact_\{key\} \
	endpoint_sender_parser_ignores_wire \
	endpoint_server_ad_reverses_identities \
	endpoint_server_send_target_uses_local_sender \
	endpoint_server_receive_ignores_parsed_sender \
	endpoint_server_receive_fail_open \
	endpoint_beacon_send_target_uses_assigned_id \
	endpoint_beacon_receive_expected_sender_uses_assigned_id \
	endpoint_registration_server_map_discards_peer_identity \
	endpoint_registration_server_publishes_control_before_peer_insert \
	endpoint_registration_beacon_expected_sender_uses_outer_id \
	endpoint_registration_beacon_assigns_local_id_before_server_binding_checks \
	endpoint_symbolic_\{family\}_\{field\}_\{call_index\} \
	endpoint_symbolic_honest_server_open_count_increases \
	endpoint_symbolic_server_seal_count_increases \
	endpoint_symbolic_malicious_initial_seal_count_increases \
	endpoint_symbolic_\{family\}_event_\{field\}_\{call_index\} \
	endpoint_symbolic_honest_received_event_count_increases \
	endpoint_symbolic_server_received_event_count_increases \
	endpoint_symbolic_honest_received_event_arity_increases \
	endpoint_symbolic_server_received_event_arity_increases \
	endpoint_symbolic_honest_ad_reverses_identities \
	endpoint_symbolic_malicious_server_ad_reverses_identities; do
	require_occurrence_count 1 "$endpoint_mutation_family" \
		"endpoint frame-context ${endpoint_mutation_family} mutation family" "$fidelity_test"
done
require_line_count 1 '^const RATCHET_EFFECT_DRIVER_MUTATION_COUNT: usize = 154;$' \
	"$fidelity_test" "ratchet effect-driver exact mutation count"
require_occurrence_count 1 \
	'(?s)fn ratchet_effect_driver_mutation_matrix_is_complete_and_rejected\(\) \{.*?assert_eq!\(mutation_count, RATCHET_EFFECT_DRIVER_MUTATION_COUNT\);\s*\}' \
	"ratchet effect-driver mutation matrix count assertion" "$fidelity_test"
for ratchet_driver_mutation_family in \
	ratchet_driver_fact_\{key\} \
	ratchet_driver_slot_take_duplicates_take \
	ratchet_driver_send_resumes_different_pending \
	ratchet_driver_send_returns_before_put \
	ratchet_driver_receive_moves_empty_gate_after_take \
	ratchet_driver_receive_takes_kernel_before_typed_parse \
	ratchet_driver_receive_moves_sender_gate_after_take \
	ratchet_driver_receive_moves_length_gate_after_take \
	ratchet_driver_receive_resumes_different_pending \
	ratchet_driver_receive_kdf_publishes_slot \
	ratchet_driver_receive_questions_result_before_put \
	ratchet_driver_core_finish_none_drops_entry \
	ratchet_driver_core_finish_cached_publication_omitted \
	ratchet_driver_core_finish_future_publication_omitted \
	ratchet_driver_core_begin_receive_mutates_live_control \
	ratchet_driver_core_receive_kdf_publishes_cached_early \
	ratchet_driver_core_receive_kdf_publishes_future_early \
	ratchet_driver_lean_structural_anchor_\{index\}_renamed \
	ratchet_driver_lean_failure_trace_anchor_renamed \
	ratchet_driver_lean_conditional_anchor_\{index\}_renamed \
	ratchet_driver_proverif_renames_atomic_seal \
	ratchet_driver_proverif_renames_ideal_open \
	ratchet_driver_proverif_exposes_\{concrete_step\}; do
	require_occurrence_count 1 "$ratchet_driver_mutation_family" \
		"ratchet effect-driver ${ratchet_driver_mutation_family} mutation family" "$fidelity_test"
done
require_line_count 1 '^const FINITE_RECEIVE_STATE_FIXTURE_MUTATION_COUNT: usize = 1_230;$' \
	"$fidelity_test" "finite receive-state fixture exact mutation count"
require_occurrence_count 1 \
	'(?s)fn finite_receive_state_fixture_mutation_matrix_is_complete_and_rejected\(\) \{.*?assert_eq!\(mutation_count, FINITE_RECEIVE_STATE_FIXTURE_MUTATION_COUNT\);\s*\}' \
	"finite receive-state fixture mutation matrix count assertion" "$fidelity_test"
for receive_fixture_mutation_family in \
	finite_receive_fixture_fact_\{key\} \
	finite_receive_core_changes_max_gap \
	finite_receive_core_finish_failure_drops_entry \
	finite_receive_proverif_omits_capacity_leg \
	finite_receive_short_open_\{call_index\}_argument_\{argument_index\} \
	finite_receive_short_first_bypasses_destructor_failure \
	finite_receive_short_retry_bypasses_destructor_failure \
	finite_receive_short_rejection_snapshot_field_\{index\} \
	finite_receive_short_retains_target_in_cache \
	finite_receive_capacity_sequence_\{sequence\}_drifts \
	finite_receive_capacity_cached_event_\{event_index\}_argument_\{argument_index\} \
	finite_receive_capacity_cached_consumed_argument_\{argument_index\} \
	finite_receive_capacity_retains_target_\{target\} \
	finite_receive_correspondence_\{event\}_\{occurrence\}_argument_\{argument_index\} \
	finite_receive_reachability_\{event\}_argument_\{argument_index\} \
	finite_receive_correspondence_count_drops \
	finite_receive_reachability_query_count_drops; do
	require_occurrence_count 1 "$receive_fixture_mutation_family" \
		"finite receive-state ${receive_fixture_mutation_family} mutation family" "$fidelity_test"
done
require_line_count 1 '^const REGISTRATION_LIFECYCLE_MUTATION_COUNT: usize = 177;$' \
	"$fidelity_test" "registration lifecycle exact mutation count"
require_occurrence_count 1 \
	'(?s)fn registration_lifecycle_mutation_matrix_is_complete_and_rejected\(\) \{.*?assert_eq!\(mutation_count, REGISTRATION_LIFECYCLE_MUTATION_COUNT\);\s*\}' \
	"registration lifecycle mutation matrix count assertion" "$fidelity_test"
for registration_lifecycle_mutation_family in \
	registration_lifecycle_fact_\{key\} \
	registration_identifier_first_half_uses_prekey \
	registration_proverif_projection_uses_pq \
	registration_pretransition_failure_changes_state \
	registration_finish_server_key_id_mismatch_keeps_init \
	registration_finish_server_identity_mismatch_keeps_init \
	registration_server_dh4_moves_before_status_gate \
	registration_server_consumes_different_id_before_crypto \
	registration_server_explicit_failure_after_consumption \
	registration_honest_different_guard_is_duplicated \
	registration_honest_guard_and_bundle_are_sequential \
	registration_malicious_server_adds_replay_guard \
	registration_hb49_\{label\}_bundle_argument_\{argument_index\}; do
	require_occurrence_count 1 "$registration_lifecycle_mutation_family" \
		"registration lifecycle ${registration_lifecycle_mutation_family} mutation family" "$fidelity_test"
done
require_line_count 1 '^const INITIAL_RATCHET_MUTATION_COUNT: usize = 223;$' \
	"$fidelity_test" "initial-ratchet exact mutation count"
require_occurrence_count 1 \
	'(?s)fn initial_ratchet_mutation_matrix_is_complete_and_rejected\(\) \{.*?assert_eq!\(mutation_count, INITIAL_RATCHET_MUTATION_COUNT\);\s*\}' \
	"initial-ratchet mutation matrix count assertion" "$fidelity_test"
for initial_ratchet_mutation_family in \
	initial_ratchet_fact_\{key\} \
	initial_ratchet_derived_root_alias_size_drifts \
	initial_ratchet_derived_root_accessor_substitutes_data \
	initial_ratchet_server_output_consumer_borrows_value \
	initial_ratchet_server_handoff_root_is_shadowed \
	initial_ratchet_server_kdf_pending_is_shadowed \
	initial_ratchet_beacon_root_is_shadowed \
	initial_ratchet_beacon_kdf_pending_is_shadowed \
	initial_ratchet_candidate_role_methods_swap_together \
	initial_ratchet_left_and_right_slices_swap \
	initial_ratchet_request_input_accessor_substituted \
	initial_ratchet_pending_derives_clone \
	initial_ratchet_pending_derives_copy \
	initial_ratchet_response_confuses_76_byte_step_type \
	initial_ratchet_response_constructor_substitutes_bytes \
	initial_ratchet_server_candidate_start_return_type_drifts \
	initial_ratchet_kernel_initial_chains_swap \
	initial_ratchet_adapter_executor_substitutes_output_bytes \
	initial_ratchet_adapter_response_is_shadowed \
	initial_ratchet_adapter_pending_parameter_is_shadowed \
	initial_ratchet_lean_ideal_chain_agreement_anchor_renamed \
	initial_ratchet_pv_honest_beacon_root_constructor_drifts \
	initial_ratchet_pv_malicious_server_root_input_drifts \
	initial_ratchet_pv_honest_beacon_initial_material_uses_wrong_chain \
	initial_ratchet_pv_server_root_is_shadowed; do
	require_occurrence_count 1 "$initial_ratchet_mutation_family" \
		"initial-ratchet ${initial_ratchet_mutation_family} mutation family" "$fidelity_test"
done
require_line_count 1 '^const LATER_REGISTRATION_MUTATION_COUNT: usize = 409;$' \
	"$fidelity_test" "later-sequence registration exact mutation count"
require_occurrence_count 1 \
	'(?s)fn later_registration_mutation_matrix_is_complete_and_rejected\(\) \{.*?assert_eq!\(mutation_count, LATER_REGISTRATION_MUTATION_COUNT\);\s*\}' \
	"later-sequence registration mutation matrix count assertion" "$fidelity_test"
for later_registration_mutation_family in \
	later_registration_fact_\{key\} \
	later_registration_beacon_reads_decrypted_sequence \
	later_registration_beacon_adds_first_sequence_gate \
	later_registration_adapter_adds_first_sequence_gate \
	later_registration_core_begin_entry_substituted \
	later_registration_core_staged_sequence_substituted \
	later_registration_refined_pending_target_substituted \
	later_registration_staged_scan_accepts_live_slot \
	later_registration_slot_mover_wrong_destination \
	later_registration_publisher_inserts_target \
	later_registration_pv_beacon_dh1_secret_substituted \
	later_registration_pv_beacon_kem_ciphertext_substituted \
	later_registration_pv_beacon_shared_dh_order_swapped \
	later_registration_pv_server_dh1_secret_substituted \
	later_registration_pv_server_kem_ciphertext_key_substituted \
	later_registration_pv_server_shared_dh_order_swapped \
	later_registration_pv_substitution_outer_identity_changed \
	later_registration_pv_candidate_gate_bypassed \
	later_registration_pv_faithful_adds_sequence_gate \
	later_registration_pv_first_only_gate_moved_before_open_reply \
	later_registration_poststate_query_cache_order_mutated \
	later_registration_target_query_material3_mutated \
	later_registration_query_\{\}_formula_mutated \
	later_registration_checker_result_\{index\}_term_mutated \
	later_registration_checker_result_\{index\}_polarity_mutated \
	later_registration_checker_query_count_mutated; do
	require_occurrence_count 1 "$later_registration_mutation_family" \
		"later-sequence registration ${later_registration_mutation_family} mutation family" "$fidelity_test"
done
require_line_count 1 '^\s*"later_registration_make_scenario_removed",$' \
	"$fidelity_test" "later-sequence registration scenario-removal mutation"
require_line_count 1 '^\s*if name == "later_registration_make_scenario_removed" \{$' \
	"$fidelity_test" "later-sequence registration scenario-removal mutation dispatch"
for mutation_name in \
	pqxdh_label_byte \
	symmetric_label_byte \
	aliased_domains \
	separate_initial_step_domain \
	reversed_ad_identities \
	swapped_x25519_roles \
	reordered_phase2_manifest_field \
	changed_phase2_manifest_constructor \
	changed_phase2_manifest_field_count \
	changed_phase2_manifest_field_0 \
	changed_phase2_manifest_field_1 \
	changed_phase2_manifest_field_2 \
	changed_phase2_manifest_field_4 \
	changed_phase2_manifest_server_writes \
	changed_phase2_manifest_beacon_reads \
	legacy_phase2_symbolic_order \
	permuted_phase2_beacon_destructure \
	permuted_phase2_response_construction \
	permuted_active_quantum_phase2_destructure \
	reordered_phase2_schema_fields \
	omitted_phase2_schema_field \
	renamed_phase2_schema_field \
	swapped_phase2_server_identity_mapping \
	swapped_phase2_server_ephemeral_mapping \
	swapped_phase2_server_kem_mapping \
	swapped_phase2_server_frame_mapping \
	swapped_phase2_server_key_id_mapping \
	swapped_phase2_beacon_identity_mapping \
	swapped_phase2_beacon_ephemeral_mapping \
	swapped_phase2_beacon_kem_mapping \
	swapped_phase2_beacon_frame_mapping \
	swapped_phase2_beacon_key_id_mapping \
	agreement_without_selected_pqpk \
	agreement_without_kem_ciphertext \
	ctx_without_key \
	ctx_without_nonce \
	ctx_without_associated_data \
	ctx_without_retained_aead_tag \
	ctx_without_sequence \
	ctx_without_sender_id; do
	require_occurrence_count 1 "\"${mutation_name}\"" \
		"transcript-fidelity ${mutation_name} mutation" "$fidelity_test"
done
require_line_count 1 \
	'^exclude = \["Makefile", "proofs/\*\*", "tests/proverif_transcript_fidelity\.rs"\]$' \
	Cargo.toml "transcript-fidelity publication exclusion"
require_line_count 1 \
	'^PROVERIF_INTERFACE := \$\(PROVERIF_DIR\)/production-transcript-interface\.pvl$' \
	Makefile "canonical ProVerif transcript interface path"
require_line_count 1 '^check-proverif-transcript-fidelity:$' \
	Makefile "transcript-fidelity Make target"
require_line_count 1 \
	'^\tcargo test --locked -p beaconcrypt-core --test proverif_transcript_fidelity$' \
	Makefile "transcript-fidelity test invocation"
require_line_count 1 \
	'^\$\(PROVERIF_CHECK_TARGETS\): check-proverif-transcript-fidelity$' \
	Makefile "per-scenario transcript-fidelity prerequisite"
require_line_count 1 \
	'^check-proverif-passive-reachability check-proverif-quantum-capabilities: check-proverif-transcript-fidelity$' \
	Makefile "auxiliary ProVerif transcript-fidelity prerequisite"
require_line_count 1 '^check-proverif: check-proverif-transcript-fidelity$' \
	Makefile "aggregate transcript-fidelity prerequisite"
require_occurrence_count 1 \
	'check-proverif-phase2-assigned-id-weak:\s+check-proverif-extraction\s+\\\s*check-proverif-phase2-response-binding' \
	"weak Phase-2 target paired with production response binding" \
	Makefile
require_occurrence_count 1 \
	'check-proverif-phase2-response-binding:\s+check-proverif-extraction[\s\S]*?\$\(PROVERIF_COMMON_LIBS\)\s+\\\s*-lib \$\(PROVERIF_DIR\)/phase2-assigned-id-strong-theory\.pvl\s+\\\s*-lib \$\(PROVERIF_DIR\)/phase2-response-binding-control\.pvl\s+\\[\s\S]*?awk -v scenario=phase2-response-binding' \
	"production Phase-2 target loads only the strong assigned-ID gate" \
	Makefile
require_occurrence_count 1 \
	'check-proverif-phase2-assigned-id-weak:\s+check-proverif-extraction[\s\S]*?\$\(PROVERIF_COMMON_LIBS\)\s+\\\s*-lib \$\(PROVERIF_DIR\)/phase2-assigned-id-weak-theory\.pvl\s+\\\s*-lib \$\(PROVERIF_DIR\)/phase2-response-binding-control\.pvl\s+\\[\s\S]*?awk -v scenario=phase2-assigned-id-weak' \
	"weak Phase-2 target loads only the weak assigned-ID gate" \
	Makefile
require_occurrence_count 1 \
	'check-proverif-later-sequence-registration:\s+check-proverif-extraction[\s\S]*?\$\(PROVERIF_COMMON_LIBS\)\s+\\\s*-lib \$\(PROVERIF_DIR\)/phase2-assigned-id-strong-theory\.pvl\s+\\\s*-lib \$\(PROVERIF_DIR\)/later-sequence-registration-control\.pvl\s+\\\s*-lib \$\(PROVERIF_DIR\)/later-sequence-registration-queries\.pvl\s+\\[\s\S]*?awk -v scenario=later-sequence-registration' \
	"later-sequence registration target loads the reviewed finite control and queries" \
	Makefile
require_line_count 8 '^free LATER_REGISTRATION_' \
	proofs/pro-verif/later-sequence-registration-control.pvl \
	"later-sequence registration private fixture value"
require_line_count 12 '^event LaterRegistration' \
	proofs/pro-verif/later-sequence-registration-control.pvl \
	"later-sequence registration event declaration"
require_line_count 5 '^let LaterSequenceRegistration' \
	proofs/pro-verif/later-sequence-registration-control.pvl \
	"later-sequence registration finite process"
require_line_count 18 '^query ' \
	proofs/pro-verif/later-sequence-registration-queries.pvl \
	"later-sequence registration query"
require_occurrence_count 1 \
	'else if \(scenario == "later-sequence-registration"\) \{\s*if \(query_count != 18\)' \
	"later-sequence registration exact result count" \
	proofs/pro-verif/check-results.awk
require_occurrence_count 1 \
	'for \(later_index = 1; later_index <= 18; later_index\+\+\) \{\s*require_exact\(later_expected\[later_index\],' \
	"later-sequence registration exact result loop" \
	proofs/pro-verif/check-results.awk
require_line_count 2 \
	'^\s*-lib \$\(PROVERIF_DIR\)/phase2-assigned-id-strong-theory\.pvl \\$' \
	Makefile "production Phase-2 and later-registration assigned-ID gate loaders"
require_line_count 1 \
	'^\s*-lib \$\(PROVERIF_DIR\)/phase2-assigned-id-weak-theory\.pvl \\$' \
	Makefile "weak Phase-2 assigned-ID gate loader"
require_line_count 2 \
	'^\s*-lib \$\(PROVERIF_DIR\)/phase2-response-binding-control\.pvl \\$' \
	Makefile "shared strong/weak Phase-2 control loader"
require_occurrence_count 1 \
	'PROVERIF_CRYPTO_LIBS :=\s*\\\s*-lib \$\(PROVERIF_INTERFACE\)\s*\\\s*-lib \$\(PROVERIF_DIR\)/crypto\.pvl' \
	"canonical interface loaded before cryptographic theory" Makefile
require_line_count 1 '^            target: check-proverif-transcript-fidelity$' \
	../.github/workflows/formal-verification.yml \
	"dedicated transcript-fidelity CI target"
require_line_count 1 '^            target: check-generated-proverif-phase2-response-binding$' \
	../.github/workflows/formal-verification.yml \
	"dedicated Phase-2 response-binding CI target"
require_line_count 1 '^            target: check-generated-proverif-phase2-assigned-id-weak$' \
	../.github/workflows/formal-verification.yml \
	"dedicated weak Phase-2 assigned-ID CI target"

require_line_count 1 '^  Theorem ctx_misattribution_reduces_to_collision :' \
	proofs/ssprove/CtxEventReduction.v \
	"SSProve CTX event-reduction capstone"
require_line_count 1 '^Print Assumptions ctx_misattribution_reduces_to_collision\.$' \
	proofs/ssprove/CtxEventReduction.v \
	"SSProve CTX assumption report"
require_line_count 1 '^  Theorem run_bounded_rom_query_count_bound$' \
	proofs/ssprove/BoundedRom.v \
	"SSProve bounded-ROM query-count theorem"
require_line_count 1 '^  Theorem run_bounded_rom_trace_consistent$' \
	proofs/ssprove/BoundedRom.v \
	"SSProve bounded-ROM trace-consistency theorem"
require_line_count 1 '^  Theorem bounded_rom_same_run_extractor_reduction$' \
	proofs/ssprove/BoundedRom.v \
	"SSProve bounded-ROM extractor reduction"
require_line_count 1 '^Print Assumptions bounded_rom_same_run_extractor_reduction\.$' \
	proofs/ssprove/BoundedRom.v \
	"SSProve bounded-ROM assumption report"
require_line_count 1 '^Theorem ctx_hidden_rom_extractor_reduction$' \
	proofs/ssprove/CtxGame.v \
	"SSProve hidden-ROM CTX extractor reduction"
require_line_count 1 '^Corollary ctx_uniform_hidden_rom_extractor_reduction$' \
	proofs/ssprove/CtxGame.v \
	"SSProve uniform-ROM CTX extractor reduction"
require_line_count 1 '^Theorem ctx_hidden_binding_trace_size_bound$' \
	proofs/ssprove/CtxGame.v \
	"SSProve CTX query-count theorem"
require_line_count 1 '^Theorem ctx_attach_verifier_completed_run$' \
	proofs/ssprove/CtxGame.v \
	"SSProve CTX verifier-suffix theorem"
require_line_count 1 '^Lemma ctx_hidden_misattribution_challenge_reachable :' \
	proofs/ssprove/CtxGame.v \
	"SSProve CTX non-vacuity witness"
require_line_count 1 '^Print Assumptions ctx_hidden_rom_extractor_reduction\.$' \
	proofs/ssprove/CtxGame.v \
	"SSProve CTX extractor assumption report"
require_line_count 1 '^  Theorem ctx_true_real_is_programmed_real$' \
	proofs/ssprove/CtxPrivacy.v \
	"SSProve CTX programming representation theorem"
require_line_count 1 '^  Theorem ctx_same_run_mismatch_implies_secret_query$' \
	proofs/ssprove/CtxPrivacy.v \
	"SSProve CTX secret-query fundamental lemma"
require_line_count 1 '^  Theorem ctx_hidden_uniform_key_privacy_hop$' \
	proofs/ssprove/CtxPrivacy.v \
	"SSProve CTX hidden-key privacy hop"
require_line_count 1 '^  Theorem ctx_hidden_true_real_is_programmed_real$' \
	proofs/ssprove/CtxPrivacy.v \
	"SSProve CTX hidden-key programming representation"
require_line_count 1 '^  Theorem ctx_hidden_true_programmed_decision_probability$' \
	proofs/ssprove/CtxPrivacy.v \
	"SSProve CTX true/programmed decision equality"
require_line_count 1 '^  Theorem ctx_programmed_fresh_decision_advantage_bound$' \
	proofs/ssprove/CtxPrivacy.v \
	"SSProve CTX programmed/fresh advantage bound"
require_line_count 1 '^  Theorem ctx_hidden_uniform_key_true_real_privacy_bound$' \
	proofs/ssprove/CtxPrivacy.v \
	"SSProve CTX true-real/fresh-ideal privacy bound"
require_line_count 1 '^Print Assumptions ctx_hidden_uniform_key_true_real_privacy_bound\.$' \
	proofs/ssprove/CtxPrivacy.v \
	"SSProve CTX true-real privacy assumption report"
for label_capstone in \
	kdf_domain_tag_models_exact_info \
	production_kdf_labels_are_exact \
	initial_and_step_share_symmetric_domain \
	production_kdf_output_sizes \
	associated_data_label_suffix_is_exact; do
	require_line_count 1 "^Theorem ${label_capstone} :" \
		proofs/ssprove/ProtocolLabels.v \
		"SSProve exact-label ${label_capstone} theorem"
	require_line_count 1 \
		"^Print Assumptions ${label_capstone}\\.\$" \
		proofs/ssprove/ProtocolLabels.v \
		"SSProve exact-label ${label_capstone} assumption report"
done
for protocol_capstone in \
	active_classical_confidentiality \
	passive_classical_confidentiality \
	passive_quantum_capability_confidentiality \
	active_quantum_advantage_one; do
	require_line_count 1 "^Theorem ${protocol_capstone} :" \
		proofs/ssprove/PqxdhRatchetGames.v \
		"SSProve protocol ${protocol_capstone} capstone"
done
for protocol_assumption_report in \
	active_classical_confidentiality \
	passive_classical_confidentiality \
	passive_quantum_confidentiality \
	active_quantum_advantage_one; do
	require_line_count 1 \
		"^Print Assumptions ${protocol_assumption_report}\\.\$" \
		proofs/ssprove/PqxdhRatchetGames.v \
		"SSProve protocol ${protocol_assumption_report} assumption report"
done
require_line_count 1 '^Lemma pqxdh_ratchet_game_uses_production_kdf_domains :' \
	proofs/ssprove/PqxdhRatchetGames.v \
	"SSProve closed-game exact KDF-use theorem"
require_line_count 1 '^Print Assumptions pqxdh_ratchet_game_uses_production_kdf_domains\.$' \
	proofs/ssprove/PqxdhRatchetGames.v \
	"SSProve closed-game exact KDF-use assumption report"
require_line_count 2 '^  let root := ideal_pqxdh_root tape PqxdhRootDerivation input in$' \
	proofs/ssprove/PqxdhRatchetGames.v \
	"SSProve closed-game root exact KDF use"
require_line_count 1 '^  let output := ideal_symmetric_hkdf tape InitialRatchetExpansion root in$' \
	proofs/ssprove/PqxdhRatchetGames.v \
	"SSProve closed-game initial exact KDF use"
require_line_count 1 '^  let output := ideal_symmetric_hkdf tape RatchetStepExpansion chain in$' \
	proofs/ssprove/PqxdhRatchetGames.v \
	"SSProve closed-game step exact KDF use"
for composition_capstone in \
	complementary_role_orientation \
	separated_ckey_transfer_is_one_way_and_role_oriented \
	separated_first_response_matches_monolithic \
	separated_unauthenticated_response_rejects \
	public_response_rejects_unauthenticated_provenance \
	unauthenticated_public_responses_are_challenge_independent \
	pure_public_response_observation_matches_monolithic \
	separated_first_response_opens_sequence_one \
	state_separated_composition_uses_production_kdf_domains \
	failed_response_construction_consumes_only_replay_state \
	dropped_response_has_asymmetric_publication \
	accepted_response_has_complementary_live_counters \
	rejected_response_terminally_aborts_beacon \
	component_locations_are_state_separated \
	pure_single_run_body_matches_monolithic; do
	require_line_count 1 "^(Theorem|Lemma) ${composition_capstone} :" \
		proofs/ssprove/StateSeparatedComposition.v \
		"SSProve state-separation ${composition_capstone} capstone"
	require_line_count 1 \
		"^Print Assumptions ${composition_capstone}\\.\$" \
		proofs/ssprove/StateSeparatedComposition.v \
		"SSProve state-separation ${composition_capstone} assumption report"
done
require_line_count 15 '^Print Assumptions ' \
	proofs/ssprove/StateSeparatedComposition.v \
	"complete SSProve state-separation assumption reports"
require_line_count 1 '^Definition consuming_ckey :' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve consuming private CKEY package"
require_line_count 1 '^#\[tactic=notac\] Equations\? composition_core$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve state-separated linked core"
require_line_count 1 '^#\[tactic=notac\] Equations\? state_separated_response_package$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve state-separated public package"
require_line_count 1 '^Definition public_response_observation : Type := option bool\.$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve optional public response observation"
require_line_count 1 '^Definition chPublicResponseObservation : choice_type := chOption chBool\.$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve optional package response observation"
require_line_count 1 '^Definition uniform_response_sample_op : Op :=$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve private joint response sampler"
require_line_count 1 '^  existT _ chRomSample uniform_rom_sample\.$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve exact pure/package sample source"
require_line_count 1 "^    #val #\\[run_response_id\\] : 'unit → 'response$" \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve unit-input public response signature"
require_occurrence_count 3 \
	"#def #\\[run_response_id\\] \\(_ : 'unit\\) : 'response \\{" \
	"SSProve unit-input response implementations" \
	proofs/ssprove/StateSeparatedComposition.v
require_occurrence_count 2 'sample <\$ uniform_response_sample_op ;;' \
	"SSProve internal joint sample draws" \
	proofs/ssprove/StateSeparatedComposition.v
require_line_count 1 '^      opened_plaintext ← OPEN \(sample, ciphertext\) ;;$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve internal-only opened response"
require_line_count 1 "^      @ret 'response \\(Some ciphertext\\)$" \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve successful public ciphertext observation"
require_line_count 1 "^      @ret 'response None$" \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve explicit public rejection observation"
require_line_count 1 '^Definition state_separated_response_games$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve challenge-indexed public game pair"
require_line_count 1 '^  loc_GamePair response_interface :=$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve public game-pair interface"
require_line_count 1 '^  fun challenge =>$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve hidden challenge world mapping"
require_line_count 1 '^Definition state_separated_public_response_view_game$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve direct public-response view game"
require_line_count 1 '^Definition state_separated_public_response_advantage$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve direct public-response advantage"
require_occurrence_count 1 '\\P_\[uniform_rom_sample\]' \
	"SSProve direct view uses joint finite source" \
	proofs/ssprove/StateSeparatedComposition.v
require_line_count 1 '^Definition composition_driver \(authenticated : bool\) :$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve provenance-indexed response driver"
require_line_count 1 '^  if authenticated$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve response driver provenance branch"
require_line_count 1 '^  then successful_composition_driver$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve authenticated response driver"
require_line_count 1 '^  else rejected_composition_driver\.$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve rejected-provenance driver"
require_line_count 1 '^Definition first_response_sequence : nat := 1%N\.$' \
	proofs/ssprove/StateSeparatedComposition.v \
	"SSProve production first-response sequence"
require_occurrence_count 2 \
	'#assert \(payload_authenticated (?:server|beacon) == true\)' \
	"SSProve authenticated-provenance enforcement" \
	proofs/ssprove/StateSeparatedComposition.v
for package_semantics_capstone in \
	authenticated_package_run_normalizes \
	rejected_package_run_normalizes \
	package_public_response_observation_matches_direct \
	state_separated_package_response_view_matches_direct \
	state_separated_package_response_advantage_matches_direct; do
	require_line_count 1 "^Theorem ${package_semantics_capstone} :" \
		proofs/ssprove/StateSeparatedPackageSemantics.v \
		"SSProve package-semantics ${package_semantics_capstone} capstone"
	require_line_count 1 \
		"^Print Assumptions ${package_semantics_capstone}\\.\$" \
		proofs/ssprove/StateSeparatedPackageSemantics.v \
		"SSProve package-semantics ${package_semantics_capstone} assumption report"
done
require_line_count 5 '^Print Assumptions ' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"complete SSProve package-semantics assumption reports"
require_line_count 1 '^Fixpoint run_response_code_with_sample$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve restricted response-code evaluator"
require_line_count 1 '^Definition authenticated_linked_response_code$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve projected authenticated linked RUN"
require_line_count 1 '^Definition rejected_linked_response_code :$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve projected rejected linked RUN"
require_line_count 1 '^Local Lemma authenticated_linked_response_code_has_normal_form :$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve authenticated linked RUN bridge"
require_line_count 1 '^Local Lemma rejected_linked_response_code_has_normal_form :$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve rejected linked RUN bridge"
require_line_count 1 '^Local Lemma authenticated_linked_response_code_is_checked_run :$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve authenticated raw projection bridge"
require_line_count 1 '^Local Lemma rejected_linked_response_code_is_checked_run :$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve rejected raw projection bridge"
require_line_count 1 '^Record response_run_certificate$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve indexed response-run certificate"
require_line_count 1 '^  \(execution : option \(public_response_observation \* heap\)\) := \{$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve full-execution certificate index"
require_line_count 1 '^  certified_response_run : option \(public_response_observation \* heap\);$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve full-execution certificate witness"
require_line_count 1 '^  response_run_certificate_sound : execution = certified_response_run$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve exact response-run certificate soundness field"
require_line_count 1 '^Definition authenticated_package_run_certificate$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve authenticated package-run certificate"
require_line_count 1 '^Definition rejected_package_run_certificate$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve rejected package-run certificate"
require_line_count 2 '^Defined\.$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"transparent SSProve package-run certificates"
require_occurrence_count 1 \
	'response_run_certificate\n    \(run_response_code_with_sample sample\n      \(authenticated_linked_response_code session challenge input\)\n      empty_heap\)\.' \
	"SSProve authenticated certificate exact raw-execution index" \
	proofs/ssprove/StateSeparatedPackageSemantics.v
require_occurrence_count 1 \
	'response_run_certificate\n    \(run_response_code_with_sample sample\n      rejected_linked_response_code empty_heap\)\.' \
	"SSProve rejected certificate exact raw-execution index" \
	proofs/ssprove/StateSeparatedPackageSemantics.v
require_line_count 1 '^         authenticated_package_execution_normal_form$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve authenticated certificate full-heap witness"
require_line_count 1 '^         rejected_package_execution_normal_form \|}\.$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve rejected certificate full-heap witness"
require_line_count 1 '^  apply authenticated_linked_response_code_has_normal_form\.$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve authenticated certificate soundness proof"
require_line_count 1 '^  apply \(rejected_linked_response_code_has_normal_form$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve rejected certificate soundness proof"
require_line_count 1 '^Definition authenticated_package_run_normal_form$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve authenticated proof-erased normal form"
require_line_count 1 '^Definition rejected_package_run_normal_form$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve rejected proof-erased normal form"
require_line_count 2 '^    @certified_response_run _$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve proof-erased certificate projections"
require_line_count 1 '^      \(authenticated_package_run_certificate$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve authenticated normal-form certificate source"
require_line_count 1 '^      \(rejected_package_run_certificate$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve rejected normal-form certificate source"
require_line_count 1 '^Definition package_public_response_observation$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve package-semantics public observation"
require_line_count 1 '^Definition state_separated_package_response_view_game$' \
	proofs/ssprove/StateSeparatedPackageSemantics.v \
	"SSProve package-semantics finite view"
require_occurrence_count 1 '\\P_\[uniform_rom_sample\]' \
	"SSProve package-semantics view uses joint finite source" \
	proofs/ssprove/StateSeparatedPackageSemantics.v
indexed_sessions=proofs/ssprove/StateSeparatedIndexedSessions.v
for indexed_session_capstone in \
	indexed_role_session_locations_are_distinct \
	indexed_cache_location_is_disjoint \
	indexed_first_session_heap_summary \
	indexed_both_sessions_heap_summary \
	indexed_response_matches_monolithic \
	indexed_package_trace_matches_reference \
	indexed_package_context_matches_reference \
	indexed_same_handle_trace_normalizes \
	indexed_rejected_trace_is_neutral \
	indexed_fresh_trace_underflow_is_explicit \
	indexed_distinct_handle_trace_normalizes \
	indexed_reverse_handle_trace_normalizes \
	indexed_both_orders_have_same_private_summary \
	indexed_session_handle_is_ghost \
	indexed_sessions_use_production_kdf_domains \
	indexed_package_context_single_sample_is_total \
	indexed_public_context_view_matches_reference \
	indexed_public_context_game_matches_reference; do
	require_line_count 1 "^(Theorem|Lemma) ${indexed_session_capstone} :" \
		"$indexed_sessions" \
		"SSProve indexed-session ${indexed_session_capstone} capstone"
	require_line_count 1 \
		"^Print Assumptions ${indexed_session_capstone}\\.\$" \
		"$indexed_sessions" \
		"SSProve indexed-session ${indexed_session_capstone} assumption report"
done
require_line_count 18 '^Print Assumptions ' "$indexed_sessions" \
	"complete SSProve indexed-session assumption reports"

require_line_count 1 '^Definition indexed_consuming_ckey :' \
	"$indexed_sessions" \
	"SSProve indexed-session consuming private CKEY package"
require_line_count 1 '^#\[tactic=notac\] Equations\? indexed_composition_core$' \
	"$indexed_sessions" \
	"SSProve indexed-session linked core"
require_line_count 1 \
	'^#\[tactic=notac\] Equations\? indexed_state_separated_response_package$' \
	"$indexed_sessions" \
	"SSProve indexed-session linked public package"
require_occurrence_count 1 \
	'Definition indexed_ckey_locs : \{fset Location\} :=\n  fset \[:: server_ckey_loc; beacon_ckey_loc;\n    server_session_one_loc; beacon_session_one_loc\]\.' \
	"SSProve indexed-session four private CKEY slots" "$indexed_sessions"
require_line_count 1 \
	'^Definition chCachedRomSample : choice_type := chOption chRomSample\.$' \
	"$indexed_sessions" \
	"SSProve indexed-session optional global ROM cache type"
require_line_count 1 \
	'^Definition indexed_rom_cache_loc : Location := \(chCachedRomSample; 84%N\)\.$' \
	"$indexed_sessions" \
	"SSProve indexed-session global ROM cache location"
require_occurrence_count 1 \
	'Definition indexed_cache_locs : \{fset Location\} :=\n  fset \[:: indexed_rom_cache_loc\]\.' \
	"SSProve indexed-session singleton global ROM cache" "$indexed_sessions"
require_line_count 1 \
	"^    #val #\\[indexed_run_response_id\\] : 'bool → 'response\$" \
	"$indexed_sessions" \
	"SSProve indexed-session Boolean RUN signature"
require_line_count 1 \
	"^    #def #\\[indexed_run_response_id\\] \\(session : 'bool\\) : 'response \\{\$" \
	"$indexed_sessions" \
	"SSProve indexed-session Boolean RUN implementation"
require_line_count 1 '^          cached ← get indexed_rom_cache_loc ;;$' \
	"$indexed_sessions" \
	"SSProve indexed-session sole global ROM cache read"
require_line_count 1 \
	'^              #put indexed_rom_cache_loc := Some sample ;;$' \
	"$indexed_sessions" \
	"SSProve indexed-session sole global ROM cache fill"
require_occurrence_count 1 'sample <\$ uniform_response_sample_op ;;' \
	"SSProve indexed-session sole global ROM sample operation" \
	"$indexed_sessions"
require_occurrence_count 1 \
	'if select_session session authentications then[\s\S]{0,2400}?cached ← get indexed_rom_cache_loc ;;[\s\S]{0,800}?sample <\$ uniform_response_sample_op ;;' \
	"SSProve indexed-session authentication precedes cache and sampling" \
	"$indexed_sessions"

require_line_count 1 '^Fixpoint run_response_code_with_samples$' \
	"$indexed_sessions" \
	"SSProve indexed-session sample-stream evaluator"
require_occurrence_count 1 \
	'Inductive indexed_reference_state : Type :=\n\| IndexedReferenceFresh\n\| IndexedReferenceOneUsed\n    \(first_session : bounded_session_handle\) \(sample : rom_sample\)\n\| IndexedReferenceBothUsed\n    \(first_session : bounded_session_handle\) \(sample : rom_sample\)\.' \
	"SSProve indexed-session bounded reference state" "$indexed_sessions"
require_line_count 1 '^Definition indexed_reference_step$' \
	"$indexed_sessions" \
	"SSProve indexed-session reference transition"
require_line_count 1 '^Fixpoint run_indexed_reference_trace$' \
	"$indexed_sessions" \
	"SSProve indexed-session reference trace"
require_line_count 1 '^Local Fixpoint run_indexed_package_trace$' \
	"$indexed_sessions" \
	"SSProve indexed-session package trace"
require_occurrence_count 1 \
	'Inductive indexed_public_context : Type :=\n\| IndexedContextReturn \(result : bool\)\n\| IndexedContextCall\n    \(session : bounded_session_handle\)\n    \(continuation : public_response_observation -> indexed_public_context\)\.' \
	"SSProve indexed-session adaptive public context" "$indexed_sessions"
require_line_count 1 '^Fixpoint run_indexed_reference_context$' \
	"$indexed_sessions" \
	"SSProve indexed-session reference context"
require_line_count 1 '^Local Fixpoint run_indexed_package_context$' \
	"$indexed_sessions" \
	"SSProve indexed-session package context"
require_line_count 1 '^Local Lemma checked_indexed_trace_matches_reference :' \
	"$indexed_sessions" \
	"SSProve indexed-session checked trace bridge"
require_line_count 1 '^Local Lemma checked_indexed_context_matches_reference :' \
	"$indexed_sessions" \
	"SSProve indexed-session checked context bridge"
require_line_count 1 '^Record indexed_trace_run_certificate$' \
	"$indexed_sessions" \
	"SSProve indexed-session trace certificate"
require_line_count 1 '^  indexed_trace_run_certificate_sound :$' \
	"$indexed_sessions" \
	"SSProve indexed-session exact trace certificate soundness field"
require_occurrence_count 1 \
	'indexed_trace_run_certificate\n      \(run_indexed_package_trace\n        authentications challenges inputs requests samples empty_heap\)\.' \
	"SSProve indexed-session certificate exact raw-trace index" \
	"$indexed_sessions"
require_line_count 1 '^Record indexed_context_run_certificate$' \
	"$indexed_sessions" \
	"SSProve indexed-session context certificate"
require_line_count 1 '^  indexed_context_run_certificate_sound :$' \
	"$indexed_sessions" \
	"SSProve indexed-session exact context certificate soundness field"
require_occurrence_count 1 \
	'indexed_context_run_certificate\n      \(run_indexed_package_context\n        authentications challenges inputs context samples empty_heap\)\.' \
	"SSProve indexed-session certificate exact raw-context index" \
	"$indexed_sessions"
require_line_count 2 '^Defined\.$' "$indexed_sessions" \
	"transparent SSProve indexed-session certificates"

require_occurrence_count 1 \
	'authentications challenges inputs \[:: session; session\] \[:: sample\] =\n    Some\n      \(\[:: indexed_reference_ciphertext\n             challenges inputs session sample; None\],\n       indexed_first_session_heap session sample,\n       \[::\]\)\.' \
	"SSProve indexed-session fixed same-handle trace result" \
	"$indexed_sessions"
require_occurrence_count 1 \
	'authentications challenges inputs \[:: session\] samples =\n    Some \(\[:: None\], empty_heap, samples\)\.' \
	"SSProve indexed-session fixed rejected trace result" \
	"$indexed_sessions"
require_occurrence_count 1 \
	'authentications challenges inputs \[:: session\] \[::\] = None\.' \
	"SSProve indexed-session fixed sampler-underflow trace result" \
	"$indexed_sessions"
require_occurrence_count 1 \
	'\[:: first_session; negb first_session\] \[:: sample\] =\n    Some\n      \(\[:: indexed_reference_ciphertext\n             challenges inputs first_session sample;\n           indexed_reference_ciphertext\n             challenges inputs \(negb first_session\) sample\],\n       indexed_both_sessions_heap first_session sample,\n       \[::\]\)\.' \
	"SSProve indexed-session fixed distinct-handle trace result" \
	"$indexed_sessions"
require_occurrence_count 1 \
	'\[:: negb first_session; first_session\] \[:: sample\] =\n    Some\n      \(\[:: indexed_reference_ciphertext\n             challenges inputs \(negb first_session\) sample;\n           indexed_reference_ciphertext\n             challenges inputs first_session sample\],\n       indexed_both_sessions_heap \(negb first_session\) sample,\n       \[::\]\)\.' \
	"SSProve indexed-session fixed reverse-handle trace result" \
	"$indexed_sessions"

require_line_count 1 '^Theorem indexed_package_context_single_sample_is_total :' \
	"$indexed_sessions" \
	"SSProve indexed-session adaptive singleton-sample totality"
require_line_count 1 '^Definition indexed_package_public_context_game$' \
	"$indexed_sessions" \
	"SSProve indexed-session adaptive package game"
require_line_count 1 '^Definition indexed_reference_public_context_game$' \
	"$indexed_sessions" \
	"SSProve indexed-session adaptive reference game"
require_occurrence_count 2 '\\P_\[uniform_rom_sample\]' \
	"SSProve indexed-session adaptive games use the same finite source" \
	"$indexed_sessions"
require_occurrence_count 1 \
	'Theorem indexed_sessions_use_production_kdf_domains :\n  kdf_use_info PqxdhRootDerivation = pqxdh_info /\\\n  kdf_use_info InitialRatchetExpansion = symmetric_ratchet_info /\\\n  kdf_use_info RatchetStepExpansion = symmetric_ratchet_info /\\\n  kdf_use_info InitialRatchetExpansion =\n    kdf_use_info RatchetStepExpansion /\\\n  kdf_output_size PqxdhRootDerivation = 32%N /\\\n  kdf_output_size InitialRatchetExpansion = 64%N /\\\n  kdf_output_size RatchetStepExpansion = 76%N\.' \
	"SSProve indexed-session exact production KDF-domain theorem" \
	"$indexed_sessions"
for protocol_rom_capstone in \
	pqxdh_ratchet_bounded_rom_confidentiality_bound \
	active_classical_forward_bounded_rom_confidentiality \
	passive_classical_forward_bounded_rom_confidentiality \
	passive_quantum_classical_query_forward_confidentiality \
	active_classical_replace_fixed_failure_confidentiality \
	active_classical_all_actions_bounded_rom_confidentiality; do
	require_line_count 1 "^  Theorem ${protocol_rom_capstone}\$" \
		proofs/ssprove/PqxdhRatchetRom.v \
		"SSProve protocol-ROM ${protocol_rom_capstone} capstone"
	require_line_count 1 \
		"^Print Assumptions ${protocol_rom_capstone}\\.\$" \
		proofs/ssprove/PqxdhRatchetRom.v \
		"SSProve protocol-ROM ${protocol_rom_capstone} assumption report"
done
require_line_count 1 '^  Lemma protocol_supported_scenario_root_hidden$' \
	proofs/ssprove/PqxdhRatchetRom.v \
	"SSProve supported-scenario hidden-root bridge"
require_line_count 1 '^Print Assumptions protocol_supported_scenario_root_hidden\.$' \
	proofs/ssprove/PqxdhRatchetRom.v \
	"SSProve supported-scenario bridge assumption report"
for hybrid_capstone in \
	pqxdh_hybrid_one_hidden_contribution_confidentiality \
	active_classical_forward_hybrid_confidentiality \
	passive_classical_forward_hybrid_confidentiality \
	passive_quantum_forward_hybrid_confidentiality; do
	require_line_count 1 "^  Theorem ${hybrid_capstone}\$" \
		proofs/ssprove/PqxdhHybridSecurity.v \
		"SSProve hybrid ${hybrid_capstone} capstone"
	require_line_count 1 \
		"^Print Assumptions ${hybrid_capstone}\\.\$" \
		proofs/ssprove/PqxdhHybridSecurity.v \
		"SSProve hybrid ${hybrid_capstone} assumption report"
done
require_line_count 1 '^Lemma pqxdh_hybrid_domains_are_separated$' \
	proofs/ssprove/PqxdhHybridSecurity.v \
	"SSProve hybrid domain-separation theorem"
require_line_count 1 '^Lemma active_quantum_replace_has_no_hidden_hybrid_component$' \
	proofs/ssprove/PqxdhHybridSecurity.v \
	"SSProve active-quantum hybrid failure classification"
require_line_count 1 '^Print Assumptions active_quantum_replace_has_no_hidden_hybrid_component\.$' \
	proofs/ssprove/PqxdhHybridSecurity.v \
	"SSProve active-quantum hybrid classification assumption report"
for ratchet_capstone in \
	ratchet_erasure_forward_secrecy_bad_query_bound \
	ratchet_attacker_trace_query_count_bound; do
	require_line_count 1 "^  Theorem ${ratchet_capstone}\$" \
		proofs/ssprove/RatchetForwardSecrecy.v \
		"SSProve ratchet ${ratchet_capstone} capstone"
	require_line_count 1 \
		"^Print Assumptions ${ratchet_capstone}\\.\$" \
		proofs/ssprove/RatchetForwardSecrecy.v \
		"SSProve ratchet ${ratchet_capstone} assumption report"
done
require_line_count 1 '^Theorem ratchet_other_domain_separation$' \
	proofs/ssprove/RatchetForwardSecrecy.v \
	"SSProve ratchet domain-separation theorem"
for integrity_capstone in \
	record_active_modification_query_or_guess_classification_bound \
	record_fresh_input_integrity_probability_is_fresh_guess \
	record_cross_context_reuse_reduces_to_collision \
	record_cross_sequence_reuse_reduces_to_collision \
	record_integrity_trace_size_bound; do
	require_line_count 1 "^Theorem ${integrity_capstone}\$" \
		proofs/ssprove/RecordIntegrity.v \
		"SSProve record ${integrity_capstone} capstone"
	require_line_count 1 \
		"^Print Assumptions ${integrity_capstone}\\.\$" \
		proofs/ssprove/RecordIntegrity.v \
		"SSProve record ${integrity_capstone} assumption report"
done
for integrity_bound_capstone in \
	record_runs_agree_after_unqueried_flip \
	record_bound_table_flip_involutive \
	record_bound_flip_toggles_success \
	record_uniform_one_bit_fresh_tag_guess_bound; do
	require_line_count 1 \
		"^Print Assumptions ${integrity_bound_capstone}\\.\$" \
		proofs/ssprove/RecordIntegrityBound.v \
		"SSProve record-bound ${integrity_bound_capstone} assumption report"
done
require_line_count 1 '^  Theorem record_uniform_one_bit_fresh_tag_guess_bound :$' \
	proofs/ssprove/RecordIntegrityBound.v \
	"SSProve one-bit fresh-tag numerical bound"
reject_matches "SSProve proof bypass or unsafe hax prelude" \
	'(?i:\badmit(?:ted)?\b)|\b(?:Axiom|Conjecture|Parameters?|Abort)\b|__admitted__|falso|(?:exact|vm_cast|native_cast)_no_check|\bHacspec\b|Hacspec_|Beaconcrypt_core_|(?:Unset[[:space:]]+(?:Guard|Positivity|Universe)[[:space:]]+Checking|Set[[:space:]]+(?:Type[[:space:]]+in[[:space:]]+Type|Impredicative[[:space:]]+Set))' \
	proofs/ssprove --glob '*.v'

# Both invalid sequence-three attempts and the compromise handoff carry the exact same symbolic entry-state term.
# No rejection-created cache is constructed or disclosed.
require_occurrence_count 2 \
	'event\s+Receive(?:RejectedNeutral|RejectionRetried)\(\s*session,\s*target_sequence,\s*forged_target_frame,\s*ready_state\s*\)' \
	"state-neutral repeated rejection state" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'out\(\s*receive_snapshots,\s*\(\s*session,\s*target_sequence,\s*ready_state,\s*ready_state,\s*chain_2,\s*empty_cache,' \
	"state-neutral compromise handoff" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'let\s+receive_cache_empty\(\)\s*=\s*live_cache\s+in' \
	"unchanged empty-cache compromise state" \
	proofs/pro-verif/environment.pvl
reject_matches "obsolete failed-receive advancement vocabulary remains" \
	'(FailedReceive(?:StateAdvanced|CacheFilled|CapacityRejected|RetryRetained|Accepted|KeyConsumed|HonestDelivery|ReplayRejected|AfterCapacityReleaseAdmitted|StateCompromised)|FAILED_(?:PAST|SKIPPED|TARGET|FUTURE)_SECRET|failed_receive_(?:cache|state|snapshots))' \
	proofs/pro-verif --glob '*.pv' --glob '*.pvl' --glob '*.awk'

# The exact maximum-gap success publishes sequences two through 51 and retains 50 skipped entries.
# Both successful targets stay out of the cache.
require_line_count 50 \
	'^  event MessageKeyCached\($' \
	proofs/pro-verif/environment.pvl \
	"maximum-gap skipped-key cache event"
require_line_count 50 \
	'^[[:space:]]+let capacity_cache_[0-9]+ = receive_cache_entry\(' \
	proofs/pro-verif/environment.pvl \
	"maximum-gap skipped cache entry"
for skipped_sequence in {2..51}; do
	require_occurrence_count 1 \
		'event\s+MessageKeyCached\(\s*capacity_session,\s*beacon_role\(\),\s*server_to_beacon\(\),\s*capacity_sequence_'"${skipped_sequence}"',\s*capacity_material_'"${skipped_sequence}"'\s*\)' \
		"maximum-gap skipped-key cache event for sequence ${skipped_sequence}" \
		proofs/pro-verif/environment.pvl
	require_line_count 1 \
		"^[[:space:]]+let capacity_cache_${skipped_sequence} = receive_cache_entry\\(" \
		proofs/pro-verif/environment.pvl \
		"maximum-gap skipped sequence ${skipped_sequence}"
done
require_occurrence_count 1 \
	'let\s+committed_cache\s*=\s*receive_cache_entry\(\s*skipped_sequence,\s*skipped_material,\s*empty_cache\s*\)' \
	"successful future skipped-key publication" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'let\s+committed_state\s*=\s*receive_state\(\s*target_sequence,\s*chain_4,\s*committed_cache\s*\)' \
	"successful future target consumption state" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'let\s+maximum_gap_state\s*=\s*receive_state\(\s*capacity_sequence_52,\s*capacity_chain_53,\s*capacity_cache_51\s*\)' \
	"successful maximum-gap 50-entry state" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'event\s+ReceiveCapacityRejected\(\s*capacity_session,\s*capacity_sequence_54,\s*capacity_rejected_frame,\s*maximum_gap_state\s*\)' \
	"state-neutral capacity rejection" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'let\s+released_state\s*=\s*receive_state\(\s*capacity_sequence_52,\s*capacity_chain_53,\s*capacity_cache_50\s*\)' \
	"cached success releases one capacity slot" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'let\s+after_release_cache\s*=\s*receive_cache_entry\(\s*capacity_sequence_53,\s*capacity_material_53,\s*capacity_cache_50\s*\)' \
	"post-release future skipped-key publication" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'let\s+after_release_state\s*=\s*receive_state\(\s*capacity_sequence_54,\s*capacity_chain_55,\s*after_release_cache\s*\)' \
	"post-release future target consumption state" \
	proofs/pro-verif/environment.pvl
reject_matches "successful receive target remains cached" \
	'receive_cache_entry\(\s*(?:target_sequence|capacity_sequence_(?:52|54))\b' \
	proofs/pro-verif/environment.pvl

# Current production uses first-order, affine effect phases.
# The old callback-bearing helpers remain test-only and must not enter the no-exclusion Lean extraction.
for phase_type in \
	ConcreteRatchetKernel \
	SendStart \
	SendKdf \
	SendSeal \
	ReceiveEffect \
	ReceiveKdf \
	ReceiveOpen \
	ConcreteRatchetRestore; do
	require_line_count 1 \
		"^pub (enum|struct) ${phase_type}([<{[:space:]]|$)" \
		src/ratchet/concrete.rs \
		"production affine ratchet phase ${phase_type}"
done
for phase_type in InitialRatchetKdfPending InitialRatchetKdfResponse; do
	require_line_count 1 \
		"^pub struct ${phase_type}([<{[:space:]]|$)" \
		src/pqxdh/concrete.rs \
		"production affine initial-KDF phase ${phase_type}"
done

affine_phase_pattern='(?:ConcreteRatchetKernel|SendStart|SendKdf|SendSeal|ReceiveEffect|ReceiveKdf|ReceiveOpen|ConcreteRatchetRestore|InitialRatchetKdfPending|InitialRatchetKdfResponse)'
reject_matches "affine effect phase became Clone or Copy" \
	'#\[derive\([^]]*\b(?:Clone|Copy)\b[^]]*\)\]\s*(?:(?:#\[[^]]*\]|//[^\n]*|/\*[\s\S]*?\*/)\s*)*(?:pub(?:\([^)]*\))?\s+)?(?:enum|struct)\s+'"${affine_phase_pattern}"'\b' \
	src/ratchet/concrete.rs src/pqxdh/concrete.rs
reject_matches "affine effect phase gained conditional Clone or Copy derive" \
	'#\[cfg_attr\([^]]*\bderive\s*\([^)]*\b(?:Clone|Copy)\b[^)]*\)[^]]*\)\]\s*(?:(?:#\[[^]]*\]|//[^\n]*|/\*[\s\S]*?\*/)\s*)*(?:pub(?:\([^)]*\))?\s+)?(?:enum|struct)\s+'"${affine_phase_pattern}"'\b' \
	src/ratchet/concrete.rs src/pqxdh/concrete.rs
reject_matches "affine effect phase gained explicit Clone or Copy implementation" \
	'impl(?:\s*<[\s\S]{0,500}?>)?\s+(?:[A-Za-z_][A-Za-z0-9_]*::)*(?:Clone|Copy)\s+for\s+'"${affine_phase_pattern}"'\b' \
	src/ratchet/concrete.rs src/pqxdh/concrete.rs
reject_matches "production effect module stores a function pointer" \
	':\s*(?:fn\s*\(|(?:dyn|impl)\s+Fn(?:Mut|Once)?\b)' \
	src/ratchet/concrete.rs src/pqxdh/concrete.rs

for pending_type in PreparedReceive PreparedCachedReceive PreparedFutureTarget PendingReceive; do
	require_line_count 1 \
		"^(pub\\(super\\) )?(enum|struct) ${pending_type}([[:space:]<{]|$)" \
		src/ratchet/refined.rs \
		"private pending receive type ${pending_type}"
done
reject_matches "private pending receive capability became Clone or Copy" \
	'#\[derive\([^]]*\b(?:Clone|Copy)\b[^]]*\)\]\s*(?:(?:#\[[^]]*\]|//[^\n]*|/\*[\s\S]*?\*/)\s*)*(?:pub(?:\([^)]*\))?\s+)?(?:enum\s+PreparedReceive|struct\s+(?:PreparedCachedReceive|PreparedFutureTarget|PendingReceive))' \
	src/ratchet/refined.rs
reject_matches "private pending receive capability gained conditional Clone or Copy derive" \
	'#\[cfg_attr\([^]]*\bderive\s*\([^)]*\b(?:Clone|Copy)\b[^)]*\)[^]]*\)\]\s*(?:(?:#\[[^]]*\]|//[^\n]*|/\*[\s\S]*?\*/)\s*)*(?:pub(?:\([^)]*\))?\s+)?(?:enum\s+PreparedReceive|struct\s+(?:PreparedCachedReceive|PreparedFutureTarget|PendingReceive))' \
	src/ratchet/refined.rs
reject_matches "private pending receive capability gained explicit Clone or Copy implementation" \
	'impl(?:\s*<[\s\S]{0,500}?>)?\s+(?:[A-Za-z_][A-Za-z0-9_]*::)*(?:Clone|Copy)\s+for\s+(?:PreparedReceive|PreparedCachedReceive|PreparedFutureTarget|PendingReceive)\b' \
	src/ratchet/refined.rs

for callback_helper in \
	refined_advance_send \
	refined_seal_next \
	refined_advance_receive \
	prepare_future_receive_steps \
	prepare_receive \
	refined_execute_receive_steps \
	refined_advance_receive_until \
	refined_finish_receive \
	refined_open_and_finish; do
	require_occurrence_count 1 \
		"#\\[cfg\\(test\\)\\][\\s\\S]{0,1200}?fn\\s+${callback_helper}\\b" \
		"callback helper remains test-only: ${callback_helper}" \
		src/ratchet/refined.rs
	reject_matches "test-only callback helper entered Lean extraction: ${callback_helper}" \
		"^def ratchet\\.refined\\.${callback_helper}( |$)" \
		proofs/lean/BeaconcryptCore/Extraction/Funs.lean
done

# The canonical Lean extraction command has no Charon module exclusions and therefore covers both concrete effect modules.
reject_matches "Lean extraction reintroduced a module exclusion" \
	'(?:--exclude(?:[=[:space:]]|$)|LEAN_CHARON_ARGS)' Makefile
require_occurrence_count 1 \
	"cargo\\s+hax\\s+-C\\s+--locked\\s+';'\\s+into\\s+lean" \
	"canonical no-exclusion Lean extraction command" Makefile

lean_types=proofs/lean/BeaconcryptCore/Extraction/Types.lean
for lean_structure in \
	pqxdh.concrete.InitialRatchetKdfPending \
	pqxdh.concrete.InitialRatchetKdfResponse \
	ratchet.SymmetricRatchetKdfRequest \
	ratchet.RatchetKdfResponse \
	ratchet.RatchetKdfOutput \
	ratchet.concrete.ConcreteRatchetKernel \
	ratchet.concrete.SendKdf \
	ratchet.concrete.SendSeal \
	ratchet.concrete.ReceiveKdf \
	ratchet.concrete.ReceiveOpen \
	ratchet.concrete.ConcreteRatchetRestore; do
	require_line_count 1 "^structure ${lean_structure//./\\.}( |$)" \
		"$lean_types" "generated Lean effect structure ${lean_structure}"
done
for lean_inductive in \
	ratchet.concrete.SendStart \
	ratchet.concrete.ReceiveEffect; do
	require_line_count 1 "^inductive ${lean_inductive//./\\.}( |$)" \
		"$lean_types" "generated Lean effect phase ${lean_inductive}"
done

lean_funs=proofs/lean/BeaconcryptCore/Extraction/Funs.lean
for lean_definition in \
	pqxdh.concrete.start_initial_ratchet_kdf \
	pqxdh.concrete.resume_initial_ratchet_kdf \
	pqxdh.concrete.start_beacon_ratchet_kdf \
	pqxdh.concrete.start_server_ratchet_kdf \
	pqxdh.concrete.start_beacon_candidate_ratchet_kdf \
	pqxdh.concrete.start_server_candidate_ratchet_kdf \
	ratchet.concrete.ratchet_step_from_response \
	ratchet.concrete.begin_send \
	ratchet.concrete.SendKdf.impl.request \
	ratchet.concrete.SendKdf.cancel \
	ratchet.concrete.SendKdf.resume \
	ratchet.concrete.SendSeal.finish \
	ratchet.concrete.begin_receive \
	ratchet.concrete.ReceiveKdf.impl.request \
	ratchet.concrete.ReceiveKdf.cancel \
	ratchet.concrete.ReceiveKdf.resume \
	ratchet.concrete.ReceiveOpen.reject \
	ratchet.concrete.ReceiveOpen.finish \
	ratchet.control.advance_receive_target \
	ratchet.concrete.start_concrete_restore \
	ratchet.concrete.concrete_restore_receive_key \
	ratchet.concrete.finish_concrete_restore; do
	require_line_count 1 "^def ${lean_definition//./\\.}( |$)" \
		"$lean_funs" "generated Lean effect definition ${lean_definition}"
done
reject_matches "predecessor executor/callback symbol remains in current Lean extraction" \
	'ConcreteRatchetChain|derive_ratchet_step|concrete_(?:seal_next|open_and_finish)' \
	"$lean_types" "$lean_funs"

sed -n '/^import Aeneas$/,$p' \
	proofs/lean/BeaconcryptCore/Extraction/FunsExternal_Template.lean |
	sed '/^[[:space:]]*$/d' > "$tmp_dir/generated-lean-externals"
sed -n '/^import Aeneas$/,$p' \
	proofs/lean/BeaconcryptCore/Assumptions/FunsExternal.lean |
	sed '/^[[:space:]]*$/d' > "$tmp_dir/maintained-lean-externals"
cmp -s "$tmp_dir/generated-lean-externals" "$tmp_dir/maintained-lean-externals" ||
	fail "maintained Lean externals differ from the reviewed generated template"
require_line_count 1 '^import BeaconcryptCore\.Assumptions\.FunsExternal$' \
	proofs/lean/BeaconcryptCore/Extraction/FunsExternal.lean \
	"generated Lean assumptions forwarding import"
mapfile -t handwritten_lean < <(
	awk -F '\t' '$1 == "handwritten-lean" { print $3 }' "$manifest"
)
reject_matches "handwritten Lean contains an unproved escape hatch" \
	'\b(?:sorry|admit|axiom)\b|sorryAx' "${handwritten_lean[@]}"

lean_root=proofs/lean/BeaconcryptCore.lean
require_line_count 1 '^import BeaconcryptCore\.Refinement\.RatchetControlRestore$' \
	"$lean_root" \
	"canonical control/restoration proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Refinement\.RatchetEffectRefinement$' \
	"$lean_root" \
	"canonical phase-refinement proof import"
require_line_count 1 '^import BeaconcryptCore\.Refinement\.PqxdhSession$' \
	"$lean_root" \
	"canonical PQXDH session-refinement proof import"
require_line_count 1 '^import BeaconcryptCore\.Refinement\.PqxdhCommitment$' \
	"$lean_root" \
	"canonical PQXDH commitment-refinement proof import"
require_line_count 1 '^import BeaconcryptCore\.Verification\.PqxdhCommitmentRefinement$' \
	"$lean_root" \
	"canonical PQXDH commitment-refinement contract proof import"
for pqxdh_root_module in Instance InstanceCommit Acceptance Runs; do
	require_line_count 1 "^import BeaconcryptCore\\.Model\\.Pqxdh\\.${pqxdh_root_module}$" \
		"$lean_root" "canonical ideal PQXDH ${pqxdh_root_module} proof-root import"
done
require_line_count 1 '^import BeaconcryptCore\.Computational\.VCVioFeasibility$' \
	"$lean_root" \
	"canonical VCVio feasibility proof-root import"
for pqxdh_computational_module in PqxdhJointKdf PqxdhJointKdfGame PqxdhHiddenRoot PqxdhProjectionCollisions PqxdhKemIndCca PqxdhEd25519EufCma PqxdhInitializerSecrecy PqxdhInitialRatchetComplementarity PqxdhInitializedChainsSecrecy; do
	require_line_count 1 "^import BeaconcryptCore\\.Computational\\.${pqxdh_computational_module}$" \
		"$lean_root" "canonical PQXDH computational ${pqxdh_computational_module} proof-root import"
done
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxReduction$' \
	"$lean_root" \
	"canonical CTX reduction proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxRomAuth$' \
	"$lean_root" \
	"canonical modified-CTX ROM-authentication proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxPrefixIsolation$' \
	"$lean_root" \
	"canonical modified-CTX prefix-isolation proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxSplitCache$' \
	"$lean_root" \
	"canonical modified-CTX split-cache proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxSealSampling$' \
	"$lean_root" \
	"canonical modified-CTX seal-sampling proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxIndependentTags$' \
	"$lean_root" \
	"canonical modified-CTX independent-tag proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxHonestTagSampling$' \
	"$lean_root" \
	"canonical modified-CTX honest-tag sampling proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxNonceAeadIntCtxt$' \
	"$lean_root" \
	"canonical modified-CTX nonce-AEAD INT-CTXT proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxNonceAeadIndDollar$' \
	"$lean_root" \
	"canonical modified-CTX nonce-AEAD key-probe IND-dollar proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxNonceAeadIndDollarValidation$' \
	"$lean_root" \
	"canonical modified-CTX conventional IND-dollar validation proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxComputationalSecurity$' \
	"$lean_root" \
	"canonical modified-CTX computational-security proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxComputationalPrivacy$' \
	"$lean_root" \
	"canonical modified-CTX computational-privacy proof-root import"
require_line_count 1 '^LEAN_ROOT := \$\(LEAN_DIR\)/BeaconcryptCore\.lean$' Makefile \
	"maintained Lean verification root"
require_line_count 1 '^LEAN_PROOF_PATHS := \$\(LEAN_DIR\)/BeaconcryptCore \$\(LEAN_DIR\)/BeaconcryptCore\.lean$' Makefile \
	"complete maintained Lean policy paths"
require_line_count 1 '^check-lean-root:$' Makefile \
	"maintained Lean root check target"
require_line_count 1 '^globs = \["BeaconcryptCore", "BeaconcryptCore\.\*"\]$' \
	proofs/lean/lakefile.toml \
	"Lean root and all-submodule build glob"
for theorem_name in \
	pqxdh.concrete.start_initial_ratchet_kdf_exact \
	pqxdh.concrete.initial_request_accessor_exact \
	pqxdh.concrete.start_beacon_ratchet_kdf_exact \
	pqxdh.concrete.start_server_ratchet_kdf_exact \
	pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition \
	ratchet.concrete.ratchet_step_from_response_exact \
	ratchet.concrete.SendKdf.cancel_exact \
	ratchet.concrete.SendKdf.request_exact \
	ratchet.concrete.begin_send_nonexhausted_exact \
	ratchet.concrete.begin_send_exhausted_restores_entry \
	ratchet.concrete.SendKdf.resume_exact \
	ratchet.concrete.ReceiveKdf.cancel_exact \
	ratchet.concrete.ReceiveKdf.request_exact \
	ratchet.concrete.begin_receive_rejected_plan_restores_entry \
	ratchet.concrete.begin_receive_cached_exact \
	ratchet.concrete.begin_receive_future_request_exact \
	ratchet.concrete.ReceiveOpen.reject_exact \
	ratchet.concrete.ReceiveOpen.context_exact \
	ratchet.concrete.ReceiveOpen.future_sequence_exact \
	ratchet.concrete.ReceiveOpen.future_material_exact \
	ratchet.concrete.SendSeal.finish_returns_interpreter_result \
	ratchet.concrete.ReceiveOpen.finish_failure_restores_entry \
	ratchet.concrete.ReceiveOpen.finish_future_success_publishes_same_plaintext \
	ratchet.concrete.ReceiveOpen.finish_cached_success_publishes_same_plaintext; do
	require_line_count 1 "^theorem ${theorem_name//./\\.}( |$)" \
		proofs/lean/BeaconcryptCore/Refinement/RatchetEffect.lean \
		"current-production effect theorem ${theorem_name}"
done

for theorem_name in \
	plan_receive_until_accept_51_of_empty \
	plan_receive_until_reject_52 \
	advance_receive_target_ok; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		proofs/lean/BeaconcryptCore/Refinement/RatchetControl.lean \
		"corrected receive-boundary theorem ${theorem_name}"
done
require_line_count 1 '^theorem receiveMessage_refines( |$)' \
	proofs/lean/BeaconcryptCore/Refinement/RatchetRefinement.lean \
	"direct ideal receive refinement theorem"
reject_matches "obsolete bound-49 Lean refinement remains" \
	'\brecvStepGen\b|CachedOpenRefines\.(?:ideal_success_49|ideal_success_recvStep|finish_success_matches_ideal_49|finish_success_refines_49_of_publication)\b' \
	proofs/lean/BeaconcryptCore/Model \
	proofs/lean/BeaconcryptCore/Refinement

vcvio_pilot=proofs/lean/BeaconcryptCore/Computational/VCVioFeasibility.lean
for theorem_name in \
	ctx_binding_bound_tight \
	ctx_binding_bound_tight_512 \
	ctx_binding_bound \
	ctx_binding_bound_512 \
	extracted_aead_key_size \
	linked_run_success_state \
	linked_run_tombstoned_state \
	linked_run_two_calls_consumes_once \
	linked_run_success_public; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$vcvio_pilot" "VCVio feasibility theorem ${theorem_name}"
done
require_line_count 1 '^rev = "cbd4144b51d92da00dd50f05e068b2348fa6e529"$' \
	proofs/lean/lakefile.toml \
	"immutable VCVio v4.31 dependency pin"

pqxdh_joint_kdf=proofs/lean/BeaconcryptCore/Computational/PqxdhJointKdf.lean
for declaration in JointKdfAddress ProductionHkdfPrefixConsistent; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$pqxdh_joint_kdf" "joint PQXDH KDF structure ${declaration}"
done
for theorem_name in rootAddress_ne_ratchetAddress first64_eq_first32_append_second32 \
	first64_append_final12 rootSecret_eq_rootProjection rootChains_eq_initialProjection \
	initialOutput_eq_ratchetOut_prefix rootChains_left_eq_msgMaterial_key \
	rootChains_right_eq_nextChain; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$pqxdh_joint_kdf" "joint PQXDH KDF theorem ${theorem_name}"
done

pqxdh_joint_kdf_game=proofs/lean/BeaconcryptCore/Computational/PqxdhJointKdfGame.lean
for declaration in JointKdfViewQuery FixedHkdfSha512NoSaltSource \
	JointKdfViewAdversary FixedHkdfSha512JointStreamAdversary; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$pqxdh_joint_kdf_game" "joint KDF game structure ${declaration}"
done
for theorem_name in jointKdfLazyRandomStreamImpl_run_hit \
	jointKdfLazyRandomStreamImpl_run_miss jointKdfLazyRandomStreamImpl_hit_query_bound \
	jointKdfLazyRandomStreamImpl_miss_query_bound \
	jointKdfViewReduction_no_untyped_stream_queries \
	jointKdfViewAdvantage_eq_fixedHkdfSha512JointStreamAdvantage; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$pqxdh_joint_kdf_game" "joint KDF game theorem ${theorem_name}"
done

pqxdh_hidden_root=proofs/lean/BeaconcryptCore/Computational/PqxdhHiddenRoot.lean
for declaration in KnownPqxdhRootCoordinates HiddenRootSourceAdversary; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$pqxdh_hidden_root" "hidden PQXDH root structure ${declaration}"
done
for theorem_name in hiddenRootIKM_length hiddenRootIKM_injective \
	hiddenRootAddress_injective \
	hiddenRootReductionMain_uniform_query_bound hiddenRootReductionMain_root_query_bound \
	hiddenRootReductionMain_symmetric_query_bound hiddenRootReductionMain_stream_query_bound \
	hiddenRootReductionMain_no_untyped_stream_queries \
	hiddenRootReduction_no_untyped_stream_queries \
	evalDist_first32_uniformJointKdfStream \
	jointKdfSingletonProgrammed_tracking_tvDist_le_bad \
	hiddenRootStreamCandidates_length_le probEvent_uniformHiddenRoot_candidateHit_le \
	tvDist_hiddenRootSharedRandomGame_independentGame_le \
	hiddenRootAdvantage_le_fixedHkdfSha512JointStreamAdvantage_add; do
	require_line_count 1 "^(@\\[[^]]+\\] )?theorem ${theorem_name}( |$)" \
		"$pqxdh_hidden_root" "hidden PQXDH root theorem ${theorem_name}"
done
require_line_count 1 '^theorem parseHiddenRootCoordinate\?_eq_some_iff( |$)' \
	"$pqxdh_hidden_root" "hidden PQXDH root exact parser theorem"
require_line_count 1 '^#guard_msgs in$' \
	"$pqxdh_hidden_root" "hidden PQXDH root capstone guarded axiom audit"
require_line_count 1 '^#print axioms hiddenRootAdvantage_le_fixedHkdfSha512JointStreamAdvantage_add$' \
	"$pqxdh_hidden_root" "hidden PQXDH root capstone axiom audit"

pqxdh_projection_collisions=proofs/lean/BeaconcryptCore/Computational/PqxdhProjectionCollisions.lean
for declaration in Coord32 Observation32 Observation12 SourceProjectionLog SourceKdfAdversary \
	ProjectionObservationState; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$pqxdh_projection_collisions" "PQXDH projection-collision structure ${declaration}"
done
for definition in sourceQF sourceQS sourceQN sourceQStream sourceQ32; do
	require_line_count 1 "^def ${definition}( |$)" \
		"$pqxdh_projection_collisions" "PQXDH projection-collision accounting ${definition}"
done
for theorem_name in firstCoord_ne_secondCoord evalDist_split_uniformJointKdfStream \
	initial_firstCoord_eq_step_firstCoord initial_secondCoord_eq_step_secondCoord \
	bad32_iff_projectionCacheBad32 bad12_iff_projectionCacheBad12 \
	projectionCoordCachingLoggingImpl_simulateQ_invariant \
	projectionCoordCachingLoggingImpl_simulateQ_cache_marginal \
	probEvent_projectionCacheBad32_le_birthday probEvent_projectionCacheBad12_le_birthday \
	sourceProjectionCollision_random_le evalDist_fixedJointStreamRandom_eq_eagerCoordinates \
	evalDist_projectionCoordUnifiedRandom_prefetch_irrelevant \
	evalDist_sourceKdfEagerCoordinate_eq_deferred \
	evalDist_sourceProjectionObservedFullRandom_eq_deferred \
	probEvent_sourceProjectionCollision_fullRandom_eq_cache \
	sourceProjectionCollisionReduction_uniform_query_bound \
	sourceProjectionCollisionReduction_stream_query_bound \
	sourceProjectionCollisionReduction_no_untyped_stream_queries \
	sourceProjectionCollisionReduction_totalQueryBound sourceProjectionCollision_real_le; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$pqxdh_projection_collisions" "PQXDH projection-collision theorem ${theorem_name}"
done
require_line_count 1 '^#guard_msgs in$' \
	"$pqxdh_projection_collisions" "PQXDH projection-collision capstone guarded axiom audit"
require_line_count 1 '^#print axioms sourceProjectionCollision_real_le$' \
	"$pqxdh_projection_collisions" "PQXDH projection-collision capstone axiom audit"

pqxdh_kem_indcca=proofs/lean/BeaconcryptCore/Computational/PqxdhKemIndCca.lean
require_line_count 1 '^import BeaconcryptCore\.Model\.Pqxdh\.Primitives$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM source-shape dependency"
require_line_count 1 '^import VCVio\.CryptoFoundations\.KeyEncapMech$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM generic IND-CCA dependency"
reject_matches "PQXDH ML-KEM module imports the maintained proof root" \
	'^import BeaconcryptCore$' "$pqxdh_kem_indcca"
require_line_count 1 '^abbrev MlKem768PublicKey := List\.Vector UInt8 1184$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM exact untagged public-key width"
require_line_count 1 '^abbrev MlKem768Ciphertext := List\.Vector UInt8 1088$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM exact ciphertext width"
require_line_count 1 '^abbrev MlKemSharedSecret := List\.Vector UInt8 32$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM exact shared-secret width"
for declaration in MlKemChallengeTranscript OneKeyAdversary; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$pqxdh_kem_indcca" "PQXDH ML-KEM IND-CCA structure ${declaration}"
done
for transcript_field in \
	'  publicKey : MlKem768PublicKey' \
	'  ciphertext : MlKem768Ciphertext' \
	'  context : Context'; do
	require_line_count 1 "^${transcript_field}$" \
		"$pqxdh_kem_indcca" "PQXDH ML-KEM public challenge-transcript field ${transcript_field}"
done
require_line_count 1 '^  postChallenge : MlKemChallengeTranscript Context → MlKemSharedSecret →$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM private candidate-secret argument"
for definition in oneKeyPrefix oneKeyFinish oneKeyBranchMain oneKeyBranch \
	IsMlKemUniformQuery IsMlKemBaseQuery IsMlKemLogicalDecapsulationQuery \
	IsMlKemUnblockedDecapsulationQuery INDCCAAdversaryMakesAtMostQueries \
	mlKem768RecipientCorrectnessExp MlKem768RecipientCorrectness; do
	require_line_count 1 "^(noncomputable )?def ${definition}( |$)" \
		"$pqxdh_kem_indcca" "PQXDH ML-KEM IND-CCA definition ${definition}"
done
for namespaced_definition in toINDCCA MakesAtMostQueries logicalClientMain; do
	require_line_count 1 "^def OneKeyAdversary\.${namespaced_definition}( |$)" \
		"$pqxdh_kem_indcca" "PQXDH ML-KEM adversary definition ${namespaced_definition}"
done
for theorem_name in boolBias_sharedPrefix_eq_branchDist \
	oneKey_indCCAAdvantage_eq_branchDist \
	OneKeyAdversary.toINDCCA_pre_queryBound_iff \
	OneKeyAdversary.toINDCCA_post_queryBound_iff \
	OneKeyAdversary.toINDCCA_makesAtMostQueries_iff \
	unblockedDecapsulationQueryBound_of_logical \
	OneKeyAdversary.post_unblockedDecapsulationQueryBound \
	OneKeyAdversary.logicalClient_uniformQueryBound \
	OneKeyAdversary.logicalClient_baseQueryBound \
	OneKeyAdversary.logicalClient_decapsulationQueryBound \
	indCCA_preChallengeImpl_decapsulation \
	indCCA_postChallengeImpl_challenge \
	indCCA_postChallengeImpl_nonchallenge \
	mlKem768RecipientCorrectness_iff_perfectlyCorrect \
	mlKem768RecipientCorrectness_recovered_eq; do
	require_line_count 1 "^theorem ${theorem_name//./\.}( |$)" \
		"$pqxdh_kem_indcca" "PQXDH ML-KEM IND-CCA theorem ${theorem_name}"
done
require_line_count 1 '^    kem\.IND_CCA_Advantage runtime adversary\.toINDCCA =$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM factor-one generic IND-CCA endpoint"
require_line_count 1 '^        \(oneKeyBranch kem runtime adversary true\)$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM real branch orientation"
require_line_count 1 '^        \(oneKeyBranch kem runtime adversary false\) := by$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM uniform branch orientation"
require_line_count 1 '^  let kRand ← runtime\.liftProbComp \(\$ᵗ MlKemSharedSecret\)$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM branch-independent ghost secret draw"
require_line_count 1 '^    \(adversary\.postChallenge .* \(if b then kReal else kRand\)\)$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM true-real false-uniform branch mapping"
require_line_count 2 '^#guard_msgs in$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM guarded axiom audits"
require_line_count 1 '^#print axioms oneKey_indCCAAdvantage_eq_branchDist$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM IND-CCA capstone axiom audit"
require_line_count 1 '^#print axioms mlKem768RecipientCorrectness_recovered_eq$' \
	"$pqxdh_kem_indcca" "PQXDH ML-KEM recipient-correctness axiom audit"

pqxdh_ed25519_eufcma=proofs/lean/BeaconcryptCore/Computational/PqxdhEd25519EufCma.lean
require_line_count 1 '^import BeaconcryptCore\.Model\.Pqxdh\.Primitives$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 exact-encoding dependency"
require_line_count 1 '^import VCVio\.CryptoFoundations\.SignatureAlg$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 generic EUF-CMA dependency"
reject_matches "PQXDH Ed25519 module imports the maintained proof root" \
	'^import BeaconcryptCore$' "$pqxdh_ed25519_eufcma"
require_line_count 1 '^abbrev Ed25519PublicKey := List\.Vector UInt8 32$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 exact raw public-key width"
require_line_count 1 '^abbrev Ed25519Signature := List\.Vector UInt8 64$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 exact raw signature width"
require_line_count 1 '^abbrev MlKem768PublicKey := List\.Vector UInt8 1184$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 exact raw ML-KEM public-key width"
require_line_count 1 '^  signature\.toList \+\+ message$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 attached signature-prefix shape"
require_line_count 1 '^  if h : 64 ≤ buffer\.length then$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 exact attached split width"
for definition in encodedIdentity prekeyMessage oneTimeMessage pqMessage; do
	require_line_count 1 "^def ${definition}( |$)" \
		"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 canonical encoding ${definition}"
done
require_line_count 1 '^  Pqxdh\.tagSig pk\.toList$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 identity marker encoding"
require_line_count 1 '^  Pqxdh\.tagX Pqxdh\.rolePre prekey\.toList$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 prekey role encoding"
require_line_count 1 '^  Pqxdh\.tagX Pqxdh\.roleOtk oneTime\.toList$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 one-time role encoding"
require_line_count 1 '^  Pqxdh\.tagPQ pqKey\.toList$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 PQ marker encoding"
for declaration in Phase1Material Phase1KeyTuple Phase1Candidate Phase1PublicTranscript \
	Phase1MaterialGenerator Phase1Adversary Phase1ClientResult Phase1SharedResult; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 structure ${declaration}"
done
for theorem_name in splitAttachedSignature_attach splitAttachedSignature_eq_none_iff \
	splitAttachedSignature_eq_some_iff attachSignature_injective \
	parseIdentity_eq_some_iff parsePrekeyMessage_eq_some_iff \
	parseOneTimeMessage_eq_some_iff parsePqMessage_eq_some_iff \
	prekeyMessage_ne_oneTimeMessage prekeyMessage_ne_pqMessage \
	oneTimeMessage_ne_pqMessage phase1FieldSubstitutionBit_eq_true_iff \
	phase1FieldSubstitution_selects_fresh_valid phase1ClientMain_logged_messages \
	phase1ClientMain_signingQueryBound phase1ClientMain_baseQueryBound \
	phase1ToEUFCMA_signingQueryBound phase1ToEUFCMA_baseQueryBound \
	ed25519AttachedSignatureCorrectness_iff_perfectlyComplete \
	ed25519AttachedSignatureCorrectness_opens_supported \
	attachedVerificationAdapter_opens_honest \
	phase1FieldSubstitutionAdvantage_le_eufCma; do
	require_line_count 1 "^(@\[simp\] )?theorem ${theorem_name}( |$)" \
		"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 theorem ${theorem_name}"
done
for definition in attachSignature splitAttachedSignature openAttached \
	decodePhase1Candidate acceptPhase1Candidate phase1FieldSubstitutionBit \
	selectPhase1Forgery HasDeterministicVerification honestPhase1Transcript \
	phase1ClientMain phase1ToEUFCMA Phase1FieldSubstitutionAdvantage \
	IsPhase1BaseQuery IsPhase1SigningQuery HasAttachedVerificationAdapter \
	Ed25519AttachedSignatureCorrectness; do
	require_line_count 1 "^(noncomputable )?def ${definition}( |$)" \
		"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 definition ${definition}"
done
require_line_count 1 '^  let pqPayload ← openAttached verifyFn candidatePk candidate\.pqKey$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 server-first PQ verification"
require_line_count 1 '^  let prePayload ← openAttached verifyFn candidatePk candidate\.preKey$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 server-second prekey verification"
require_line_count 1 '^  let onePayload ← openAttached verifyFn candidatePk candidate\.oneTimeKey$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 server-third one-time verification"
require_line_count 1 '^      decide \(candidatePk = targetPk ∧ decoded ≠ material\.keyTuple\)$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 honest-target bad-event filter"
require_line_count 1 '^  let preSignature ← liftM$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 first prekey signing call"
require_line_count 1 '^  let oneTimeSignature ← liftM$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 second one-time signing call"
require_line_count 1 '^  let pqSignature ← liftM$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 third PQ signing call"
require_line_count 1 '^      \(phase1ToEUFCMA sigAlg materialGenerator adversary\)\.advantage runtime := by$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 coefficient-one generic EUF-CMA endpoint"
require_line_count 2 '^      IsPhase1SigningQuery 3 := by$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 three-query client and reduction bounds"
require_line_count 2 '^      IsPhase1BaseQuery \(qMaterial \+ qAdversary\) := by$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 additive base-query bounds"
require_line_count 2 '^#guard_msgs in$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 guarded axiom audits"
require_line_count 1 '^#print axioms phase1FieldSubstitutionAdvantage_le_eufCma$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 EUF-CMA capstone axiom audit"
require_line_count 1 '^#print axioms ed25519AttachedSignatureCorrectness_opens_supported$' \
	"$pqxdh_ed25519_eufcma" "PQXDH Ed25519 correctness axiom audit"

pqxdh_initializer_secrecy=proofs/lean/BeaconcryptCore/Computational/PqxdhInitializerSecrecy.lean
require_line_count 1 '^import BeaconcryptCore\.Computational\.PqxdhKemIndCca$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer one-key KEM dependency"
require_line_count 1 '^import BeaconcryptCore\.Computational\.PqxdhHiddenRoot$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer hidden-root dependency"
reject_matches "PQXDH initializer module imports the maintained proof root" \
	'^import BeaconcryptCore$' "$pqxdh_initializer_secrecy"
require_line_count 1 '^abbrev InitializerPostSpec \(baseSpec : OracleSpec iota\) :=$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer exact post-challenge surface"
require_occurrence_count 1 \
	'^structure InitializerPublicTranscript \(Context : Type\) where\n  publicKey : MlKem768PublicKey\n  ciphertext : MlKem768Ciphertext\n  context : Context\n\n' \
	"PQXDH initializer exact secret-free public transcript surface" \
	"$pqxdh_initializer_secrecy"
require_occurrence_count 1 \
	'^structure InitializerAdversary\n    \(kem : MlKemScheme \(baseSpec := baseSpec\) \(SK := SK\)\) where\n  State : Type\n  Context : Type\n  preChallenge : MlKem768PublicKey → OracleComp kem\.IND_CCA_oracleSpec State\n  knownCoordinates : State → MlKem768PublicKey → MlKem768Ciphertext →\n    KnownPqxdhRootCoordinates\n  publicContext : State → MlKem768PublicKey → MlKem768Ciphertext → Context\n  main : InitializerPublicTranscript Context → KnownPqxdhRootCoordinates →\n    HiddenRootCoordinate → OracleComp \(InitializerPostSpec baseSpec\) Bool\n\n' \
	"PQXDH initializer exact adversary public-prefix and private-root interface" \
	"$pqxdh_initializer_secrecy"
for declaration in InitializerPublicTranscript InitializerAdversary InitializerKdfPrefix \
	InitializerKdfReductionBounds InitializerExplicitReductionBounds; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$pqxdh_initializer_secrecy" "PQXDH initializer structure ${declaration}"
done
for definition in runtimeOfImpl initializerPostRealImpl toKemOneKeyAdversary \
	initializerKemBranch kemAmbientImpl initializerKdfPrefixProb \
	ambientToJointKdfViewImpl initializerPostToJointKdfViewImpl \
	toHiddenRootAdversary sampledHiddenRootAdversary initializerKdfReductionMain \
	initializerUniformKemCore initializerUniformKemGame initializerSharedRootGame \
	initializerIndependentRootGame initializerKdfReduction initializerRealGame \
	initializerSecrecyAdvantage; do
	require_line_count 1 "^(noncomputable )?def ${definition}( |$)" \
		"$pqxdh_initializer_secrecy" "PQXDH initializer definition ${definition}"
done
for definition in IsInitializerUniformQuery IsInitializerBaseQuery \
	IsInitializerLogicalDecapsulationQuery IsInitializerRootQuery \
	IsInitializerSymmetricQuery; do
	require_line_count 1 "^def ${definition}( |$)" \
		"$pqxdh_initializer_secrecy" "PQXDH initializer query predicate ${definition}"
done
for theorem_name in initializerUniformKemGame_eq_core \
	initializerKdfReduction_real_eq_uniformKem \
	initializerKdfReduction_random_eq_sharedRoot \
	simulateQ_initializerOneKeyFalse_eq_falseCore \
	initializerKemFalseCore_eq_uniformKemCore \
	initializerKemBranch_false_eq_uniformKemCore \
	initializerPostToJointKdfViewImpl_challenge \
	initializerPostToJointKdfViewImpl_nonchallenge \
	initializerPostRealImpl_uniform_query_bound \
	initializerPostRealImpl_base_query_bound \
	initializerPostRealImpl_decapsulation_query_bound \
	toKemOneKeyAdversary_makesAtMostQueries \
	initializerKdfReduction_uniform_query_bound \
	initializerKdfReduction_root_query_bound \
	initializerKdfReduction_symmetric_query_bound \
	initializerKdfReduction_stream_query_bound \
	initializerKdfReduction_totalQueryBound \
	initializerKdfReduction_no_untyped_stream_queries \
	runtimeOfImpl_evalDist_pure runtimeOfImpl_evalDist_bind \
	runtimeOfImpl_evalDist_liftProbComp runtimeOfImpl_noFail_bool \
	initializerKemBranch_true_eq_real \
	initializerKemBranch_false_eq_uniformKemGame \
	initializerReal_uniformKem_advantage_eq_indCCA \
	tvDist_initializerSharedRoot_independentRoot_le \
	initializerSharedRoot_independentRoot_advantage_le \
	initializerUniformKem_sharedRoot_advantage_eq_fixedHkdf \
	initializerKemReduction_makesAtMostQueries \
	initializerKemReduction_post_unblockedDecapsulationQueryBound \
	initializerSecrecyAdvantage_le; do
	require_line_count 1 "^(@\[simp\] )?theorem ${theorem_name}( |$)" \
		"$pqxdh_initializer_secrecy" "PQXDH initializer theorem ${theorem_name}"
done
require_line_count 2 '^  let \(cStar, _kReal\) ← simulateQ \(kemAmbientImpl baseImpl\) \(kem\.encaps pk\)$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer KDF-prefix and normalized false branch discard the real secret"
require_line_count 1 '^  let hidden ← \$ᵗ HiddenRootCoordinate$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer single uniform KEM replacement sample"
require_occurrence_count 1 \
	'^  let kRand ← \$ᵗ MlKemSharedSecret\n  simulateQ \(kemAmbientImpl baseImpl\)[\s\S]{0,700}\(productionHiddenRoot source\n            \(adversary\.knownCoordinates state pk cStar\) kRand\)\)\)\)$' \
	"PQXDH initializer false core samples and uses exactly one uniform replacement secret" \
	"$pqxdh_initializer_secrecy"
require_line_count 1 '^        \(\.inl \(\.inr cStar\)\) =$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer exact challenge-ciphertext block"
require_line_count 1 '^    FixedHkdfSha512JointStreamAdversary$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer fixed-HKDF reduction endpoint"
require_line_count 1 '^      \(qKemAmbient \+ qUPre \+ qUPost \+ 32\) \(qRoot \+ qSym \+ 1\) where$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer uniform and stream reduction caps"
require_line_count 1 '^  ambientTotal : qKemPrefix \+ qKemPost ≤ qKemAmbient$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer caller-supplied ambient slack relation"
require_line_count 1 '^        IsFixedHkdfSha512UniformQuery \(qKemPrefix \+ qUPre\)$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer direct transformed-prefix uniform obligation"
require_line_count 1 '^      IsJointKdfViewUniformQuery \(qKemPost \+ qUPost\)$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer direct transformed-post uniform obligation"
require_line_count 1 '^      IsFixedHkdfRootStreamQuery \(qRoot \+ 1\) :=$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer root-domain upper bound"
require_line_count 1 '^      IsFixedHkdfSymmetricStreamQuery qSym :=$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer symmetric-domain upper bound"
require_line_count 1 '^      IsFixedHkdfSha512UntypedStreamQuery 0 :=$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer zero-untyped-stream invariant"
require_line_count 2 '^      kem\.IND_CCA_Advantage \(runtimeOfImpl \(kemAmbientImpl baseImpl\)\)$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer coefficient-one KEM endpoint"
require_line_count 2 '^        fixedHkdfSha512JointStreamAdvantage source$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer coefficient-one fixed-HKDF endpoint"
require_line_count 2 '^        \(\(qRoot : ℝ≥0∞\) / \(2 \^ 256 : ℝ≥0∞\)\)\.toReal := by$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer single hidden-root guess term"
require_line_count 3 '^#guard_msgs in$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer guarded axiom audits"
require_line_count 1 '^#print axioms initializerSecrecyAdvantage_le$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer capstone axiom audit"
require_line_count 1 '^#print axioms initializerKdfReduction_no_untyped_stream_queries$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer untyped-query axiom audit"
require_line_count 1 '^#print axioms initializerPostToJointKdfViewImpl_challenge$' \
	"$pqxdh_initializer_secrecy" "PQXDH initializer challenge-block axiom audit"

pqxdh_initial_ratchet=proofs/lean/BeaconcryptCore/Computational/PqxdhInitialRatchetComplementarity.lean
for import_name in \
	BeaconcryptCore.Computational.PqxdhJointKdf \
	BeaconcryptCore.Refinement.PqxdhCore \
	BeaconcryptCore.Refinement.RatchetEffectRefinement; do
	require_line_count 1 "^import ${import_name//./\\.}$" \
		"$pqxdh_initial_ratchet" "PQXDH initial-ratchet narrow import ${import_name}"
done
reject_matches "PQXDH initial-ratchet module imports the maintained proof root" \
	'^import BeaconcryptCore$' "$pqxdh_initial_ratchet"
for definition in firstHalf secondHalf ChainBytesRefines RootArrayRefines \
	InitialResponseRefines serverPending beaconPending InitialKernelResult InitialKernelWitness; do
	require_line_count 1 "^def ${definition}( |$)" \
		"$pqxdh_initial_ratchet" "PQXDH initial-ratchet definition ${definition}"
done
for theorem_name in chain_eq_of_refines InitialResponseRefines.modelOutput \
	absBytes_ratchetSymmetricInfo serverStartRequest_refines beaconStartRequest_refines \
	initialHalves_exact splitInitialServer_exact splitInitialBeacon_exact \
	concreteKernelNew_exact concreteKernelNew_refines_initial serverStartResume_refines \
	beaconStartResume_refines initialRatchetComplementarity \
	initialRatchetComplementarity_jointStream; do
	require_line_count 1 "^(@\[simp\] )?theorem ${theorem_name//./\\.}( |$)" \
		"$pqxdh_initial_ratchet" "PQXDH initial-ratchet theorem ${theorem_name}"
done
require_line_count 1 '^def InitialResponseRefines \(c : Pqxdh\.Crypto\)$' \
	"$pqxdh_initial_ratchet" "PQXDH initial response external equation"
require_line_count 1 '^    c\.hkdf \(PqxdhRefinement\.absBytes pending\.request\.input\)$' \
	"$pqxdh_initial_ratchet" "PQXDH initial response exact pending input"
require_line_count 1 '^      \(PqxdhRefinement\.absBytes pending\.request\.info\) 64$' \
	"$pqxdh_initial_ratchet" "PQXDH initial response exact pending label and width"
require_line_count 2 '^  initialization := \{ send_offset := (0|32)#u8, receive_offset := (32|0)#u8 \}$' \
	"$pqxdh_initial_ratchet" "PQXDH initial canonical opposite role offsets"
require_line_count 1 '^def firstHalf \(output : Std\.Array Std\.U8 64#usize\) : Pqxdh\.Bytes :=$' \
	"$pqxdh_initial_ratchet" "PQXDH initial first-half width"
require_line_count 1 '^  \(PqxdhRefinement\.absBytes output\)\.take 32$' \
	"$pqxdh_initial_ratchet" "PQXDH initial first-half projection"
require_line_count 1 '^  \(PqxdhRefinement\.absBytes output\)\.drop 32$' \
	"$pqxdh_initial_ratchet" "PQXDH initial second-half projection"
require_line_count 1 '^      kernel\.refined\.control\.send_sequence\.val = 0 ∧$' \
	"$pqxdh_initial_ratchet" "PQXDH initial zero send counter"
require_line_count 1 '^      kernel\.refined\.control\.receive_sequence\.val = 0 ∧$' \
	"$pqxdh_initial_ratchet" "PQXDH initial zero receive counter"
require_line_count 1 '^      kernel\.refined\.control\.receive_cache\.len\.val = 0 ∧$' \
	"$pqxdh_initial_ratchet" "PQXDH initial empty receive cache"
require_line_count 1 '^        kernel\.refined\.receive_slots\.val\[i\]! = core\.option\.Option\.None\) := by$' \
	"$pqxdh_initial_ratchet" "PQXDH initial empty material slots"
require_line_count 2 '^        serverKernel\.refined\.send_chain = beaconKernel\.refined\.receive_chain ∧$' \
	"$pqxdh_initial_ratchet" "PQXDH initial Server-send Beacon-receive complementarity"
require_line_count 2 '^        serverKernel\.refined\.receive_chain = beaconKernel\.refined\.send_chain := by$' \
	"$pqxdh_initial_ratchet" "PQXDH initial Server-receive Beacon-send complementarity"
require_line_count 1 '^    \(hprefix : BeaconcryptCore\.Computational\.PqxdhJointKdf\.ProductionHkdfPrefixConsistent c\)$' \
	"$pqxdh_initial_ratchet" "PQXDH initial explicit production-prefix premise"
require_line_count 1 '^      \(BeaconcryptCore\.Computational\.PqxdhJointKdf\.productionStream c$' \
	"$pqxdh_initial_ratchet" "PQXDH initial canonical joint stream"
require_line_count 1 '^        \(BeaconcryptCore\.Computational\.PqxdhJointKdf\.ratchetAddress root\)\)$' \
	"$pqxdh_initial_ratchet" "PQXDH initial canonical ratchet address"
require_line_count 3 '^#guard_msgs in$' \
	"$pqxdh_initial_ratchet" "PQXDH initial-ratchet guarded axiom audits"
for theorem_name in concreteKernelNew_refines_initial initialRatchetComplementarity \
	initialRatchetComplementarity_jointStream; do
	require_line_count 1 "^#print axioms ${theorem_name}$" \
		"$pqxdh_initial_ratchet" "PQXDH initial-ratchet axiom audit ${theorem_name}"
done

pqxdh_initialized_chains=proofs/lean/BeaconcryptCore/Computational/PqxdhInitializedChainsSecrecy.lean
for import_name in \
	BeaconcryptCore.Computational.PqxdhInitializerSecrecy \
	BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity; do
	require_line_count 1 "^import ${import_name//./\\.}$" \
		"$pqxdh_initialized_chains" "PQXDH initialized-chain narrow import ${import_name}"
done
require_line_count 2 '^import ' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain exact import count"
for structure_name in InitializedDirectionalChains InitializedChainsObserver \
	InitializedChainsExplicitReductionBounds; do
	require_line_count 1 "^structure ${structure_name}( |$)" \
		"$pqxdh_initialized_chains" "PQXDH initialized-chain structure ${structure_name}"
done
for definition in initializedFirstQuery initializedSecondQuery \
	initializedChainsWrapperMain toInitializerAdversary \
	InitializedChainsObserver.MakesAtMostQueries \
	toProductionInitializedChainsOneKeyAdversary productionInitializedChainsGame \
	independentRootInitializedChainsGame \
	InitializedChainsExplicitReductionBounds.toInitializerBounds \
	initializedChainsKemReduction initializedChainsKdfReduction \
	initializedChainsSecrecyAdvantage productionDirectionalChains; do
	require_line_count 1 "^(noncomputable )?def ${definition//./\\.}( |$)" \
		"$pqxdh_initialized_chains" "PQXDH initialized-chain definition ${definition}"
done
for theorem_name in initializedFirstQuery_address initializedSecondQuery_address \
	initializedQueries_same_address initializedFirstQuery_width initializedSecondQuery_width \
	initializedChainsWrapperMain_query_normal_form \
	simulateQ_initializedChainsWrapperMain_real \
	initializedChainsWrapperMain_uniform_query_bound \
	initializedChainsWrapperMain_base_query_bound \
	initializedChainsWrapperMain_decapsulation_query_bound \
	initializedChainsWrapperMain_root_query_bound \
	initializedChainsWrapperMain_symmetric_query_bound \
	toInitializerAdversary_makesAtMostQueries \
	simulateQ_initializedChainsWrapperMain_toJointKdfView \
	jointKdfViewRandomImpl_inr_run_miss jointKdfViewRandomImpl_inr_run_hit \
	run_initializedChainsWrapperMain_random_empty \
	"run'_initializedChainsWrapperMain_random_empty" \
	toKemOneKeyAdversary_initializedChains_postChallenge \
	initializerRealGame_initializedChains_eq_production \
	initializerIndependentRootGame_initializedChains_eq \
	initializedChainsKdfReduction_uniform_query_bound \
	initializedChainsKdfReduction_stream_query_bound \
	initializedChainsKdfReduction_root_query_bound \
	initializedChainsKdfReduction_symmetric_query_bound \
	initializedChainsKdfReduction_no_untyped_stream_queries \
	initializedChainsKdfReduction_totalQueryBound \
	initializedChainsKemReduction_makesAtMostQueries \
	initializedChainsKemReduction_post_unblockedDecapsulationQueryBound \
	initializedChainsSecrecyAdvantage_le \
	productionDirectionalChains_serverToBeacon productionDirectionalChains_beaconToServer \
	productionInitializedChains_to_concreteKernels; do
	require_line_count 1 "^(@\[simp\] )?theorem ${theorem_name}( |$)" \
		"$pqxdh_initialized_chains" "PQXDH initialized-chain theorem ${theorem_name}"
done
require_line_count 1 '^  main : InitializerPublicTranscript Context → KnownPqxdhRootCoordinates →$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain observer public inputs"
require_line_count 1 '^    InitializedDirectionalChains → OracleComp \(InitializerPostSpec baseSpec\) Bool$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain observer chain-only argument"
require_line_count 1 '^  serverToBeacon : Pqxdh\.Bytes$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain Server-to-Beacon model bytes"
require_line_count 1 '^  beaconToServer : Pqxdh\.Bytes$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain Beacon-to-Server model bytes"
require_line_count 1 '^  ⟨root\.toList, \.ratchet, \.first32⟩$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain first typed same-root query"
require_line_count 1 '^  ⟨root\.toList, \.ratchet, \.second32⟩$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain second typed same-root query"
require_line_count 1 '^      kem\.IND_CCA_Advantage \(runtimeOfImpl \(kemAmbientImpl baseImpl\)\)$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain one KEM advantage"
require_line_count 1 '^        fixedHkdfSha512JointStreamAdvantage source$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain one fixed-HKDF advantage"
require_line_count 1 '^        \(\(qRoot : ℝ≥0∞\) / \(2 \^ 256 : ℝ≥0∞\)\)\.toReal := by$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain one root-guess term"
require_line_count 1 '^      IsFixedHkdfSymmetricStreamQuery \(qSym \+ 2\) :=$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain two added symmetric calls"
require_line_count 1 '^      IsFixedHkdfSha512StreamQuery \(qRoot \+ \(qSym \+ 2\) \+ 1\) :=$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain complete-stream accounting"
require_line_count 1 '^      IsFixedHkdfSha512UntypedStreamQuery 0 :=$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain no untyped calls"
require_line_count 1 '^    \(hserverRoot : RootArrayRefines serverRoot root\)$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain separate Server root premise"
require_line_count 1 '^    \(hbeaconRoot : RootArrayRefines beaconRoot root\)$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain separate Beacon root premise"
require_line_count 1 '^      \(serverPending serverRoot\) serverResponse\)$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain pending-indexed Server response"
require_line_count 1 '^      \(beaconPending beaconRoot\) beaconResponse\) :$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain pending-indexed Beacon response"
require_line_count 3 '^#guard_msgs in$' \
	"$pqxdh_initialized_chains" "PQXDH initialized-chain guarded axiom audits"
for theorem_name in run_initializedChainsWrapperMain_random_empty \
	initializedChainsSecrecyAdvantage_le productionInitializedChains_to_concreteKernels; do
	require_line_count 1 "^#print axioms ${theorem_name}$" \
		"$pqxdh_initialized_chains" "PQXDH initialized-chain axiom audit ${theorem_name}"
done

require_line_count 1 '^theorem openRecord_double_opening_yields_ctx_collision( |$)' \
	proofs/lean/BeaconcryptCore/Model/Pqxdh/Commit.lean \
	"ideal CTX collision-extraction theorem"
pqxdh_commitment_refinement=proofs/lean/BeaconcryptCore/Refinement/PqxdhCommitment.lean
for theorem_name in \
	commitment_encode_u64_le_eq_registration \
	commitment_encode_u64_le_abs \
	build_commitment_transcript_call_mut \
	build_commitment_transcript_abs; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$pqxdh_commitment_refinement" "extracted commitment refinement theorem ${theorem_name}"
done
pqxdh_commitment_refinement_contract=proofs/lean/BeaconcryptCore/Verification/PqxdhCommitmentRefinement.lean
require_line_count 1 '^import BeaconcryptCore\.Refinement\.PqxdhCommitment$' \
	"$pqxdh_commitment_refinement_contract" \
	"PQXDH commitment-refinement contract source import"
require_line_count 2 '^#guard_msgs in$' \
	"$pqxdh_commitment_refinement_contract" \
	"PQXDH commitment-refinement contract guarded axiom audits"
for theorem_name in commitment_encode_u64_le_abs build_commitment_transcript_abs; do
	require_line_count 1 "^#print axioms ${theorem_name}$" \
		"$pqxdh_commitment_refinement_contract" \
		"PQXDH commitment-refinement contract axiom audit ${theorem_name}"
done
ctx_reduction=proofs/lean/BeaconcryptCore/Computational/CtxReduction.lean
for theorem_name in \
	ctxMisattribution_implies_blake2b_collision \
	ctxMisattributionAdvantage_le_blake2b_cr \
	ctxFullCommitment_implies_misattribution \
	ctxFullCommitment_implies_blake2b_collision \
	ctxFullCommitmentAdvantage_le_blake2b_cr \
	successful_wrong_sequence_open_yields_blake2b_collision \
	successful_wrong_sender_open_yields_blake2b_collision \
	successful_cross_session_open_yields_blake2b_collision \
	ctxRelabelAdvantage_le_blake2b_cr; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_reduction" "native CTX computational theorem ${theorem_name}"
done
for declaration in CtxExplanation CtxAttempt CtxFullCommitmentAttempt CtxRelabelClaim; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$ctx_reduction" "native CTX game structure ${declaration}"
done
for declaration in CtxMisattribution ctxCollisionInputs ctxCollisionReduction \
	CtxFullCommitment ctxFullCommitmentMisattributionAttempt \
	ctxFullCommitmentCollisionInputs ctxFullCommitmentCollisionReduction; do
	require_line_count 1 "^def ${declaration}( |$)" \
		"$ctx_reduction" "native CTX game definition ${declaration}"
done
for declaration in ctxMisattributionExp ctxMisattributionAdvantage \
	ctxFullCommitmentExp ctxFullCommitmentAdvantage; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_reduction" "native CTX probability definition ${declaration}"
done

ctx_retained_tag_projection=proofs/lean/BeaconcryptCore/Computational/CtxRetainedTagProjection.lean
for theorem_name in \
	encode_eq_of_decodeRecord_eq_some \
	openRecord_success_implies_base_success \
	valid_record_eq_honest_seal \
	fixedMaterialContext_ctxFresh_implies_baseFresh \
	fixedMaterialContext_ctxFreshOpening_implies_baseFreshOpening \
	fixedMaterialContext_ctxFreshOpeningProbability_le_sameViewBaseFreshOpeningProbability; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_retained_tag_projection" "retained-tag authenticity projection theorem ${theorem_name}"
done
require_line_count 1 '^structure FixedMaterialContextAttempt( |$)' \
	"$ctx_retained_tag_projection" "fixed-material/context authenticity attempt"
for declaration in baseCipher honestCtxOutput honestBaseOutput \
	FixedMaterialContextCtxFreshOpening SameViewBaseFreshOpening; do
	require_line_count 1 "^def ${declaration}( |$)" \
		"$ctx_retained_tag_projection" "retained-tag authenticity definition ${declaration}"
done
for declaration in fixedMaterialContextCtxFreshOpeningExp \
	fixedMaterialContextCtxFreshOpeningProbability sameViewBaseFreshOpeningExp \
	sameViewBaseFreshOpeningProbability; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_retained_tag_projection" "retained-tag probability definition ${declaration}"
done

ctx_auth_classification=proofs/lean/BeaconcryptCore/Computational/CtxAuthClassification.lean
for theorem_name in \
	acceptedFullFreshForgery_classification \
	contextAliasReplay_has_distinct_ctxPreimages \
	ctxAcceptedFullFreshForgeryProbability_le_projection_add_alias \
	contextAliasReplay_target_outerHashPreimage_fresh \
	nonceConsistentAcceptedFullFreshForgery_classification \
	ctxNonceConsistentAliasReplayProbability_le_freshTargetOuterHashAliasReplay \
	ctxNonceConsistentAcceptedFullFreshForgeryProbability_le_nonceConsistentProjection_add_freshAlias; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_auth_classification" "general CTX authenticity classification theorem ${theorem_name}"
done
for declaration in CtxSealHistoryEntry CtxAuthClassificationAttempt; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$ctx_auth_classification" "general CTX authenticity structure ${declaration}"
done
for declaration in CtxFullFresh CtxBaseProjectionMatch CtxBaseProjectionFresh \
	CtxAcceptedFullFreshForgery CtxFreshAcceptedBaseProjection CtxContextAliasReplay \
	CtxPerKeyNonceConsistent CtxTargetOuterHashPreimageFresh \
	CtxFreshTargetOuterHashPreimage CtxFreshTargetOuterHashAliasReplay \
	CtxNonceConsistentAcceptedFullFreshForgery \
	CtxNonceConsistentFreshAcceptedBaseProjection; do
	require_line_count 1 "^def ${declaration}( |$)" \
		"$ctx_auth_classification" "general CTX authenticity definition ${declaration}"
done
for declaration in CtxSealHistoryEntry.ctxOutput CtxSealHistoryEntry.baseOutput \
	CtxSealHistoryEntry.outerHashPreimage; do
	require_line_count 1 "^def ${declaration//./\\.}( |$)" \
		"$ctx_auth_classification" "general CTX authentication output ${declaration}"
done
for declaration in ctxAcceptedFullFreshForgeryProbability \
	ctxFreshAcceptedBaseProjectionProbability ctxContextAliasReplayProbability \
	ctxNonceConsistentAliasReplayProbability \
	ctxFreshTargetOuterHashAliasReplayProbability \
	ctxNonceConsistentFreshAcceptedBaseProjectionProbability \
	ctxNonceConsistentAcceptedFullFreshForgeryProbability; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_auth_classification" "general CTX authentication probability ${declaration}"
done

ctx_rom_auth=proofs/lean/BeaconcryptCore/Computational/CtxRomAuth.lean
for theorem_name in \
	ctxRandomOracle_cache_origin \
	ctxPublicOracle_preserves_invariant \
	ctxSealOracle_preserves_invariant \
	ctxAdversaryImpl_preserves_invariant \
	ctxAdversary_run_invariant \
	ctxBeforeVerifyInner_invariant \
	ctxBeforeVerifyGame_invariant \
	publicTargetQueried_implies_secretPrefixQueried \
	fullAliasShape_excludes_honestTarget \
	aliasCacheHit_implies_publicTargetQueried \
	generated_aliasCacheHit_implies_publicTargetQueried \
	generated_aliasCacheHit_implies_secretPrefixQueried \
	ctxAliasTargetCacheHitProbability_le_secretPrefixQueriedProbability \
	ctxFreshAliasVerifier_le_inv \
	ctxFreshAliasGame_le_inv \
	ctxDigest_card \
	ctxFreshAliasGame_le_inv_512 \
	ctxAliasGameProbability_le_cacheHit_add_inv \
	ctxAliasGameProbability_le_cacheHit_add_inv_512 \
	ctxAliasGameProbability_le_secretPrefix_add_inv \
	ctxAliasGameProbability_le_secretPrefix_add_inv_512; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_rom_auth" "modified CTX ROM theorem ${theorem_name}"
done
for theorem_name in ctxDigest_toList_length decodeRecord_romRecord \
	outerInput_take_key emptyCtxHandlerState_invariant; do
	require_line_count 1 "^@\[simp\] theorem ${theorem_name}( |$)" \
		"$ctx_rom_auth" "modified CTX ROM representation theorem ${theorem_name}"
done
for declaration in CtxRecordContext CtxSealInput CtxRomRecord CtxAliasTarget \
	CtxAdversary CtxSuccessfulSeal CtxHandlerState CtxBeforeVerify; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$ctx_rom_auth" "modified CTX ROM structure ${declaration}"
done
for declaration in FixedBytes CtxKey CtxNonce CtxDigest CtxRO CtxSealSpec \
	CtxAdversarySpec; do
	require_line_count 1 "^abbrev ${declaration}( |$)" \
		"$ctx_rom_auth" "modified CTX ROM type ${declaration}"
done
require_line_count 1 '^@\[inline, reducible\] def ctxRandomOracle( |$)' \
	"$ctx_rom_auth" "modified CTX lazy random-oracle implementation"
for declaration in CtxRomRecord.toRecordCipher CtxRomRecord.encode recordWf \
	outerInput ctxSeal emptyCtxHandlerState \
	CtxHandlerState.SealsMarkedUsed CtxHandlerState.UniqueSealNonces \
	CtxHandlerState.CacheProvenance CtxHandlerState.Invariant \
	CtxHandlerState.addPublic CtxHandlerState.addSeal \
	CtxAliasTarget.matchesSuccessfulSeal \
	CtxAliasTarget.sameFullTupleAsSuccessfulSeal \
	CtxFullAliasShape CtxBeforeVerify.targetInput CtxPublicTargetQueried \
	CtxSecretPrefixQueried CtxBeforeVerify.Invariant \
	CtxAcceptedFullAliasReplayAt; do
	require_line_count 1 "^def ${declaration//./\\.}( |$)" \
		"$ctx_rom_auth" "modified CTX ROM definition ${declaration}"
done
for declaration in ctxPublicOracle ctxSealOracle ctxAdversaryImpl \
	ctxBeforeVerifyInner ctxBeforeVerifyGame ctxFreshAliasVerifier \
	ctxFreshAliasGame ctxAliasGame ctxAliasTargetCacheHitProbability \
	ctxSecretPrefixQueriedProbability; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_rom_auth" "modified CTX ROM probability definition ${declaration}"
done

ctx_prefix_isolation=proofs/lean/BeaconcryptCore/Computational/CtxPrefixIsolation.lean
for theorem_name in \
	secretPrefixQuery_outerInput \
	withStickyBad_fst_map_run \
	withStickyBad_mono \
	withStickyBad_true \
	ctxRealWithPrefixFlagImpl_proj_step \
	ctxRealWithPrefixFlagImpl_proj_run \
	ctxReal_prefixIsolated_agree_good \
	ctxRealWithPrefixFlagImpl_bad_mono \
	ctxPrefixIsolatedImpl_bad_mono \
	withStickyBad_result_state \
	ctxPublicOracle_publicInputs \
	ctxSealOracle_publicInputs \
	ctxRealWithPrefixFlagImpl_preserves_prefix_flag \
	fullAliasShape_toBeforeVerify \
	secretPrefixQueried_toBeforeVerify \
	ctxRealWithPrefixFlag_run_prefix_flag \
	trackedProjection_realWithPrefixFlag_eq_ctxBeforeVerifyInner \
	ctxPrefixBadProbability_eq_secretPrefixQueriedProbabilityInner \
	tvDist_ctxReal_prefixIsolated_le_prefixBad \
	tvDist_ctxReal_prefixIsolated_le_secretPrefixQueried \
	tvDist_ctxBeforeVerifyInner_prefixIsolated_le_secretPrefixQueried \
	ctxSecretPrefixQueriedProbability_toReal_eq_tsum \
	tvDist_ctxBeforeVerifyGame_prefixIsolatedGame_le_secretPrefixQueried; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_prefix_isolation" "modified CTX prefix-isolation theorem ${theorem_name}"
done
require_line_count 1 '^@\[simp\] theorem emptyCtxPrefixFlagInvariant( |$)' \
	"$ctx_prefix_isolation" "modified CTX prefix-isolation empty-state invariant"
require_line_count 1 '^instance \(key : CtxKey\) : DecidablePred \(SecretPrefixQuery key\) :=$' \
	"$ctx_prefix_isolation" "modified CTX prefix-query decidability instance"
for declaration in SecretPrefixQuery withStickyBad CtxPrefixFlagInvariant \
	handlerStateToBeforeVerify trackedProjection; do
	require_line_count 1 "^def ${declaration}( |$)" \
		"$ctx_prefix_isolation" "modified CTX prefix-isolation definition ${declaration}"
done
for declaration in ctxPrefixIsolatedPublic ctxRealWithPrefixFlagImpl \
	ctxPrefixIsolatedImpl ctxRealWithPrefixFlagBeforeVerify \
	ctxPrefixIsolatedFlaggedBeforeVerify ctxPrefixBadProbability \
	ctxSecretPrefixQueriedProbabilityInner ctxPrefixIsolatedBeforeVerifyInner \
	ctxPrefixIsolatedGame; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_prefix_isolation" "modified CTX prefix-isolation game definition ${declaration}"
done

ctx_split_cache=proofs/lean/BeaconcryptCore/Computational/CtxSplitCache.lean
for theorem_name in \
	outerInput_eq_secretAddress_outerSuffix \
	outerSuffix_length \
	secretAddress_secretSuffix \
	secretSuffix_outerInput \
	splitCtxCache_normalized \
	splitCtxCache_lookup \
	merge_splitCtxCache \
	splitCtxCache_merge; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_split_cache" "modified CTX split-cache theorem ${theorem_name}"
done
for theorem_name in secretPrefixQuery_secretAddress secretSuffix_secretAddress \
	splitCtxCache_empty; do
	require_line_count 1 "^@\[simp\] theorem ${theorem_name}( |$)" \
		"$ctx_split_cache" "modified CTX split-cache simplification theorem ${theorem_name}"
done
require_line_count 1 '^abbrev CtxSuffixRO( |$)' \
	"$ctx_split_cache" "modified CTX suffix-oracle type"
require_line_count 1 '^@\[ext\] structure SplitCache( |$)' \
	"$ctx_split_cache" "modified CTX split-cache structure"
for declaration in secretSuffix secretAddress outerSuffix SplitCache.lookup \
	SplitCache.merge splitCtxCache SplitCache.Normalized; do
	require_line_count 1 "^def ${declaration//./\\.}( |$)" \
		"$ctx_split_cache" "modified CTX split-cache definition ${declaration}"
done

ctx_seal_sampling=proofs/lean/BeaconcryptCore/Computational/CtxSealSampling.lean
for theorem_name in ctxSeal_query_fresh_of_good_unused \
	ctxSealOracle_eq_directSample_of_good; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_seal_sampling" "modified CTX fresh seal-sampling theorem ${theorem_name}"
done
require_line_count 1 '^noncomputable def ctxDirectSampleSealOracle( |$)' \
	"$ctx_seal_sampling" "modified CTX direct-sampling seal transition"

ctx_independent_tags=proofs/lean/BeaconcryptCore/Computational/CtxIndependentTags.lean
require_line_count 1 '^structure CtxIndependentTagState( |$)' \
	"$ctx_independent_tags" "modified CTX independent-tag handler state"
for theorem_name in \
	splitCtxCache_cacheQuery_prefix \
	splitCtxCache_cacheQuery_public \
	splitCtxCache_cacheQuery \
	ctxRandomOracle_split_projection \
	ctxSplitRandomOracle_outerInput_eq_keyFreeSuffix \
	ctxPublicOracle_split_projection \
	ctxSealOracle_split_projection \
	ctxAdversaryImpl_split_projection_step \
	ctxAdversaryImpl_split_projection_run \
	withStickyBad_projection \
	ctxRealWithPrefixFlagImpl_split_projection_step \
	ctxRealWithPrefixFlagImpl_split_projection_run \
	ctxSplitRoutedPublicOracle_eq_independent_of_not_prefix \
	ctxSplitRouted_independent_agree_good \
	ctxSplitRoutedWithPrefixFlagImpl_bad_mono \
	ctxIndependentWithPrefixFlagImpl_bad_mono \
	ctxSplitRouted_badProbability_eq_prefixBad \
	tvDist_ctxSplitRouted_independentTag_le_prefixBad \
	ctxSplitRoutedWithPrefixFlagImpl_proj_step \
	ctxIndependentWithPrefixFlagImpl_proj_step \
	ctxSplitRoutedWithPrefixFlagImpl_proj_run \
	ctxIndependentWithPrefixFlagImpl_proj_run \
	independentFlaggedProjection_splitRouted \
	independentFlaggedProjection_independent \
	tvDist_ctxSplitRoutedBeforeVerifyInner_independentTag_le_secretPrefixQueried \
	ctxSplitRoutedBeforeVerifyInner_eq_ctxSplitBeforeVerifyInner \
	tvDist_ctxSplitBeforeVerifyInner_independentTag_le_secretPrefixQueried \
	tvDist_ctxSplitBeforeVerifyGame_independentTagGame_le_secretPrefixQueried; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_independent_tags" "modified CTX independent-tag theorem ${theorem_name}"
done
for theorem_name in merge_splitHandlerState splitHandlerState_empty \
	splitHandlerState_addPublic splitHandlerState_addSeal; do
	require_line_count 1 "^@\[simp\] theorem ${theorem_name}( |$)" \
		"$ctx_independent_tags" "modified CTX independent-tag simplification theorem ${theorem_name}"
done
for declaration in splitHandlerState CtxIndependentTagState.merge \
	emptyCtxIndependentTagState splitFlaggedHandlerState cachePublic cacheSuffix \
	cacheCanonical CtxIndependentTagState.addPublic CtxIndependentTagState.addSeal \
	independentHandlerStateToBeforeVerify independentTrackedProjection \
	independentFlaggedProjection splitBeforeVerifyProjection; do
	require_line_count 1 "^def ${declaration//./\\.}( |$)" \
		"$ctx_independent_tags" "modified CTX independent-tag definition ${declaration}"
done
for declaration in ctxKeyFreeSuffixStep ctxSplitRandomOracle \
	ctxKeyFreeSuffixOracle ctxSplitRoutedPublicOracle ctxIndependentPublicOracle \
	ctxKeyFreeSealOracle ctxSplitRoutedImpl ctxIndependentTagImpl \
	ctxSplitRoutedWithPrefixFlagImpl ctxIndependentWithPrefixFlagImpl \
	ctxSplitRoutedFlaggedBeforeVerify ctxIndependentTagFlaggedBeforeVerify \
	ctxSplitRoutedBeforeVerifyInner ctxIndependentTagBeforeVerifyInner \
	ctxSplitBeforeVerifyInner ctxSplitBeforeVerifyGame ctxIndependentTagGame; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_independent_tags" "modified CTX independent-tag game definition ${declaration}"
done
require_line_count 1 '^@\[inline, reducible\] noncomputable def ctxSuffixRandomOracle( |$)' \
	"$ctx_independent_tags" "modified CTX suffix random-oracle implementation"

ctx_honest_tag_sampling=proofs/lean/BeaconcryptCore/Computational/CtxHonestTagSampling.lean
for theorem_name in \
	outerSuffix_eq_implies_nonce_eq \
	outerSuffix_fresh_of_unused \
	ctxKeyFreeSeal_suffix_fresh_of_unused \
	ctxKeyFreeSealOracle_eq_directSample_of_invariant \
	cacheSuffix_origin \
	ctxIndependentPublicOracle_preserves_invariant \
	ctxDirectSampleKeyFreeSealOracle_preserves_invariant \
	ctxDirectSampleIndependentTagImpl_preserves_invariant \
	ctxIndependentTagImpl_eq_directSample_step_of_invariant \
	ctxDirectSampleIndependentTag_run_invariant \
	ctxIndependentTagImpl_run_eq_directSample \
	ctxDirectSampleIndependentTag_run_unique_seal_nonces \
	ctxIndependentTagBeforeVerifyInner_eq_directSample \
	ctxIndependentTagGame_eq_directSampleIndependentTagGame \
	tvDist_ctxSplitBeforeVerifyGame_directSampleIndependentTagGame_le_secretPrefixQueried; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_honest_tag_sampling" "modified CTX honest-tag sampling theorem ${theorem_name}"
done
for theorem_name in outerSuffix_take_nonce emptyCtxIndependentTagState_invariant; do
	require_line_count 1 "^@\[simp\] theorem ${theorem_name}( |$)" \
		"$ctx_honest_tag_sampling" "modified CTX honest-tag simplification theorem ${theorem_name}"
done
for declaration in CtxIndependentTagStateSealsMarkedUsed \
	CtxIndependentTagStateUniqueSealNonces \
	CtxIndependentTagStateSuffixCacheProvenance \
	CtxIndependentTagStateInvariant; do
	require_line_count 1 "^def ${declaration}( |$)" \
		"$ctx_honest_tag_sampling" "modified CTX honest-tag invariant ${declaration}"
done
for declaration in ctxDirectSampleKeyFreeSealOracle \
	ctxDirectSampleIndependentTagImpl \
	ctxDirectSampleIndependentTagBeforeVerifyInner \
	ctxDirectSampleIndependentTagGame; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_honest_tag_sampling" "modified CTX direct honest-tag game ${declaration}"
done

ctx_nonce_aead_int_ctxt=proofs/lean/BeaconcryptCore/Computational/CtxNonceAeadIntCtxt.lean
for declaration in ModifiedNonceAeadSealInput ModifiedNonceAeadCiphertext \
	ModifiedNonceAeadSuccessfulSeal ModifiedNonceAeadForgery \
	ModifiedNonceAeadAdversary ModifiedNonceAeadHandlerState \
	ModifiedNonceAeadBeforeVerify; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$ctx_nonce_aead_int_ctxt" "modified nonce-AEAD INT-CTXT structure ${declaration}"
done
for declaration in ModifiedNonceAeadSealSpec ModifiedNonceAeadAdversarySpec; do
	require_line_count 1 "^abbrev ${declaration}( |$)" \
		"$ctx_nonce_aead_int_ctxt" "modified nonce-AEAD INT-CTXT abbreviation ${declaration}"
done
for declaration in emptyModifiedNonceAeadHandlerState \
	ModifiedNonceAeadHandlerState.addSeal ModifiedNonceAeadFresh \
	ModifiedNonceAeadINTCTXTWin CtxSealInput.toModifiedNonceAeadSealInput \
	CtxRomRecord.toModifiedNonceAeadCiphertext \
	CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal \
	CtxAliasTarget.toModifiedNonceAeadForgery ctxBeforeVerifyToModifiedNonceAead \
	CtxFreshAcceptedRetainedBase ctxIndependentTagStateToModifiedNonceAead \
	queryModifiedNonceAeadSeal IsCtxSealQuery IsModifiedNonceAeadSealQuery \
	ModifiedNonceAeadAdversary.MakesAtMostSealQueries; do
	require_line_count 1 "^def ${declaration//./\\.}( |$)" \
		"$ctx_nonce_aead_int_ctxt" "modified nonce-AEAD INT-CTXT definition ${declaration}"
done
for declaration in modifiedNonceAeadSealOracle modifiedNonceAeadINTCTXTImpl \
	modifiedNonceAeadINTCTXTBeforeVerifyInner modifiedNonceAeadINTCTXTGame \
	modifiedNonceAeadINTCTXTAdvantage modifiedNonceAeadDigest \
	ctxRetainedBasePublicOracle ctxRetainedBaseSealOracle \
	ctxRetainedBaseReductionImpl ctxRetainedBaseReduction \
	ctxRetainedBaseCombinedImpl; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_nonce_aead_int_ctxt" "modified nonce-AEAD INT-CTXT game definition ${declaration}"
done
for theorem_name in modifiedNonceAeadSealOracle_run \
	modifiedNonceAeadSealOracle_run_ctx \
	ctxFreshAcceptedRetainedBase_implies_modifiedNonceAeadINTCTXTWin \
	liftProbComp_no_modifiedNonceAeadSealQueries \
	ctxRetainedBaseReductionImpl_seal_query_bound_step \
	ctxRetainedBaseReduction_seal_query_bound \
	simulateQ_queryModifiedNonceAeadSeal simulateQ_modifiedNonceAeadDigest \
	map_lift_ctxDigest_run map_lift_ctxDigest_apply \
	ctxRetainedBasePublicOracle_projection \
	ctxRetainedBaseSealOracle_projection \
	ctxRetainedBaseCombinedImpl_projection \
	ctxRetainedBaseCombinedImpl_run_projection \
	ctxRetainedBaseNestedRun_eq_direct ctxRetainedBaseReduction_run_eq_direct \
	modifiedNonceAeadINTCTXTBeforeVerifyInner_reduction_eq_direct \
	modifiedNonceAeadINTCTXTGame_reduction_eq_direct \
	ctxFreshAcceptedRetainedBaseProbability_le_intCtxtAdvantage; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_nonce_aead_int_ctxt" "modified nonce-AEAD INT-CTXT theorem ${theorem_name}"
done
for theorem_name in toModifiedNonceAeadSealInput_nonce \
	toModifiedNonceAeadSealInput_ad toModifiedNonceAeadSealInput_plaintext; do
	require_line_count 1 "^@\[simp\] theorem ${theorem_name}( |$)" \
		"$ctx_nonce_aead_int_ctxt" "modified nonce-AEAD INT-CTXT simplification theorem ${theorem_name}"
done

ctx_nonce_aead_ind_dollar=proofs/lean/BeaconcryptCore/Computational/CtxNonceAeadIndDollar.lean
require_line_count 1 '^abbrev CtxKeyProbes( |$)' \
	"$ctx_nonce_aead_ind_dollar" "modified nonce-AEAD key-probe vector"
for declaration in CtxQueryBoundedAdversary \
	ModifiedNonceAeadINDDollarProbeAdversary; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$ctx_nonce_aead_ind_dollar" "modified nonce-AEAD key-probe structure ${declaration}"
done
for declaration in CtxKeyProbeHit ctxPrefixProbeVector \
	CtxIndependentPrefixFlagInvariant IsCtxPublicQuery \
	ModifiedNonceAeadINDDollarProbeAdversary.MakesAtMostSealQueries; do
	require_line_count 1 "^def ${declaration//./\\.}( |$)" \
		"$ctx_nonce_aead_ind_dollar" "modified nonce-AEAD key-probe definition ${declaration}"
done
require_line_count 1 '^def prefixCandidate\?( |$)' \
	"$ctx_nonce_aead_ind_dollar" "modified nonce-AEAD key-probe prefix candidate definition"
for declaration in ctxIndependentPublicPrefixProbability \
	ctxDirectSamplePublicPrefixProbability \
	ctxPrefixToModifiedNonceAeadINDDollarReduction \
	modifiedNonceAeadINDDollarRandomSealOracle \
	modifiedNonceAeadINDDollarRandomImpl \
	modifiedNonceAeadINDDollarRealProbeExp \
	modifiedNonceAeadINDDollarRandomProbeExp \
	modifiedNonceAeadINDDollarProbeAdvantage \
	ctxDirectSamplePrefixProbeExpInner \
	modifiedNonceAeadINDDollarRealProbeExpInner \
	ctxDirectSamplePrefixProbeExp; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_nonce_aead_ind_dollar" "modified nonce-AEAD key-probe game definition ${declaration}"
done
for theorem_name in ctxPrefixProbeVector_hit_of_prefix \
	ctxPrefixProbeVector_prefix_of_hit \
	ctxPrefixProbeVector_hit_iff_of_length_le \
	ctxIndependent_badProbability_eq_prefixBad \
	ctxIndependentPublicOracle_publicInputs ctxKeyFreeSealOracle_publicInputs \
	ctxIndependentWithPrefixFlagImpl_preserves_prefix_flag \
	ctxIndependentTagFlagged_run_prefix_flag \
	ctxIndependent_badProbability_eq_publicPrefix \
	ctxDirectSampleKeyFreeSealOracle_publicInputs \
	ctxDirectSampleIndependentTagImpl_publicInputs_length_step \
	ctxDirectSampleIndependentTag_run_publicInputs_length_le \
	ctxDirectSampleIndependentTag_run_publicInputs_length_le_qH \
	ctxIndependentPublicPrefixProbability_eq_directSample \
	ctxSecretPrefixQueriedProbabilityInner_eq_directSamplePublicPrefix \
	ctxPrefixToModifiedNonceAeadINDDollarReduction_seal_query_bound \
	isTotalQueryBound_of_ctx_public_and_seal_bounds \
	CtxQueryBoundedAdversary.totalQueryBound ctxKey_card \
	probEvent_uniformKey_probeHit_le modifiedNonceAeadINDDollarRandomProbe_le \
	ctxDirectSamplePrefixProbeExpInner_probability \
	ctxPrefixReduction_realProbeExpInner_eq_directSample \
	ctxSecretPrefixQueriedProbability_eq_directSampleProbe \
	modifiedNonceAeadINDDollarRealProbeExp_reduction_eq_directSample \
	ctxSecretPrefixQueriedProbability_eq_realProbeReduction \
	ctxSecretPrefixQueriedProbability_le_modifiedNonceAeadINDDollar; do
	require_line_count 1 "^theorem ${theorem_name//./\\.}( |$)" \
		"$ctx_nonce_aead_ind_dollar" "modified nonce-AEAD key-probe theorem ${theorem_name}"
done
require_line_count 1 '^theorem prefixCandidate\?_eq_some_iff( |$)' \
	"$ctx_nonce_aead_ind_dollar" "modified nonce-AEAD key-probe prefix-candidate equivalence"
require_line_count 1 '^@\[simp\] theorem emptyCtxIndependentPrefixFlagInvariant( |$)' \
	"$ctx_nonce_aead_ind_dollar" "modified nonce-AEAD key-probe empty-state invariant"

ctx_nonce_aead_ind_dollar_validation=proofs/lean/BeaconcryptCore/Computational/CtxNonceAeadIndDollarValidation.lean
require_line_count 1 '^structure ModifiedNonceAeadINDDollarAdversary( |$)' \
	"$ctx_nonce_aead_ind_dollar_validation" "conventional modified nonce-AEAD IND-dollar adversary"
for declaration in ctxValidationInput ctxValidationTag \
	ctxValidationTagProbeVector CtxValidationTagHit \
	modifiedNonceAeadCiphertextTag CtxValidationCiphertextHit; do
	require_line_count 1 "^def ${declaration}( |$)" \
		"$ctx_nonce_aead_ind_dollar_validation" "conventional IND-dollar validation definition ${declaration}"
done
for declaration in modifiedNonceAeadINDDollarRealExp \
	modifiedNonceAeadINDDollarRandomExp modifiedNonceAeadINDDollarAdvantage \
	ctxValidationAccept ctxPrefixToBooleanINDDollarReduction \
	modifiedNonceAeadINDDollarRealExpInner; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_nonce_aead_ind_dollar_validation" "conventional IND-dollar game definition ${declaration}"
done
for theorem_name in ctxNonce_card chooseFreshCtxNonce_not_mem \
	ctxDirectSampleIndependentTag_run_usedNonces_length_le_qE \
	chooseFreshCtxNonce_fresh_of_direct_support \
	ctxPrefixToBooleanINDDollarReduction_seal_query_bound \
	ctxPrefixBooleanReduction_random_le \
	ctxSecretPrefixQueriedProbability_le_booleanReal \
	ctxSecretPrefixQueriedProbability_le_booleanINDDollar; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_nonce_aead_ind_dollar_validation" "conventional IND-dollar theorem ${theorem_name}"
done

ctx_computational_security=proofs/lean/BeaconcryptCore/Computational/CtxComputationalSecurity.lean
require_line_count 1 '^structure CtxComputationalQueryAccounting( |$)' \
	"$ctx_computational_security" "modified-CTX composed query-accounting record"
for declaration in CtxClassifiedForgeryAt CtxTypedFullFresh \
	CtxAcceptedTypedFullFreshAt CtxHonestCommitmentsCached \
	CtxIndependentTagStateCommitmentsCached IsModifiedNonceAeadUniformQuery; do
	require_line_count 1 "^def ${declaration}( |$)" \
		"$ctx_computational_security" "modified-CTX final definition ${declaration}"
done
for declaration in ctxClassifiedVerifier ctxClassifiedForgeryGame \
	ctxDirectClassifiedForgeryGame ctxTypedFullFreshVerifier \
	ctxTypedFullFreshForgeryGame ctxDirectTypedFullFreshForgeryGame; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_computational_security" "modified-CTX final game definition ${declaration}"
done
for theorem_name in ctxDirectSampleIndependentTagGame_commitmentsCached \
	acceptedTypedFullFreshAt_implies_classified_of_cache_sound \
	ctxDirectSample_alias_suffix_fresh \
	ctxTypedFullFreshForgeryGame_le_direct_add_prefix \
	ctxTypedFullFreshForgeryProbability_le_intCtxt_add_prefix_add_inv \
	ctxTypedFullFreshForgeryProbability_le_intCtxt_add_indDollar_add_guesses \
	ctxTypedFullFreshForgeryProbability_le_intCtxt_add_booleanIndDollar_add_guesses \
	ctxRetainedBaseReduction_uniform_query_bound \
	ctxRetainedBaseReduction_total_query_bound \
	ctxPrefixToModifiedNonceAeadINDDollarReduction_uniform_query_bound \
	ctxPrefixToModifiedNonceAeadINDDollarReduction_total_query_bound \
	ctxPrefixToBooleanINDDollarReduction_uniform_query_bound \
	ctxPrefixToBooleanINDDollarReduction_total_query_bound \
	ctxDirectTypedFullFreshForgeryGame_total_query_bound \
	ctxComputationalSecurity_query_accounting; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_computational_security" "modified-CTX final theorem ${theorem_name}"
done

ctx_computational_privacy=proofs/lean/BeaconcryptCore/Computational/CtxComputationalPrivacy.lean
for declaration in CtxPrivacyAdversary CtxPrivacyQueryAccounting; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$ctx_computational_privacy" "modified-CTX privacy structure ${declaration}"
done
for declaration in ctxPrivacyRealGame ctxPrivacyIdealGame ctxPrivacyViewReduction \
	ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction \
	ctxPrivacyPrefixToBooleanINDDollarReduction; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_computational_privacy" "modified-CTX privacy game or reduction ${declaration}"
done
for theorem_name in \
	modifiedNonceAeadINDDollarRandomExp_viewReduction_eq_idealGame \
	modifiedNonceAeadINDDollarRealExp_viewReduction_eq_directSampleGame \
	ofReal_ctxPrivacyAdvantage_le_viewAdvantage_add_secretPrefix \
	ctxPrivacyAdvantage_le_viewINDDollar_add_probeINDDollar \
	ctxPrivacyAdvantage_le_viewINDDollar_add_booleanINDDollar \
	ctxPrivacy_query_accounting; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_computational_privacy" "modified-CTX privacy theorem ${theorem_name}"
done
require_line_count 3 '^#guard_msgs in$' \
	"$ctx_computational_privacy" \
	"modified-CTX privacy guarded axiom audits"
for theorem_name in \
	modifiedNonceAeadINDDollarRandomExp_viewReduction_eq_idealGame \
	ctxPrivacyAdvantage_le_viewINDDollar_add_probeINDDollar \
	ctxPrivacyAdvantage_le_viewINDDollar_add_booleanINDDollar; do
	require_line_count 1 "^#print axioms ${theorem_name}$" \
		"$ctx_computational_privacy" \
		"modified-CTX privacy axiom audit ${theorem_name}"
done

for theorem_name in serverRegister_refines beaconFinishDriver_refines; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		proofs/lean/BeaconcryptCore/Refinement/PqxdhProtocol.lean \
		"PQXDH protocol-refinement theorem ${theorem_name}"
done
require_line_count 1 '^theorem honest_run_refines( |$)' \
	proofs/lean/BeaconcryptCore/Refinement/PqxdhSession.lean \
	"PQXDH session-refinement theorem honest_run_refines"

# The imported phase-refinement layer covers the full kernel/cache relation, the KDF response law, non-exhausted successful-send refinement, all neutral exits, supplied finite failed-trace witnesses, and the conditional open reply/material relation.
# Cached success has generated open construction, exact material/reply, ideal outcome, and control refinement. RatchetCachedPublication now discharges its material publication premise; complete future success remains in progress.
for declaration in KernelRefines SendKdfRefines SendSealRefines; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		proofs/lean/BeaconcryptCore/Refinement/RatchetEffectRefinement.lean \
		"effect-refinement relation ${declaration}"
done
for declaration in ResponseRefines idealOpenReply OpenReplyRefines CachedOpenRefines CachedPublicationRefines; do
	require_line_count 1 "^def ${declaration}( |$)" \
		proofs/lean/BeaconcryptCore/Refinement/RatchetEffectRefinement.lean \
		"effect-refinement relation ${declaration}"
done
require_line_count 1 '^inductive ReceiveFailureTrace( |\(|$)' \
	proofs/lean/BeaconcryptCore/Refinement/RatchetEffectRefinement.lean \
	"represented finite failed receive trace relation"
for theorem_name in \
	SendKdf.cancel_preserves_refinement \
	ReceiveKdf.cancel_preserves_refinement \
	ReceiveOpen.reject_preserves_refinement \
	ReceiveOpen.failure_preserves_refinement \
	begin_send_refines \
	SendKdf.resume_refines \
	SendSeal.finish_refines_ideal_send \
	ReceiveFailureTrace.result_eq_entry \
	ReceiveFailureTrace.preserves_refinement \
	OpenReplyRefines.some_implies_ideal_decryption \
	begin_receive_cached_refines \
	CachedOpenRefines.material_exact \
	CachedOpenRefines.openReply_some \
	CachedOpenRefines.ideal_success \
	ratchet.control.Refines.finish_receive_with_removal_consumed_refines \
	CachedOpenRefines.finish_success_matches_ideal \
	CachedOpenRefines.finish_success_refines_of_publication; do
	require_line_count 1 "^theorem ${theorem_name//./\\.}( |$)" \
		proofs/lean/BeaconcryptCore/Refinement/RatchetEffectRefinement.lean \
		"effect-refinement theorem ${theorem_name}"
done

require_line_count 1 '^let commitment_transcript_is_exact' \
	proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst \
	"exact production commitment transcript lemma"
require_line_count 1 '^let commitment_transcript_integer_fields_are_le64' \
	proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst \
	"production commitment integer-encoding lemma"
require_line_count 1 '^let encode_u64_le_is_injective' \
	proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst \
	"injective production LE64 encoding lemma"
require_line_count 1 '^let production_commitment_input_is_injective' \
	proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst \
	"injective six-field production commitment lemma"
require_line_count 1 '^type t_HashCollisionWitness' \
	proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst \
	"CTX hash-collision witness type"
require_line_count 1 '^let ctx_distinct_openings_imply_hash_collision' \
	proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst \
	"CTX distinct-opening collision extractor"

reject_matches "unreviewed generated F* exception" \
	'\b(?:while_loop_return|to_le_bytes|assume|admit)\b' \
	proofs/fstar/extraction --glob '*.fst' --glob '*.fsti'

printf 'Formal-verification inventory matches the reviewed boundary.\n'
