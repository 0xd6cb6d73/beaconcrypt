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
	[[ "$category" =~ ^(adapter-rust|adapter-schema|core-rust|control|generated-lean|generated-proverif|handwritten-lean|handwritten-proverif|historical-generated-fstar|historical-handwritten-fstar|inventory|lean-control|validation)$ ]] ||
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
	[generated-lean]=3
	[generated-proverif]=1
	[handwritten-lean]=28
	[handwritten-proverif]=18
	[historical-generated-fstar]=5
	[historical-handwritten-fstar]=8
	[inventory]=2
	[lean-control]=8
	[validation]=2
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

find proofs/fstar/extraction -type f \
	\( -name '*.fst' -o -name '*.fsti' \) \
	-printf '%p\n' > "$tmp_dir/historical-generated-fstar"
compare_set historical-generated-fstar "$tmp_dir/historical-generated-fstar"

find proofs/pro-verif/extraction -type f \
	\( -name '*.pv' -o -name '*.pvl' \) -printf '%p\n' > "$tmp_dir/generated-proverif"
compare_set generated-proverif "$tmp_dir/generated-proverif"

find proofs/lean/BeaconcryptCore/Extraction -maxdepth 1 -type f \
	\( -name 'Funs.lean' -o -name 'Types.lean' -o -name '*_Template.lean' \) \
	-printf '%p\n' > "$tmp_dir/generated-lean"
compare_set generated-lean "$tmp_dir/generated-lean"

printf '%s\n' \
	proofs/lean/BeaconcryptCore.lean \
	proofs/lean/BeaconcryptCore/Extraction/FunsExternal.lean \
	> "$tmp_dir/handwritten-lean"
for lean_proof_dir in Model Refinement Computational; do
	find "proofs/lean/BeaconcryptCore/$lean_proof_dir" -type f -name '*.lean' \
		-printf '%p\n' >> "$tmp_dir/handwritten-lean"
done
compare_set handwritten-lean "$tmp_dir/handwritten-lean"

printf '%s\n' \
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
require_line_count 19 '^reduc ' "$generated_proverif" \
	"generated ProVerif reduction"
require_occurrence_count 11 'construct_fail\(\)' \
	"generated ProVerif construct_fail" "$generated_proverif"

mapfile -t handwritten_proverif < <(
	awk -F '\t' '$1 == "handwritten-proverif" && $3 ~ /\.(pv|pvl)$/ { print $3 }' "$manifest"
)
reject_matches "handwritten ProVerif uses a forbidden generated helper" \
	'(construct_fail|_from_bitstring|_default_value|_(?:default|err)\s*\(|nat_to_bitstring)' \
	"${handwritten_proverif[@]}"
require_occurrence_count 3 \
	'beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring' \
	"allowed generated ProVerif converter" "${handwritten_proverif[@]}"
require_occurrence_count 3 '_to_bitstring' \
	"all handwritten generated ProVerif converters" "${handwritten_proverif[@]}"

require_line_count 31 '^fun ' proofs/pro-verif/crypto.pvl \
	"handwritten primitive constructor/function"
require_line_count 6 '^reduc ' proofs/pro-verif/crypto.pvl \
	"handwritten primitive reduction"
require_line_count 1 '^letfun ' proofs/pro-verif/crypto.pvl \
	"handwritten primitive helper"
require_line_count 24 '^event ' proofs/pro-verif/environment.pvl \
	"handwritten event"
require_line_count 2 '^table ' proofs/pro-verif/environment.pvl \
	"handwritten table"
require_line_count 17 '^free ' proofs/pro-verif/environment.pvl \
	"handwritten free name/channel"
require_line_count 12 '^let [A-Z]' proofs/pro-verif/environment.pvl \
	"handwritten process"
require_line_count 11 '^query ' proofs/pro-verif/queries.pvl \
	"baseline query"
require_line_count 7 '^query ' proofs/pro-verif/reachability-queries.pvl \
	"reachability query"
require_line_count 5 '^query ' proofs/pro-verif/compromise-queries.pvl \
	"compromise query"
require_line_count 17 '^query ' proofs/pro-verif/failed-receive-queries.pvl \
	"state-neutral receive query"
require_line_count 12 '^query ' \
	proofs/pro-verif/failed-receive-reachability-queries.pvl \
	"state-neutral receive reachability query"
require_line_count 9 '^query ' \
	proofs/pro-verif/failed-receive-compromise-queries.pvl \
	"state-neutral receive compromise query"
require_line_count 2 '^query ' \
	proofs/pro-verif/failed-receive-compromise-reachability-queries.pvl \
	"state-neutral receive compromise reachability query"
require_line_count 1 '^query ' \
	proofs/pro-verif/aead-commitment-negative-control-queries.pvl \
	"AEAD commitment negative-control query"
require_line_count 1 '^event ' \
	proofs/pro-verif/aead-commitment-negative-control.pvl \
	"AEAD commitment negative-control event"
require_line_count 2 '^let [A-Z]' \
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
	"cargo\\s+hax\\s+-C\\s+--locked\\s+';'\\s+into\\s+lean\\s+--lakefile" \
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

cmp -s proofs/lean/BeaconcryptCore/Extraction/FunsExternal_Template.lean \
	proofs/lean/BeaconcryptCore/Extraction/FunsExternal.lean ||
	fail "maintained Lean externals differ from the reviewed generated template"
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
for pqxdh_root_module in Instance InstanceCommit Acceptance Runs; do
	require_line_count 1 "^import BeaconcryptCore\\.Model\\.Pqxdh\\.${pqxdh_root_module}$" \
		"$lean_root" "canonical ideal PQXDH ${pqxdh_root_module} proof-root import"
done
require_line_count 1 '^import BeaconcryptCore\.Computational\.VCVioFeasibility$' \
	"$lean_root" \
	"canonical VCVio feasibility proof-root import"
require_line_count 1 '^import BeaconcryptCore\.Computational\.CtxReduction$' \
	"$lean_root" \
	"canonical CTX reduction proof-root import"
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
	proofs/lean/BeaconcryptCore/Model proofs/lean/BeaconcryptCore/Refinement

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
	ctxAcceptedFullFreshForgeryProbability_le_projection_add_alias; do
	require_line_count 1 "^theorem ${theorem_name}( |$)" \
		"$ctx_auth_classification" "general CTX authenticity classification theorem ${theorem_name}"
done
for declaration in CtxSealHistoryEntry CtxAuthClassificationAttempt; do
	require_line_count 1 "^structure ${declaration}( |$)" \
		"$ctx_auth_classification" "general CTX authenticity structure ${declaration}"
done
for declaration in CtxFullFresh CtxBaseProjectionMatch CtxBaseProjectionFresh \
	CtxAcceptedFullFreshForgery CtxFreshAcceptedBaseProjection CtxContextAliasReplay; do
	require_line_count 1 "^def ${declaration}( |$)" \
		"$ctx_auth_classification" "general CTX authenticity definition ${declaration}"
done
for declaration in CtxSealHistoryEntry.ctxOutput CtxSealHistoryEntry.baseOutput; do
	require_line_count 1 "^def ${declaration//./\\.}( |$)" \
		"$ctx_auth_classification" "general CTX authentication output ${declaration}"
done
for declaration in ctxAcceptedFullFreshForgeryProbability \
	ctxFreshAcceptedBaseProjectionProbability ctxContextAliasReplayProbability; do
	require_line_count 1 "^noncomputable def ${declaration}( |$)" \
		"$ctx_auth_classification" "general CTX authentication probability ${declaration}"
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
# Cached success additionally has generated open construction from KernelRefines plus an ideal lookup, exact material/reply, direct ideal outcome, concrete finish output, and the consumed control-cache refinement; its material-array post-state KernelRefines result remains conditional on CachedPublicationRefines, and future success remains unproved.
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
