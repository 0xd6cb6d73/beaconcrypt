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
	[[ "$category" =~ ^(adapter-rust|adapter-schema|core-rust|control|generated-fstar|generated-proverif|handwritten-fstar|handwritten-proverif|inventory|validation)$ ]] ||
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
	[generated-fstar]=7
	[generated-proverif]=1
	[handwritten-fstar]=10
	[handwritten-proverif]=18
	[inventory]=2
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

symlink_path="$(find "$adapter_dir/src" "$core_dir/src" "$core_dir/proofs" -type l -print -quit)"
[[ -z "$symlink_path" ]] || fail "symlink in monitored tree: $symlink_path"

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

awk -F '\t' '$3 ~ /^proofs\// { print $3 }' "$manifest" \
	> "$tmp_dir/expected-all-proof-files"
printf '%s\n' "$manifest" >> "$tmp_dir/expected-all-proof-files"
find proofs -mindepth 1 \( -type f -o -type l \) -printf '%p\n' \
	> "$tmp_dir/all-proof-files"
LC_ALL=C sort -u -o "$tmp_dir/expected-all-proof-files" \
	"$tmp_dir/expected-all-proof-files"
LC_ALL=C sort -u -o "$tmp_dir/all-proof-files" "$tmp_dir/all-proof-files"
if ! cmp -s "$tmp_dir/expected-all-proof-files" "$tmp_dir/all-proof-files"; then
	printf 'reviewed proof/control file set changed:\n' >&2
	diff -u "$tmp_dir/expected-all-proof-files" "$tmp_dir/all-proof-files" >&2 || true
	fail "unreviewed file under proofs"
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
	-printf '%p\n' > "$tmp_dir/handwritten-fstar"
compare_set handwritten-fstar "$tmp_dir/handwritten-fstar"

find proofs/pro-verif -type f \
	\( -name '*.pv' -o -name '*.pvl' -o -name '*.awk' \) \
	! -path 'proofs/pro-verif/extraction/*' \
	-printf '%p\n' > "$tmp_dir/handwritten-proverif"
compare_set handwritten-proverif "$tmp_dir/handwritten-proverif"

find proofs/fstar/extraction -type f \
	\( -name '*.fst' -o -name '*.fsti' \) -printf '%p\n' > "$tmp_dir/generated-fstar"
compare_set generated-fstar "$tmp_dir/generated-fstar"

find proofs/pro-verif/extraction -type f \
	\( -name '*.pv' -o -name '*.pvl' \) -printf '%p\n' > "$tmp_dir/generated-proverif"
compare_set generated-proverif "$tmp_dir/generated-proverif"

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
require_occurrence_count 4 \
	'hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"[^"]*noeq[^"]*"\s*\)' \
	"reviewed F* noeq insertion" src
require_occurrence_count 14 \
	'hax_lib\s*::\s*fstar\s*::\s*before\s*\(' \
	"complete F* before-annotation allowlist" src
require_occurrence_count 8 \
	'hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"#push-options \\"--fuel 1 --ifuel 1 --z3rlimit 60\\""\s*\)' \
	"reviewed loop-reference F* option scope" src
require_occurrence_count 8 \
	'hax_lib\s*::\s*fstar\s*::\s*after\s*\(' \
	"complete F* after-annotation allowlist" src
require_occurrence_count 8 \
	'hax_lib\s*::\s*fstar\s*::\s*after\s*\(\s*"#pop-options"\s*\)' \
	"reviewed loop-reference F* option scope end" src
require_occurrence_count 8 \
	'hax_lib\s*::\s*ensures\s*\(' \
	"reviewed loop-reference postcondition" src
require_occurrence_count 4 \
	'hax_lib\s*::\s*loop_invariant!' \
	"reviewed iterative-loop invariant" src
for concrete_type in ConcreteRatchetChain ConcreteRatchetKernel ConcreteRatchetRestore; do
	require_occurrence_count 1 \
		'#\[cfg_attr\(\s*feature\s*=\s*"proverif",\s*hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"[^"]*noeq[^"]*"\s*\)\s*\)\]\s*(?:pub\s+)?struct\s+'"${concrete_type}"'\b' \
		"reviewed noeq target ${concrete_type}" src/ratchet/concrete.rs
done
require_occurrence_count 1 \
	'#\[cfg_attr\(feature\s*=\s*"proverif",\s*hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"noeq"\s*\)\)\]\s*pub\s+struct\s+InitialRatchetChains\b' \
	"reviewed noeq target InitialRatchetChains" src/pqxdh.rs
require_occurrence_count 1 \
	'hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"friend Beaconcrypt_core\.Ratchet\\nfriend Beaconcrypt_core\.Ratchet\.Refined\\nnoeq"\s*\)' \
	"reviewed Concrete-to-Ratchet-and-Refined friend edges" src/ratchet/concrete.rs
require_occurrence_count 1 \
	'hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"friend Beaconcrypt_core\.Ratchet\.Control"\s*\)' \
	"reviewed Refined-to-Control friend edge" src/ratchet/refined.rs
require_occurrence_count 1 \
	'hax_lib\s*::\s*fstar\s*::\s*before\s*\(\s*"friend Beaconcrypt_core\.Ratchet\\nfriend Beaconcrypt_core\.Ratchet\.Concrete"\s*\)' \
	"reviewed PQXDH.Concrete-to-Ratchet friend edges" src/pqxdh/concrete.rs
require_line_count 3 '^noeq$' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Concrete.fst \
	"generated function-record noeq directive"
require_line_count 1 '^noeq$' \
	proofs/fstar/extraction/Beaconcrypt_core.Pqxdh.fst \
	"generated initial-chain noeq directive"
require_line_count 1 '^friend Beaconcrypt_core\.Ratchet$' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Concrete.fst \
	"generated Concrete-to-Ratchet friend edge"
require_line_count 1 '^friend Beaconcrypt_core\.Ratchet\.Refined$' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Concrete.fst \
	"generated Concrete-to-Refined friend edge"
require_line_count 1 '^friend Beaconcrypt_core\.Ratchet\.Control$' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Refined.fst \
	"generated Refined-to-Control friend edge"
require_line_count 1 '^friend Beaconcrypt_core\.Ratchet$' \
	proofs/fstar/extraction/Beaconcrypt_core.Pqxdh.Concrete.fst \
	"generated PQXDH.Concrete-to-Ratchet friend edge"
require_line_count 1 '^friend Beaconcrypt_core\.Ratchet\.Concrete$' \
	proofs/fstar/extraction/Beaconcrypt_core.Pqxdh.Concrete.fst \
	"generated PQXDH.Concrete-to-Ratchet.Concrete friend edge"

require_line_count 6 '^val ' proofs/fstar/Beaconcrypt_core.Ratchet.fsti \
	"narrow PQXDH-facing ratchet value declaration"
for declaration in \
	v_RATCHET_CHAIN_SIZE \
	v_SYM_RATCHET_INFO \
	t_RatchetChain \
	impl_RatchetChain__from_bytes \
	t_SymmetricRatchetKdfRequest \
	impl_SymmetricRatchetKdfRequest__new; do
	require_line_count 1 "^val ${declaration}( | :)" \
		proofs/fstar/Beaconcrypt_core.Ratchet.fsti \
		"PQXDH-facing ratchet value declaration ${declaration}"
done
require_line_count 2 '^val ' proofs/fstar/Beaconcrypt_core.Ratchet.Concrete.fsti \
	"narrow PQXDH.Concrete-facing concrete ratchet declaration"
for declaration in \
	t_ConcreteRatchetKernel \
	impl_ConcreteRatchetKernel__new; do
	require_line_count 1 "^val ${declaration}( | :)" \
		proofs/fstar/Beaconcrypt_core.Ratchet.Concrete.fsti \
		"PQXDH.Concrete-facing concrete ratchet declaration ${declaration}"
done
require_line_count 29 '^val ' proofs/fstar/Beaconcrypt_core.Ratchet.Control.fsti \
	"Refined-facing control declaration"
require_line_count 15 '^val ' proofs/fstar/Beaconcrypt_core.Ratchet.Refined.fsti \
	"root-facing refined declaration"
reject_matches "stable ratchet interface exposes a representation" \
	'^type\s' \
	proofs/fstar/Beaconcrypt_core.Ratchet.fsti \
	proofs/fstar/Beaconcrypt_core.Ratchet.Concrete.fsti \
	proofs/fstar/Beaconcrypt_core.Ratchet.Control.fsti \
	proofs/fstar/Beaconcrypt_core.Ratchet.Refined.fsti
reject_matches "PQXDH.Concrete companion interface exposes a declaration" \
	'^(?:val|type|let|friend)\b' \
	proofs/fstar/Beaconcrypt_core.Pqxdh.Concrete.fsti
require_line_count 4 '^friend Beaconcrypt_core\.Ratchet' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"ratchet proof friend edge"
require_line_count 5 '^friend Beaconcrypt_core\.Ratchet' \
	proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst \
	"PQXDH proof friend edge"
require_line_count 1 '^friend Beaconcrypt_core\.Pqxdh\.Concrete$' \
	proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst \
	"PQXDH proof concrete-module friend edge"
reject_matches "proof interface exposes implementation friendship" \
	'^friend\s' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fsti \
	proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fsti

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

# The exact maximum-gap success publishes sequences two through 50 and retains 49 skipped entries.
# Both successful targets stay out of the cache.
require_line_count 49 \
	'^[[:space:]]+let capacity_cache_[0-9]+ = receive_cache_entry\(' \
	proofs/pro-verif/environment.pvl \
	"maximum-gap skipped cache entry"
for skipped_sequence in {2..50}; do
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
	'let\s+maximum_gap_state\s*=\s*receive_state\(\s*capacity_sequence_51,\s*capacity_chain_52,\s*capacity_cache_50\s*\)' \
	"successful maximum-gap 49-entry state" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'event\s+ReceiveCapacityRejected\(\s*capacity_session,\s*capacity_sequence_53,\s*capacity_rejected_frame,\s*maximum_gap_state\s*\)' \
	"state-neutral capacity rejection" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'let\s+released_state\s*=\s*receive_state\(\s*capacity_sequence_51,\s*capacity_chain_52,\s*capacity_cache_49\s*\)' \
	"cached success releases one capacity slot" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'let\s+after_release_cache\s*=\s*receive_cache_entry\(\s*capacity_sequence_52,\s*capacity_material_52,\s*capacity_cache_49\s*\)' \
	"post-release future skipped-key publication" \
	proofs/pro-verif/environment.pvl
require_occurrence_count 1 \
	'let\s+after_release_state\s*=\s*receive_state\(\s*capacity_sequence_53,\s*capacity_chain_54,\s*after_release_cache\s*\)' \
	"post-release future target consumption state" \
	proofs/pro-verif/environment.pvl
reject_matches "successful receive target remains cached" \
	'receive_cache_entry\(\s*(?:target_sequence|capacity_sequence_(?:51|53))\b' \
	proofs/pro-verif/environment.pvl

# Pending receive transactions are kernel-private Rust values but must remain transparent in the generated proof surface.
# They may not acquire Clone or Copy derives that would turn them into duplicable live capabilities.
for pending_type in PreparedReceive PreparedCachedReceive PreparedFutureTarget PendingReceive; do
	require_line_count 1 \
		"^(pub\\(super\\) )?(enum|struct) ${pending_type}([[:space:]<{]|$)" \
		src/ratchet/refined.rs \
		"private pending receive type ${pending_type}"
	require_line_count 1 "^type t_${pending_type}( | = )" \
		proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Refined.fst \
		"generated pending receive type ${pending_type}"
done
reject_matches "pending receive capability became Clone or Copy" \
	'#\[derive\([^]]*\b(?:Clone|Copy)\b[^]]*\)\]\s*(?:(?:#\[[^]]*\]|//[^\n]*|/\*[\s\S]*?\*/)\s*)*(?:pub(?:\([^)]*\))?\s+)?(?:enum\s+PreparedReceive|struct\s+(?:PreparedCachedReceive|PreparedFutureTarget|PendingReceive))' \
	src/ratchet/refined.rs
reject_matches "pending receive capability gained conditional Clone or Copy derive" \
	'#\[cfg_attr\([^]]*\bderive\s*\([^)]*\b(?:Clone|Copy)\b[^)]*\)[^]]*\)\]\s*(?:(?:#\[[^]]*\]|//[^\n]*|/\*[\s\S]*?\*/)\s*)*(?:pub(?:\([^)]*\))?\s+)?(?:enum\s+PreparedReceive|struct\s+(?:PreparedCachedReceive|PreparedFutureTarget|PendingReceive))' \
	src/ratchet/refined.rs
reject_matches "pending receive capability gained explicit Clone or Copy implementation" \
	'impl(?:\s*<[\s\S]{0,500}?>)?\s+(?:[A-Za-z_][A-Za-z0-9_]*::)*(?:Clone|Copy)\s+for\s+(?:PreparedReceive|PreparedCachedReceive|PreparedFutureTarget|PendingReceive)\b' \
	src/ratchet/refined.rs
require_occurrence_count 1 \
	'fn\s+prepare_future_receive_steps[\s\S]{0,600}?staged_slots:\s*&mut\s*\[Option<CachedReceiveKey<Material>>;\s*RECEIVE_CACHE_CAPACITY\],' \
	"single borrowed future-receive staging buffer" \
	src/ratchet/refined.rs
require_occurrence_count 1 \
	'#\[cfg\(any\(test,\s*feature\s*=\s*"test-utils"\)\)\]\s*#\[doc\(hidden\)\]\s*pub\s+fn\s+concrete_advance_receive_until\b' \
	"narrow dev-only receive-advancement compatibility gate" \
	src/ratchet.rs
reject_matches "dev-only receive advancement entered extraction" \
	'^let\s+concrete_advance_receive_until\b' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.fst
for helper in \
	prepare_cached_receive \
	prepare_future_receive_steps \
	receive_control_prefix_matches \
	pending_receive_slots_are_valid \
	pending_receive_is_valid \
	prepare_receive \
	publish_cached_receive \
	publish_future_receive_slots \
	publish_future_receive; do
	require_line_count 1 "^let( rec)? ${helper}( |$)" \
		proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Refined.fst \
		"generated pending receive helper ${helper}"
done

for declaration in \
	prepared_future_trace \
	prepare_future_receive_steps_is_total_and_exact \
	prepared_future_trace_passes_validator \
	future_publication_is_exact \
	publish_future_receive_slots_is_exact \
	prepared_future_publication_is_exact \
	valid_pending \
	admitted_future_plan_prepares_valid_pending; do
	require_line_count 1 "^let( rec)? ${declaration}\$" \
		proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
		"non-vacuous exact future preparation declaration ${declaration}"
done
for declaration in \
	valid_cached_preparation \
	valid_cached_target_is_preparable \
	valid_cached_target_prepares_valid_cached \
	admitted_cached_target_prepares_valid_cached; do
	require_line_count 1 "^let ${declaration}\$" \
		proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
		"non-vacuous exact cached preparation declaration ${declaration}"
done
for declaration in \
	successful_receive \
	refined_open_and_finish_rejection_is_neutral \
	refined_open_and_finish_preserves_validity \
	refined_open_and_finish_is_state_neutral_or_successful \
	refined_open_success_replay_is_neutral \
	rejected_open_attempts_preserve_entry \
	retry_after_rejected_open_attempts_equals_direct \
	refined_open_rejection_preserves_cache_capacity \
	fresh_maximum_gap_success_publishes_exactly_49; do
	require_line_count 1 "^let( rec)? ${declaration}\$" \
		proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
		"public state-neutral receive declaration ${declaration}"
done
require_line_count 1 '^let cached_receive_failure_retry_consumes_once$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"low-level cached/restored retry compatibility lemma"
require_line_count 1 \
	'^let successful_receive_releases_capacity_for_next_future$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"low-level cached/restored capacity-release compatibility lemma"

require_line_count 1 '^let valid_refined$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined logical/sealed cached sequence-material invariant"
for declaration in \
	reachable \
	reachable_restore \
	refined_from_counters_is_reachable \
	refined_new_is_reachable \
	refined_advance_send_preserves_reachability \
	refined_seal_next_preserves_reachability \
	refined_advance_receive_preserves_reachability \
	refined_advance_receive_until_preserves_reachability \
	refined_receive_key_is_derived \
	refined_finish_receive_preserves_reachability \
	refined_open_and_finish_preserves_reachability \
	start_refined_restore_is_reachable \
	refined_restore_receive_key_preserves_reachability \
	finish_refined_restore_preserves_reachability; do
	require_line_count 1 "^let ${declaration}\$" \
		proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
		"derivational reachability declaration ${declaration}"
done
require_line_count 1 '^let cached_materials_are_derived$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"canonical cached-material derivation predicate"
require_line_count 1 '^let rec chain_after$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"canonical fixed-step chain iterator"
require_line_count 1 '^let material_at$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"canonical sequence material function"
require_line_count 1 '^  state\.f_send_chain ==$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"reachable send-chain/counter equality"
require_line_count 1 '^  state\.f_receive_chain ==$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"reachable receive-chain/counter equality"
require_line_count 1 '^        cached\.f_material ==$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"canonical cached-material derivation equality"
require_line_count 1 \
	'cached\.f_sequence == cache_entry cache i$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"sealed cached-key sequence provenance invariant"
require_line_count 1 '^let ratchet_kdf_output_split_is_exact$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"exact production ratchet KDF-output split theorem"
for declaration in \
	symmetric_ratchet_kdf_request_is_exact \
	concrete_ratchet_step_preserves_executor \
	concrete_reachable \
	concrete_kernel_new_is_reachable \
	concrete_seal_next_preserves_reachability \
	concrete_open_and_finish_preserves_reachability; do
	require_line_count 1 "^let ${declaration}\$" \
		proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
		"concrete ratchet specialization declaration ${declaration}"
done
for declaration in \
	authenticated_registration_derives_common_fixed_root \
	authenticated_registrations_establish_concrete_session \
	initial_ratchet_chains_use_exact_root_and_directions \
	concrete_session \
	concrete_initial_kernels_are_complementary \
	concrete_initial_kernels_are_reachable \
	concrete_directional_materials_agree \
	beacon_seal_server_open_preserves_concrete_session \
	server_seal_beacon_open_preserves_concrete_session; do
	require_line_count 1 "^let ${declaration}\$" \
		proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst \
		"composed concrete PQXDH-ratchet declaration ${declaration}"
done
require_line_count 1 '^let refined_from_counters_is_valid$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined constructor invariant lemma"
require_line_count 1 '^let refined_advance_send_preserves_validity$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined send invariant-preservation lemma"
require_line_count 1 '^let refined_advance_receive_success_uses_step$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined one-step callback association lemma"
require_line_count 1 '^let refined_receive_step_matches$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined pure callback-result step relation"
require_line_count 1 '^let rec refined_receive_steps_are_ordered$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined recursive callback-result trace"
require_line_count 1 '^let rec refined_receive_slots_are_empty_for_valid$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined whole-plan preflight lemma"
require_line_count 1 '^let refined_advance_receive_with_space_succeeds$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined bounded one-step totality lemma"
require_line_count 1 '^let rec refined_execute_receive_steps_is_exact$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined whole-plan exact execution lemma"
require_line_count 1 '^let refined_advance_receive_until_executes_plan$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"compatibility receive-until admitted-plan lemma"
require_line_count 1 \
	'^let refined_advance_receive_until_rejection_is_neutral$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"compatibility receive-until neutral-rejection lemma"
require_line_count 1 '^let refined_advance_receive_until_is_ordered$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined composed callback-ordering lemma"
require_line_count 1 '^let refined_receive_entry_is_associated$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined active-slot accessor association lemma"
require_line_count 1 '^let refined_receive_entry_mismatched_tag_is_rejected$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined active-slot accessor mismatch-rejection lemma"
require_line_count 1 '^let refined_receive_key_mismatched_tag_is_rejected$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined cached-sequence lookup mismatch-rejection lemma"
require_line_count 1 '^let refined_finish_receive_mismatched_target_is_neutral$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined cached-target mismatch-neutrality lemma"
require_line_count 1 '^let refined_finish_receive_mismatched_last_is_neutral$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined cached-last mismatch-neutrality lemma"
require_line_count 1 \
	'^let refined_finish_receive_success_is_exact_swap_removal$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined exact sealed cached sequence-material swap-removal lemma"
require_line_count 1 '^let refined_restore_receive_key_is_atomic$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined sealed sequence-material restoration lemma"
require_line_count 1 '^let finish_refined_restore_is_valid$' \
	proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst \
	"refined restoration-finish lemma"
require_line_count 5 'Core_models\.Option\.impl__take' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Refined.fst \
	"transparent refined cached and pending-slot movement"
require_line_count 1 'Rust_primitives\.Hax\.while_loop \(fun' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Control.fst \
	"transparent bounded control loop"
require_line_count 6 'Rust_primitives\.Hax\.while_loop \(fun' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Refined.fst \
	"transparent bounded refined loops"
require_line_count 1 'Core_models\.Array\.from_fn' \
	proofs/fstar/extraction/Beaconcrypt_core.Commitment.fst \
	"reviewed commitment array-from-function contract use"
require_line_count 3 'Core_models\.Array\.from_fn' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.fst \
	"reviewed ratchet array-from-function contract use"
require_line_count 11 'Core_models\.Array\.from_fn' \
	proofs/fstar/extraction/Beaconcrypt_core.Pqxdh.fst \
	"reviewed PQXDH array-from-function contract use"
require_line_count 5 '^#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"$' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Control.fst \
	"generated control loop-reference option scope"
require_line_count 5 '^#pop-options$' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Control.fst \
	"generated control loop-reference option scope end"
require_line_count 3 '^#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"$' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Refined.fst \
	"generated refined loop-reference option scope"
require_line_count 3 '^#pop-options$' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Refined.fst \
	"generated refined loop-reference option scope end"
for declaration in \
	lookup_receive_key_from \
	lookup_receive_key_from_stops_at_capacity \
	lookup_receive_key_from_stops_at_len \
	lookup_receive_key_from_matches \
	lookup_receive_key_from_advances; do
	require_line_count 1 "^let( rec)? ${declaration}\\b" \
		proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Control.fst \
		"generated control loop reference ${declaration}"
done
for declaration in \
	refined_receive_slots_are_empty_from \
	receive_control_prefix_matches_from \
	pending_receive_slots_are_valid_from; do
	require_line_count 1 "^let rec ${declaration}\\b" \
		proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Refined.fst \
		"generated refined loop reference ${declaration}"
done
reject_matches "unconstrained memory replacement in refined ratchet" \
	'Core_models\.Mem\.replace' \
	proofs/fstar/extraction/Beaconcrypt_core.Ratchet.Refined.fst

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
