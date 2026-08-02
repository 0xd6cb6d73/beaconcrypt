#!/usr/bin/env bash
# SPDX-License-Identifier: 0BSD

set -euo pipefail

core_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
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
	[adapter-rust]=11
	[adapter-schema]=3
	[core-rust]=3
	[control]=11
	[generated-fstar]=2
	[generated-proverif]=1
	[handwritten-fstar]=2
	[handwritten-proverif]=8
	[inventory]=2
	[validation]=1
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

symlink_path="$(find ../../src src proofs -type l -print -quit)"
[[ -z "$symlink_path" ]] || fail "symlink in monitored tree: $symlink_path"

printf '%s\n' \
	../../.cargo/config.toml \
	../../.github/workflows/formal-verification.yml \
	../../.gitignore \
	../../Cargo.lock \
	../../Cargo.toml \
	../../flake.lock \
	../../flake.nix \
	Cargo.toml \
	Makefile \
	README.md \
	proofs/fstar/Makefile > "$tmp_dir/control"
compare_set control "$tmp_dir/control"

printf '%s\n' proofs/check-inventory.sh proofs/trusted-boundary.md \
	> "$tmp_dir/inventory"
compare_set inventory "$tmp_dir/inventory"

printf '%s\n' ../../tests/protocol.rs > "$tmp_dir/validation"
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

find ../../src -type f -name '*.rs' -printf '%p\n' > "$tmp_dir/adapter-rust"
printf '%s\n' ../../build.rs >> "$tmp_dir/adapter-rust"
compare_set adapter-rust "$tmp_dir/adapter-rust"

find ../../src/schema -type f -name '*.capnp' -printf '%p\n' > "$tmp_dir/adapter-schema"
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
	rg --no-ignore -q "beaconcrypt_protocol_core__pqxdh__${replacement}\\b" "$generated_proverif" ||
		fail "missing generated ProVerif replacement: $replacement"
done

require_line_count 6 '^type beaconcrypt_protocol_core' "$generated_proverif" \
	"generated ProVerif selected type"
require_line_count 12 '^fun beaconcrypt_protocol_core.*_(to|from)_bitstring' "$generated_proverif" \
	"generated ProVerif type converter"
require_line_count 6 '^const beaconcrypt_protocol_core.*_default_value' "$generated_proverif" \
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
	'beaconcrypt_protocol_core__pqxdh__t_RootKeyInput_to_bitstring' \
	"allowed generated ProVerif converter" "${handwritten_proverif[@]}"
require_occurrence_count 3 '_to_bitstring' \
	"all handwritten generated ProVerif converters" "${handwritten_proverif[@]}"

require_line_count 31 '^fun ' proofs/pro-verif/crypto.pvl \
	"handwritten primitive constructor/function"
require_line_count 6 '^reduc ' proofs/pro-verif/crypto.pvl \
	"handwritten primitive reduction"
require_line_count 1 '^letfun ' proofs/pro-verif/crypto.pvl \
	"handwritten primitive helper"
require_line_count 13 '^event ' proofs/pro-verif/environment.pvl \
	"handwritten event"
require_line_count 2 '^table ' proofs/pro-verif/environment.pvl \
	"handwritten table"
require_line_count 10 '^free ' proofs/pro-verif/environment.pvl \
	"handwritten free name/channel"
require_line_count 7 '^let [A-Z]' proofs/pro-verif/environment.pvl \
	"handwritten process"
require_line_count 11 '^query ' proofs/pro-verif/queries.pvl \
	"baseline query"
require_line_count 7 '^query ' proofs/pro-verif/reachability-queries.pvl \
	"reachability query"
require_line_count 5 '^query ' proofs/pro-verif/compromise-queries.pvl \
	"compromise query"
require_line_count 1 '^process$' proofs/pro-verif/baseline.pv \
	"baseline top-level process"
require_line_count 1 '^process$' proofs/pro-verif/compromise.pv \
	"compromise top-level process"

reject_matches "unreviewed generated F* exception" \
	'\b(?:while_loop_return|to_le_bytes|assume|admit)\b' \
	proofs/fstar/extraction --glob '*.fst' --glob '*.fsti'

printf 'Formal-verification inventory matches the reviewed boundary.\n'
