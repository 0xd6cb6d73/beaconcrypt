#!/usr/bin/env bash
# SPDX-License-Identifier: 0BSD

set -euo pipefail

[[ $# -eq 2 ]] || {
	printf 'usage: %s MODEL LOG\n' "$0" >&2
	exit 2
}

model="${1##*/}"
log="$2"
expected_file="$(dirname -- "$0")/expected-results.txt"

[[ -r "$expected_file" ]] || {
	echo "missing CryptoVerif expected-result policy: $expected_file" >&2
	exit 1
}

mapfile -t expected_results < <(
	awk -F '\t' -v model="$model" '$1 == model { sub(/^[^\t]*\t/, ""); print }' \
		"$expected_file"
)
if [[ "${#expected_results[@]}" == 0 ]]; then
	echo "no expected-result policy for CryptoVerif model: $model" >&2
	exit 1
fi

if rg -n --pcre2 '^(?:Error:|Warning:|RESULT (?!Proved|Could not prove|time_))' "$log"; then
	echo "CryptoVerif reported an error, warning, or unknown result for $model" >&2
	exit 1
fi

mapfile -t actual_results < <(rg '^RESULT (?:Proved|Could not prove) ' "$log" || true)
complete_count="$(rg -c '^All queries proved\.$' "$log" || true)"
complete_count="${complete_count:-0}"

if [[ "${#actual_results[@]}" != "${#expected_results[@]}" ]]; then
	echo "unexpected CryptoVerif result count for $model: expected=${#expected_results[@]} actual=${#actual_results[@]}" >&2
	exit 1
fi

for index in "${!expected_results[@]}"; do
	if [[ "${actual_results[$index]}" != "${expected_results[$index]}" ]]; then
		echo "unexpected CryptoVerif result for $model at index $index" >&2
		echo "  expected: ${expected_results[$index]}" >&2
		echo "  actual:   ${actual_results[$index]}" >&2
		exit 1
	fi
done

if [[ "$model" == assigned-id-binding-negative-control.ocv ]]; then
	if [[ "$complete_count" != 0 ]]; then
		echo "negative control unexpectedly proved all queries: $model" >&2
		exit 1
	fi
	echo "$model: expected assigned-ID agreement failure reproduced."
else
	if [[ "$complete_count" != 1 ]] || rg -q '^RESULT Could not prove ' "$log"; then
		echo "CryptoVerif did not prove every positive query for $model" >&2
		exit 1
	fi
	echo "$model: All queries proved."
fi
