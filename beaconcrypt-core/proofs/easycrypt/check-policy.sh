#!/bin/sh
# SPDX-License-Identifier: 0BSD

set -eu

proof_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$proof_dir/../../.." && pwd)

if rg -n -i '\b(admit|admitted|abort|sorry)\b' "$proof_dir"/*.ec; then
	echo 'unproved EasyCrypt command found' >&2
	exit 1
fi

actual_assumptions=$(mktemp)
trap 'rm -f "$actual_assumptions"' EXIT HUP INT TERM

# Inventory complete normalized declarations. Names alone are insufficient: changing an axiom's parameters or conclusion must produce a reviewed diff.
for source in "$proof_dir"/*.ec; do
	base=$(basename "$source")
	awk -v source="$base" '
		function emit() {
			gsub(/[[:space:]]+/, " ", statement)
			sub(/^ /, "", statement)
			sub(/ $/, "", statement)
			print source ":" statement
			statement = ""
			collecting = 0
		}
		/^[[:space:]]*(declare[[:space:]]+)?axiom[[:space:]]/ {
			collecting = 1
			statement = $0
			if ($0 ~ /\.[[:space:]]*$/) emit()
			next
		}
		collecting {
			statement = statement " " $0
			if ($0 ~ /\.[[:space:]]*$/) emit()
		}
		END {
			if (collecting) {
				print "unterminated EasyCrypt axiom declaration" > "/dev/stderr"
				exit 2
			}
		}
	' "$source"
done | sort >"$actual_assumptions"

if cut -d: -f2- "$actual_assumptions" |
	rg -n -v '^(declare )?axiom assumption_[A-Za-z0-9_]+'; then
	echo 'EasyCrypt axiom is not named assumption_*' >&2
	exit 1
fi

if ! diff -u "$proof_dir/expected-assumptions.txt" "$actual_assumptions"; then
	echo 'EasyCrypt assumption inventory changed' >&2
	exit 1
fi

check_symbol() {
	file=$1
	symbol=$2
	if ! rg -F -q -- "$symbol" "$repo_root/$file"; then
		echo "missing contract symbol '$symbol' in '$file'" >&2
		exit 1
	fi
}

expected_hax_revision=4fad0ae6268bc0817cafcf4f0300e50a481e4d49

tail -n +2 "$proof_dir/implementation-contracts.tsv" |
while IFS="$(printf '\t')" read -r contract hax_revision production_source production_symbol extracted_source extracted_symbols refinement_source refinement_symbols easycrypt_contract status; do
	[ -n "$contract" ] || continue
	if [ "$hax_revision" != "$expected_hax_revision" ]; then
		echo "unexpected hax revision '$hax_revision' for '$contract'" >&2
		exit 1
	fi
	check_symbol "$production_source" "$production_symbol"
	old_ifs=$IFS
	IFS=';'
	for symbol in $extracted_symbols; do
		check_symbol "$extracted_source" "$symbol"
	done
	for symbol in $refinement_symbols; do
		check_symbol "$refinement_source" "$symbol"
	done
	IFS=$old_ifs
	if ! rg -F -q -- "$easycrypt_contract" "$proof_dir"/*.ec; then
		echo "missing EasyCrypt contract '$easycrypt_contract'" >&2
		exit 1
	fi
	if [ "$status" != pending-reviewed-cross-prover-bridge ]; then
		echo "unexpected contract status '$status' for '$contract'" >&2
		exit 1
	fi
done

check_declaration() {
	language=$1
	file=$2
	symbol=$3
	case "$symbol" in
		''|*[!A-Za-z0-9_]*)
			echo "invalid $language declaration symbol '$symbol'" >&2
			exit 1
			;;
	esac
	case "$language" in
		ssprove)
			declaration_kinds='Theorem Lemma Corollary Definition'
			;;
		easycrypt)
			declaration_kinds='lemma op'
			;;
		*)
			echo "unknown proof language '$language'" >&2
			exit 1
			;;
	esac
	if ! awk -v kinds="$declaration_kinds" -v symbol="$symbol" '
		BEGIN {
			n = split(kinds, allowed, " ")
			for (i = 1; i <= n; i++) kind[allowed[i]] = 1
		}
		($1 in kind) {
			declared = $2
			sub(/\(.*/, "", declared)
			sub(/:.*/, "", declared)
			if (declared == symbol) found = 1
		}
		END { exit !found }
	' "$repo_root/$file"; then
		echo "missing exact $language declaration '$symbol' in '$file'" >&2
		exit 1
	fi
}

# This is a reviewed coverage manifest. The gate checks declaration heads and metadata; it cannot establish logical equivalence between propositions in two proof assistants.
coverage_manifest=$proof_dir/theorem-parity.tsv
expected_coverage_header='area	ssprove_file	ssprove_symbol	easycrypt_file	easycrypt_symbol	relation	scope'
actual_coverage_header=$(sed -n '1p' "$coverage_manifest")
if [ "$actual_coverage_header" != "$(printf '%b' "$expected_coverage_header")" ]; then
	echo 'unexpected bounded-capstone coverage header' >&2
	exit 1
fi

coverage_rows=$(awk 'NR > 1 { count++ } END { print count + 0 }' "$coverage_manifest")
if [ "$coverage_rows" -ne 30 ]; then
	echo "unexpected bounded-capstone coverage row count '$coverage_rows'" >&2
	exit 1
fi
duplicate_coverage_area=$(awk -F '\t' 'NR > 1 { seen[$1]++ } END { for (area in seen) if (seen[area] > 1) print area }' "$coverage_manifest")
if [ -n "$duplicate_coverage_area" ]; then
	echo "duplicate bounded-capstone coverage area '$duplicate_coverage_area'" >&2
	exit 1
fi

tail -n +2 "$coverage_manifest" |
while IFS="$(printf '\t')" read -r area ssprove_file ssprove_symbol easycrypt_file easycrypt_symbol relation scope; do
	if [ -z "$area" ] || [ -z "$ssprove_file" ] || [ -z "$ssprove_symbol" ] ||
	   [ -z "$easycrypt_file" ] || [ -z "$easycrypt_symbol" ] ||
	   [ -z "$relation" ] || [ -z "$scope" ]; then
		echo 'incomplete bounded-capstone coverage row' >&2
		exit 1
	fi
	case "$ssprove_file" in
		beaconcrypt-core/proofs/ssprove/*.v) ;;
		*) echo "invalid SSProve coverage path '$ssprove_file'" >&2; exit 1 ;;
	esac
	case "$easycrypt_file" in
		beaconcrypt-core/proofs/easycrypt/*.ec) ;;
		*) echo "invalid EasyCrypt coverage path '$easycrypt_file'" >&2; exit 1 ;;
	esac
	case "$relation" in
		reviewed-bounded-counterpart|interface-incomparable) ;;
		*)
			echo "invalid bounded-capstone coverage relation '$relation' for '$area'" >&2
			exit 1
			;;
	esac
	check_declaration ssprove "$ssprove_file" "$ssprove_symbol"
	check_declaration easycrypt "$easycrypt_file" "$easycrypt_symbol"
done
