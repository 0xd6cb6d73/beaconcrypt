#!/usr/bin/env bash
# SPDX-License-Identifier: 0BSD

set -euo pipefail

export LC_ALL=C

readonly lean_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
readonly repo_root="$(cd -- "${lean_dir}/../../.." && pwd)"
readonly patch_dir="${lean_dir}/patches"
readonly manifest="${lean_dir}/lake-manifest.json"
readonly lakefile="${lean_dir}/lakefile.toml"
readonly toolchain="${lean_dir}/lean-toolchain"
readonly hax_config="${repo_root}/hax.toml"
readonly manifest_sha256="8074eb307aef827181df03b0b4e0cbccf7ab654b1eb9ebec1d045b5d9f96d949"
readonly lakefile_sha256="7ca8d167a315dbeb402a063d6e917ae51925f543a28bb70e5094423b5191521b"
readonly toolchain_sha256="8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632"
readonly hax_config_sha256="24392e4e24eb99e916b013905d45944573e5e860473686fcb08f9c6578b72323"

die() {
	printf 'error: %s\n' "$*" >&2
	exit 1
}

file_sha256() {
	sha256sum "$1" | awk '{print $1}'
}

require_file_hash() {
	local path="$1"
	local expected="$2"
	local label="$3"
	local actual

	[[ -f "$path" ]] || die "missing ${label}: ${path}"
	actual="$(file_sha256 "$path")"
	[[ "$actual" == "$expected" ]] ||
		die "unexpected ${label} hash: expected ${expected}, got ${actual}"
}

require_root_configuration() {
	require_file_hash "$manifest" "$manifest_sha256" "Lake manifest"
	require_file_hash "$lakefile" "$lakefile_sha256" "Lake configuration"
	require_file_hash "$toolchain" "$toolchain_sha256" "Lean toolchain"
	require_file_hash "$hax_config" "$hax_config_sha256" "Hax extraction configuration"
}

require_dependency_checkout() {
	local label="$1"
	local checkout="$2"
	local inside
	local checkout_root
	local expected_root

	[[ ! -L "$checkout" ]] || die "${label} checkout must not be a symbolic link: ${checkout}"
	[[ -d "$checkout" ]] || die "missing ${label} checkout: ${checkout}"
	inside="$(git -C "$checkout" rev-parse --is-inside-work-tree 2>/dev/null)" ||
		die "${label} checkout is not a Git worktree: ${checkout}"
	[[ "$inside" == true ]] || die "${label} checkout is not a non-bare Git worktree: ${checkout}"
	checkout_root="$(git -C "$checkout" rev-parse --show-toplevel)"
	checkout_root="$(realpath -e "$checkout_root")"
	expected_root="$(realpath -e "$checkout")"
	[[ "$checkout_root" == "$expected_root" ]] ||
		die "${label} checkout resolves to unexpected Git root ${checkout_root}"
}

manifest_git_packages() {
	command -v jq >/dev/null 2>&1 || die "jq is required to validate Lake dependency checkouts"
	jq -er '.packages[] | select(.type == "git") | [.name, .rev] | @tsv' "$manifest"
}

materialize_packages() {
	local checkout
	local name
	local needs_resolution=false
	local revision

	while IFS=$'\t' read -r name revision; do
		[[ "$name" =~ ^[A-Za-z0-9_.-]+$ ]] || die "unsafe package name in Lake manifest: ${name}"
		[[ "$revision" =~ ^[0-9a-f]{40}$ ]] || die "invalid revision for ${name} in Lake manifest: ${revision}"
		checkout="${lean_dir}/.lake/packages/${name}"
		[[ ! -L "$checkout" ]] || die "dependency checkout must not be a symbolic link: ${checkout}"
		if [[ -e "$checkout" ]]; then
			require_dependency_checkout "$name" "$checkout"
		else
			needs_resolution=true
		fi
	done <<< "$manifest_packages"
	if [[ "$needs_resolution" == true ]]; then
		printf 'Materializing exact revisions from the pinned Lake manifest\n'
		(cd "$lean_dir" && lake resolve-deps)
	fi

	require_root_configuration
	while IFS=$'\t' read -r name revision; do
		require_dependency_checkout "$name" "${lean_dir}/.lake/packages/${name}"
	done <<< "$manifest_packages"
}

require_clean_manifest_dependencies() {
	local actual_revision
	local checkout
	local name
	local revision
	local untracked

	while IFS=$'\t' read -r name revision; do
		case "$name" in
			aeneas|Hax) continue ;;
		esac
		checkout="${lean_dir}/.lake/packages/${name}"
		require_dependency_checkout "$name" "$checkout"
		actual_revision="$(git -C "$checkout" rev-parse --verify HEAD)"
		[[ "$actual_revision" == "$revision" ]] ||
			die "unexpected ${name} revision: expected ${revision}, got ${actual_revision}"
		git -C "$checkout" diff --cached --quiet -- || die "${name} checkout has staged changes"
		git -C "$checkout" diff --quiet -- || die "${name} checkout has unstaged changes"
		untracked="$(git -C "$checkout" ls-files --others --exclude-standard)"
		[[ -z "$untracked" ]] || die "${name} checkout has unexpected untracked files: ${untracked}"
	done <<< "$manifest_packages"
}

dependency_diff_sha256() {
	local checkout="$1"

	git -C "$checkout" \
		-c color.ui=false \
		-c diff.algorithm=myers \
		-c diff.indentHeuristic=false \
		diff --no-ext-diff --no-textconv --full-index --binary \
		--src-prefix=a/ --dst-prefix=b/ -- | sha256sum | awk '{print $1}'
}

apply_dependency_patch() {
	local label="$1"
	local checkout="$2"
	local expected_revision="$3"
	local patch="$4"
	local expected_patch_sha256="$5"
	local expected_diff_sha256="$6"
	local actual_revision
	local actual_diff_sha256
	local untracked

	require_dependency_checkout "$label" "$checkout"
	require_file_hash "$patch" "$expected_patch_sha256" "${label} compatibility patch"
	actual_revision="$(git -C "$checkout" rev-parse --verify HEAD)"
	[[ "$actual_revision" == "$expected_revision" ]] ||
		die "unexpected ${label} revision: expected ${expected_revision}, got ${actual_revision}"
	git -C "$checkout" diff --cached --quiet -- || die "${label} checkout has staged changes"
	untracked="$(git -C "$checkout" ls-files --others --exclude-standard)"
	[[ -z "$untracked" ]] || die "${label} checkout has unexpected untracked files: ${untracked}"

	if git -C "$checkout" diff --quiet --; then
		git -C "$checkout" apply --check "$patch" || die "${label} patch does not apply to the pinned revision"
		git -C "$checkout" apply "$patch"
		printf 'Applied Lean 4.34.0 compatibility patch to %s\n' "$label"
	elif git -C "$checkout" apply --reverse --check "$patch" >/dev/null 2>&1; then
		printf 'Lean 4.34.0 compatibility patch already applied to %s\n' "$label"
	else
		die "${label} checkout contains changes other than the expected compatibility patch"
	fi

	actual_diff_sha256="$(dependency_diff_sha256 "$checkout")"
	[[ "$actual_diff_sha256" == "$expected_diff_sha256" ]] ||
		die "unexpected ${label} patched diff hash: expected ${expected_diff_sha256}, got ${actual_diff_sha256}"
}

require_root_configuration

manifest_packages="$(manifest_git_packages)" ||
	die "could not read Git packages from the pinned Lake manifest"
readonly manifest_packages
[[ -n "$manifest_packages" ]] || die "the pinned Lake manifest contains no Git packages"

readonly aeneas_checkout="${lean_dir}/.lake/packages/aeneas"
readonly hax_checkout="${lean_dir}/.lake/packages/Hax"

materialize_packages
require_clean_manifest_dependencies

apply_dependency_patch \
	Aeneas \
	"$aeneas_checkout" \
	"6852e6474ec508930acba4df79977b3483a10d10" \
	"${patch_dir}/aeneas-lean-4.34.patch" \
	"00fdbad88d59323701df644bba37bdce7ced2471c91523da8504a54bf0f8de31" \
	"a570d3db8c59698f9000cf462c9f8470ff182480b097508cb8daa9de6e222e71"

apply_dependency_patch \
	Hax-Lean \
	"$hax_checkout" \
	"b49608d5e402577b400569ee989c3f1b69e4aaf3" \
	"${patch_dir}/hax-lean-4.34.patch" \
	"8ab124902ac7d8ba2194dd23139220864d5cc2c2b9a8112e535200ddcf4a6b04" \
	"8ab124902ac7d8ba2194dd23139220864d5cc2c2b9a8112e535200ddcf4a6b04"
