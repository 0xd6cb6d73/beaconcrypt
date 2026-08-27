#!/usr/bin/env bash
# SPDX-License-Identifier: 0BSD

set -euo pipefail

fake_nix() {
	local argument line="cwd=$PWD" profile= generation= index
	for argument in "$@"; do
		line+=$'\t'"arg=$argument"
	done
	printf '%s\n' "$line" >> "${FAKE_NIX_LOG:?}"
	for argument in "$@"; do
		if [[ "$argument" == eval ]]; then
			printf '%s' "${FAKE_NIX_SYSTEM:-x86_64-linux}"
			return 0
		fi
	done
	for ((index = 1; index <= $#; index++)); do
		if [[ "${!index}" == --profile ]]; then
			index=$((index + 1))
			profile="${!index}"
			mkdir -p -- "$(dirname -- "$profile")"
			if [[ "${FAKE_NIX_FAIL_INIT:-0}" == 1 ]]; then
				[[ ! -L "$profile" ]] || rm -f -- "$profile"
				ln -s -- "$profile.failed-generation" "$profile"
				return 19
			fi
			[[ -z "${FAKE_NIX_INIT_DELAY:-}" ]] || sleep "$FAKE_NIX_INIT_DELAY"
			generation="$profile.fake-generation"
			mkdir -p -- "$generation"
			[[ ! -L "$profile" ]] || rm -f -- "$profile"
			ln -s -- "$generation" "$profile"
			return 0
		fi
	done
	return "${FAKE_NIX_RUN_STATUS:-0}"
}

if [[ "${FAKE_NIX_MODE:-0}" == 1 ]]; then
	fake_nix "$@"
	exit $?
fi

fail() {
	printf 'test-run-proof-shell: %s\n' "$*" >&2
	exit 1
}

assert_equal() {
	[[ "$1" == "$2" ]] || fail "expected '$1' to equal '$2'"
}

assert_contains() {
	grep -Fq -- "$2" "$1" || fail "expected $1 to contain: $2"
}

count_matching_lines() {
	awk -v needle="$2" 'index($0, needle) { count++ } END { print count + 0 }' "$1"
}

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source_runner="$script_dir/run-proof-shell"
test_script="$script_dir/${BASH_SOURCE[0]##*/}"
test_dir="$(mktemp -d)"
cleanup() {
	if [[ "${KEEP_TEST_RUN_PROOF_SHELL_TMP:-0}" == 1 ]]; then
		printf 'test-run-proof-shell: retained %s\n' "$test_dir" >&2
	else
		rm -rf -- "$test_dir"
	fi
}
trap cleanup EXIT
repo_dir="$test_dir/repository"
runner="$repo_dir/scripts/run-proof-shell"
mkdir -p -- "$repo_dir/scripts"
cp -- "$source_runner" "$runner"
chmod 0755 "$runner"
printf '%s\n' '{ outputs = _: { devShells = {}; }; }' > "$repo_dir/flake.nix"
printf '%s\n' '{ "nodes": {}, "root": "root", "version": 7 }' > "$repo_dir/flake.lock"
git -C "$repo_dir" init -q
git -C "$repo_dir" add flake.nix flake.lock scripts/run-proof-shell

profile_root="$test_dir/state with spaces"
fake_log="$test_dir/nix.log"
: > "$fake_log"

run_runner() {
	env \
		FAKE_NIX_MODE=1 \
		FAKE_NIX_LOG="$fake_log" \
		FAKE_NIX_SYSTEM="${FAKE_NIX_SYSTEM:-x86_64-linux}" \
		FAKE_NIX_FAIL_INIT="${FAKE_NIX_FAIL_INIT:-0}" \
		FAKE_NIX_INIT_DELAY="${FAKE_NIX_INIT_DELAY:-}" \
		FAKE_NIX_RUN_STATUS="${FAKE_NIX_RUN_STATUS:-0}" \
		NIX="$test_script" \
		BEACONCRYPT_PROOF_PROFILE_ROOT="$profile_root" \
		BEACONCRYPT_PROOF_PROFILE_LOCK_STYLE="${BEACONCRYPT_PROOF_PROFILE_LOCK_STYLE:-auto}" \
		BEACONCRYPT_PROOF_PROFILE_LOCK_TIMEOUT="${BEACONCRYPT_PROOF_PROFILE_LOCK_TIMEOUT:-3600}" \
		"$runner" "$@"
}

profile_a="$(run_runner path)"
printf '%s\n' unrelated > "$repo_dir/ignored-file"
profile_b="$(run_runner path)"
assert_equal "$profile_a" "$profile_b"
printf '%s\n' tracked > "$repo_dir/tracked-unrelated"
git -C "$repo_dir" add tracked-unrelated
profile_tracked="$(run_runner path)"
printf '%s\n' changed > "$repo_dir/tracked-unrelated"
assert_equal "$(run_runner path)" "$profile_tracked"
[[ "$profile_a" != "$repo_dir"/* ]] || fail 'profile path is inside the checkout'
printf '%s\n' '{ outputs = _: { devShells.changed = {}; }; }' > "$repo_dir/flake.nix"
profile_changed="$(run_runner path)"
[[ "$profile_changed" != "$profile_a" ]] || fail 'flake.nix did not change the profile key'
printf '%s\n' '{ outputs = _: { devShells = {}; }; }' > "$repo_dir/flake.nix"
profile_other_system="$(FAKE_NIX_SYSTEM=aarch64-darwin run_runner path)"
[[ "$profile_other_system" != "$profile_a" ]] || fail 'Nix system did not change the profile key'

: > "$fake_log"
run_runner run -- proof-command 'argument with spaces'
run_runner run -- proof-command second
assert_equal "$(count_matching_lines "$fake_log" $'\targ=--profile\t')" 1
assert_equal "$(count_matching_lines "$fake_log" $'\targ=develop\targ='"$profile_a"$'\targ=-c')" 2
assert_contains "$fake_log" "cwd=$repo_dir"
assert_contains "$fake_log" $'\targ=.#proofs\t'
assert_contains "$fake_log" $'\targ=--no-update-lock-file\targ=--profile\t'
assert_contains "$fake_log" $'\targ=proof-command\targ=argument with spaces'
if grep -Fq -- 'arg=path:' "$fake_log"; then
	fail 'raw path: flake reference was used'
fi

profile_root="$test_dir/failed-state"
fake_log="$test_dir/failed.log"
: > "$fake_log"
set +e
FAKE_NIX_FAIL_INIT=1 run_runner prepare >/dev/null 2>&1
failure_status=$?
set -e
assert_equal "$failure_status" 19
failed_profile="$(run_runner path)"
[[ ! -e "$failed_profile.ready" ]] || fail 'failed initialization left a ready marker'
run_runner prepare >/dev/null
assert_equal "$(count_matching_lines "$fake_log" $'\targ=--profile\t')" 2

profile_root="$test_dir/concurrent-state"
fake_log="$test_dir/concurrent.log"
concurrent_errors="$test_dir/concurrent.err"
: > "$fake_log"
: > "$concurrent_errors"
pids=()
for _ in {1..8}; do
	(FAKE_NIX_INIT_DELAY=0.2 run_runner run -- true) 2>> "$concurrent_errors" &
	pids+=("$!")
done
parallel_status=0
for pid in "${pids[@]}"; do
	wait "$pid" || parallel_status=$?
done
assert_equal "$parallel_status" 0
if [[ -s "$concurrent_errors" ]]; then
	cat "$concurrent_errors" >&2
	fail 'concurrent preparation emitted warnings or errors'
fi
concurrent_profile="$(run_runner path)"
assert_equal "$(count_matching_lines "$fake_log" $'\targ=--profile\t')" 1
assert_equal "$(count_matching_lines "$fake_log" $'\targ=develop\targ='"$concurrent_profile"$'\targ=-c')" 8

profile_root="$test_dir/concurrent-python-state"
fake_log="$test_dir/concurrent-python.log"
concurrent_errors="$test_dir/concurrent-python.err"
: > "$fake_log"
: > "$concurrent_errors"
pids=()
for _ in {1..4}; do
	(BEACONCRYPT_PROOF_PROFILE_LOCK_STYLE=python FAKE_NIX_INIT_DELAY=0.2 \
		run_runner run -- true) 2>> "$concurrent_errors" &
	pids+=("$!")
done
parallel_status=0
for pid in "${pids[@]}"; do
	wait "$pid" || parallel_status=$?
done
assert_equal "$parallel_status" 0
if [[ -s "$concurrent_errors" ]]; then
	cat "$concurrent_errors" >&2
	fail 'Python-lock concurrent preparation emitted warnings or errors'
fi
concurrent_profile="$(run_runner path)"
assert_equal "$(count_matching_lines "$fake_log" $'\targ=--profile\t')" 1
assert_equal "$(count_matching_lines "$fake_log" $'\targ=develop\targ='"$concurrent_profile"$'\targ=-c')" 4

set +e
FAKE_NIX_RUN_STATUS=37 run_runner run -- failing-command 'preserved argument' >/dev/null
run_status=$?
set -e
assert_equal "$run_status" 37
assert_contains "$fake_log" $'\targ=failing-command\targ=preserved argument'

profile_root="$test_dir/dangling-state"
fake_log="$test_dir/dangling.log"
: > "$fake_log"
dangling_profile="$(run_runner prepare)"
dangling_generation="$(readlink -- "$dangling_profile")"
rmdir -- "$dangling_generation"
run_runner prepare >/dev/null
assert_equal "$(count_matching_lines "$fake_log" $'\targ=--profile\t')" 2

profile_root="$test_dir/collision-state"
fake_log="$test_dir/collision.log"
: > "$fake_log"
collision_profile="$(run_runner path)"
mkdir -p -- "$(dirname -- "$collision_profile")"
: > "$collision_profile"
set +e
run_runner prepare >/dev/null 2>&1
collision_status=$?
set -e
assert_equal "$collision_status" 1
rm -f -- "$collision_profile"
run_runner prepare >/dev/null
rm -f -- "$collision_profile.ready"
ln -s -- "$collision_profile.invalid-ready" "$collision_profile.ready"
set +e
run_runner prepare >/dev/null 2>&1
marker_status=$?
set -e
assert_equal "$marker_status" 1

profile_root="$test_dir/fallback-lock-state"
fake_log="$test_dir/fallback-lock.log"
: > "$fake_log"
fallback_profile="$(run_runner path)"
mkdir -p -- "$(dirname -- "$fallback_profile")"
exec 8>> "$fallback_profile.lock"
python3 -c 'import fcntl; fcntl.flock(8, fcntl.LOCK_EX)'
set +e
BEACONCRYPT_PROOF_PROFILE_LOCK_STYLE=python \
	BEACONCRYPT_PROOF_PROFILE_LOCK_TIMEOUT=1 run_runner prepare 8>&- >/dev/null 2>&1
fallback_status=$?
set -e
exec 8>&-
assert_equal "$fallback_status" 1

temporary_root="$test_dir/temporary root"
mkdir -p -- "$temporary_root"
cache_dir="$(TMPDIR="$temporary_root" mktemp -d)"
hint_dir="$(TMPDIR="$temporary_root" mktemp -d)"
set +e
TMPDIR="$temporary_root" CACHE_DIR="$cache_dir" HINT_DIR="$hint_dir" \
	"$runner" _run_in_shell bash -c 'exit 23'
shell_status=$?
set -e
assert_equal "$shell_status" 23
[[ ! -e "$cache_dir" && ! -e "$hint_dir" ]] || fail 'shell-hook temporary directories were not removed'

signal_cache="$(TMPDIR="$temporary_root" mktemp -d)"
signal_hint="$(TMPDIR="$temporary_root" mktemp -d)"
TMPDIR="$temporary_root" CACHE_DIR="$signal_cache" HINT_DIR="$signal_hint" \
	"$runner" _run_in_shell bash -c 'while :; do sleep 1; done' &
signal_runner_pid=$!
sleep 0.1
kill -TERM "$signal_runner_pid"
set +e
wait "$signal_runner_pid"
signal_status=$?
set -e
assert_equal "$signal_status" 143
[[ ! -e "$signal_cache" && ! -e "$signal_hint" ]] || fail 'interrupt left shell-hook temporary directories behind'

unsafe_dir="$test_dir/not-a-mktemp-directory"
mkdir -p -- "$unsafe_dir"
set +e
TMPDIR="$test_dir" CACHE_DIR="$unsafe_dir" "$runner" _run_in_shell true >/dev/null 2>&1
unsafe_status=$?
set -e
assert_equal "$unsafe_status" 1
[[ -d "$unsafe_dir" ]] || fail 'unsafe cleanup path was removed'

set +e
profile_root="$repo_dir/local-profiles" run_runner path >/dev/null 2>&1
inside_status=$?
set -e
assert_equal "$inside_status" 1
[[ ! -e "$repo_dir/local-profiles" ]] || fail 'inside-checkout profile root was created'

for root_path in '///' '/tmp/..'; do
	set +e
	profile_root="$root_path" run_runner path >/dev/null 2>&1
	root_status=$?
	set -e
	assert_equal "$root_status" 1
done

for mode in 0775 0707; do
	profile_root="$test_dir/unsafe-mode-$mode"
	mkdir -p -- "$profile_root"
	chmod "$mode" "$profile_root"
	set +e
	run_runner prepare >/dev/null 2>&1
	mode_status=$?
	set -e
	assert_equal "$mode_status" 1
	chmod 0700 "$profile_root"
done

profile_root="$test_dir/make-state"
fake_log="$test_dir/make.log"
: > "$fake_log"
make_env=(env \
	FAKE_NIX_MODE=1 \
	FAKE_NIX_LOG="$fake_log" \
	NIX="$test_script" \
	BEACONCRYPT_PROOF_PROFILE_ROOT="$profile_root")
repository_root="$(cd -- "$script_dir/.." && pwd -P)"
"${make_env[@]}" make -s -C "$repository_root/beaconcrypt-core" prepare-proof-shell >/dev/null
"${make_env[@]}" make -s -C "$repository_root/beaconcrypt-core" verify-fstar
"${make_env[@]}" make -s -C "$repository_root/beaconcrypt-core" verify-proverif-baseline
"${make_env[@]}" make -s -C "$repository_root/beaconcrypt-core/proofs/ssprove" verify
assert_equal "$(count_matching_lines "$fake_log" $'\targ=--profile\t')" 1
assert_contains "$fake_log" $'\targ=verify-fstar-in-shell'
assert_contains "$fake_log" $'\targ=verify-proverif-scenario-in-shell\targ=PROVERIF_SCENARIO=baseline'
assert_contains "$fake_log" $'\targ=check'

printf 'test-run-proof-shell: ok\n'
