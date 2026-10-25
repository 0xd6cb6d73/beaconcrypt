import os
import subprocess

workspace = "/home/user/worktrees/beaconcrypt-row-persistence"
os.chdir(workspace)
os.environ["PATH"] = ":".join([
    "/tmp/bc-arc-scratch/row-persistence-20261025",
    "/home/user/.rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin",
    "/home/user/.cargo/bin",
    "/nix/store/9wyldz5qids294k9h5qcg1f72i52jidi-gnumake-4.4.1/bin",
    os.environ["PATH"],
])
os.environ.update({
    "TMPDIR": "/tmp/bc-arc-scratch/row-persistence-20261025/hybrid",
    "RUSTFLAGS": "-C linker-features=-lld",
    "CARGO_PROFILE_TEST_OPT_LEVEL": "0",
    "CARGO_PROFILE_TEST_DEBUG": "0",
    "CARGO_BUILD_JOBS": "1",
    "RUST_TEST_THREADS": "1",
})
targets = [
    "authentication", "beacon", "cached_row_persistence", "codec", "construction", "general_registration_admission",
    "message_size", "mldsa", "persistence_properties", "properties", "protocol",
    "ratchet_properties", "raw_receive", "record_opening", "registration_completion",
    "registration_properties", "registration_response_alias", "rooterberg", "row_persistence",
    "server", "wycheproof",
]
# Proof source-fidelity targets are deliberately excluded at the owner's request.
args = ["--lib", '--config=profile.test.package."*".opt-level=1']
args += ["--test=" + target for target in targets]

os.environ["NEXTEST_TEST_THREADS"] = "1"
os.environ["NEXTEST_RETRIES"] = "0"
config = "/tmp/bc-arc-scratch/row-persistence-20261025/nextest.toml"
nextest_args = ["--config-file=" + config, "--fail-fast"]
commands = [
    ["cargo", "mutants", "--workspace", "--baseline=skip", "--output=/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/native-audit",
     "--copy-target=false", "--cap-lints=false", "--jobs=4", "--jobserver-tasks=4",
     "--timeout=180", "--build-timeout=600", "--test-tool=nextest",
     *["--cargo-arg=" + arg for arg in args],
     *["--cargo-test-arg=" + arg for arg in nextest_args]],
]
for command in commands:
    print("RUN:", " ".join(command), flush=True)
    with open("/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/native-audit.log", "w") as log:
        result = subprocess.call(command, stdout=log, stderr=subprocess.STDOUT)
    print("EXIT:", result, flush=True)
    if result:
        raise SystemExit(result)
