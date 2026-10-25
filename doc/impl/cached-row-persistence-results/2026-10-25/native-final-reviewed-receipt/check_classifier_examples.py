"""Small synthetic diagnostic checks; invokes no native build or test suite."""

import json
from finalize_native_audit import diagnostics, REVIEWED_SOURCE_HEADERS


phases = [{"phase": "Build", "process_status": {"Failure": 101}}]
source_location = "\n  --> example/src/lib.rs:10:4\n"
checked = []


def check(name, text, expected, phase_results=phases):
    actual = diagnostics(text, phase_results)["classification"]
    if actual != expected:
        raise AssertionError(f"{name}: expected {expected}, got {actual}")
    checked.append({"name": name, "expected": expected, "actual": actual})


for index, header in enumerate(sorted(REVIEWED_SOURCE_HEADERS)):
    text = header + source_location
    check(f"reviewed_header_{index}", text, "source_compile_error")
    check(f"missing_location_{index}", header, "unclassified_requires_review")
    check(f"wrong_exit_{index}", text, "unclassified_requires_review",
          [{"phase": "Build", "process_status": {"Failure": 137}}])
    check(f"test_failure_{index}", text, "unclassified_requires_review",
          [{"phase": "Test", "process_status": {"Failure": 101}}])
    check(f"extra_unknown_error_{index}", text + "error: unexplained runner failure\n",
          "unclassified_requires_review")
    for category, extra in {
        "disk": "error: No space left on device (os error 28)",
        "memory": "memory allocation of 65536 bytes failed",
        "compiler_ice": "error: internal compiler error: unexpected panic",
        "compiler_panic": "thread 'rustc' panicked at compiler/rustc_middle/src/lib.rs:20:1",
        "build_signal": "process didn't exit successfully (signal: 9, SIGKILL: kill)",
        "linker": "error: linking with `cc` failed: exit status: 1",
        "network": "error: failed to download from registry",
    }.items():
        check(f"{category}_overrides_source_{index}", text + extra + "\n", "infrastructure_failure")

for index, text in enumerate([
    "error: cannot find macro compiler executable",
    "error: this arithmetic operation will overflow memory allocator",
    "error: `<` is interpreted as an unknown tool error",
    "error: could not compile `example` (lib) due to 1 previous error",
]):
    check(f"nonmatching_header_{index}", text + source_location, "unclassified_requires_review")

print(json.dumps({"passed": len(checked), "cases": checked}, indent=2))
