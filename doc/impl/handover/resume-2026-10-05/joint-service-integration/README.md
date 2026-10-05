# Joint-service schedule integration receipt

Source checkpoint: `1e1e1c49ff5a7e2c52f57b5e5add591fce5bd192`. Integration parent: `73682c26b72a1509a9a58e36388f06fc2faa45e4`. Nine source-identical modules add 79 guarded statements; all 804 retained transitive dependencies match the reviewed lane. The root check additionally reuses 411 source-identical existing modules from the preceding maintained integration.

All nine direct Lean checks and the combined root check passed with `-j1 -M8000` and the shared lock. The inventory passed in the minimal locked proof shell with `SHELL=/run/current-system/sw/bin/bash` for this NixOS host. The first attempts found no host `make`, then no `/bin/bash`, before reaching the checker; neither is a proof failure or reported success. No aggregate build, Rust/PV rerun or mutation test was performed for these unchanged interfaces.

`direct-checks.json` records exact source and log hashes, commands and exits. `inventory.txt` records the focused Make result. The independent review is added before publication. The [integration guide](../../../joint-service-schedule-integration.md) states scope, query bounds, source correspondence and remaining global obligations.
