# Normal reconciliation of fail-stop scope and serial CI

This normal merge combines reviewed fail-stop topic `71e23c56c52134d86103e08674197ab724404976` with reviewed integration `d074f31a337c1fd99a621e430e21778a75c6e422`. The only manual conflict was the final append in `doc/formal-verification-analysis.md`; both reviewed sections are retained unchanged. The merged inventory retains both parents’ entries with their correct digests.

The source-identity receipt verifies all 1,356 Lean-related files against the CI parent and all 235 ProVerif-related files against the fail-stop parent. CI workflow, Makefile, inventory checker, transcript tests and trust-boundary documentation are byte-identical to the CI parent. No theorem, process, query, CI gate or checker behavior changes in this reconciliation.

The combined tree passed all 28 transcript fidelity tests and the reviewed-inventory gate in the locked minimal Nix proof environment. Complete output and command/timing receipt are retained here. The reviewed source artifacts are unchanged, so no Lean or ProVerif solver result is claimed to have been rerun. This integration does not close the outstanding source abstractions or global computational composition.
