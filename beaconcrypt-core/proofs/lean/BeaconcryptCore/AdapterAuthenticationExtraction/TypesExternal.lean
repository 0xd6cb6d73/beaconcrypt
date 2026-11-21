-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Types

set_option warningAsError true

/-!
The production adapter's selected function uses the same Rust core types as the maintained core extraction. Its external dependency names resolve directly to those existing definitions without introducing new representations. The extraction runner checks the generated external-type roster before installing output.
-/
