-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs

set_option warningAsError true

-- Aeneas calls an external constant initializer through RustM. This namespace-local alias returns the existing extracted constant without introducing a parser or primitive contract.
noncomputable def beaconcrypt_parse.beaconcrypt_core.transport.MAX_MESSAGE_SIZE :
    Aeneas.Std.RustM Aeneas.Std.Usize :=
  Aeneas.Std.RustM.ok _root_.beaconcrypt_core.transport.MAX_MESSAGE_SIZE
