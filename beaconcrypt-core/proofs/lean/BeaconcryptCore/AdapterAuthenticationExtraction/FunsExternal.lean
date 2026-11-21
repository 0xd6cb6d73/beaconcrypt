-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs
import BeaconcryptCore.AdapterAuthenticationExtraction.Types

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace beaconcrypt.auth

/-!
Explicit implementations of the selected adapter's two foreign primitive calls. They are parameters, not primitive-security assumptions or global constants. The existing core function names resolve through the maintained extraction imported above. `RustM` retains ordinary return, failure and divergence; this deterministic interface does not itself model probabilistic oracle state or physical primitive execution.
-/

class Operations where
  hash : beaconcrypt_core.registration.HashRequest →
    RustM (core.option.Option (Array Std.U8 64#usize))
  verify : beaconcrypt_core.registration.MldsaVerificationRequest → RustM Bool

def execute_hash [operations : Operations]
    (request : beaconcrypt_core.registration.HashRequest) :
    RustM (core.option.Option (Array Std.U8 64#usize)) :=
  operations.hash request

def verify_requested [operations : Operations]
    (request : beaconcrypt_core.registration.MldsaVerificationRequest) : RustM Bool :=
  operations.verify request

end beaconcrypt.auth
