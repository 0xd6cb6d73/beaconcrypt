-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSigningContinuations

/-! The real/censored Init states differ only in the attached one-time field. This module retains their shared stripping map. The removed Beacon ML request, signing tail and signature-width publication claims are retired; the current request-hash/Ready pairing is in IdentityHashPair. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair
open BeaconcryptCore.Refinement
variable {E Platform : Type}

def stripState (before : registration.BeaconInitState) : registration.BeaconInitState :=
  {before with one_time_key := Std.Array.repeat 98#usize 0#u8}
end BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair
