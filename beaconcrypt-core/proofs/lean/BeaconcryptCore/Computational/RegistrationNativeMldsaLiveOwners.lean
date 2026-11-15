-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap

/-! Beacon ML credential liveness and generation-suffix claims are retired: current Beacon owners contain no ML credential. The ordinary callback classification remains available to the Server-only table interpreter. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners

def NonCreate : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.create _ _ _) => False
  | _ => True

end BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners
