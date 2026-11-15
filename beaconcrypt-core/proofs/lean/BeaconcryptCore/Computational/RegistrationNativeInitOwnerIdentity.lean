-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAdHashIdentity
import BeaconcryptCore.Computational.RegistrationNativeInitTupleSource
import BeaconcryptCore.Computational.PqxdhRootTableInitialization
/-! Current original-source validation identifies the completed binding's exact generated Ed key. The source receipt transports the original Init message; no identity is recovered by parsing opaque AD, and no assumption of injective key generation is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeInitOwnerIdentity
/-- The completed identity is obtained from the same original source Init that passed validation; source metadata equality only transports that existing validation to the retained raw field. -/
theorem completed_identity (started : pqxdh.BeaconStart) (state : registration.BeaconInitState)
    (pin : session.ServerAuthenticationPin) (publicKey : Std.Array U8 32#usize)
    (pending : session.RegistrationBinding) (verified : pqxdh.VerifiedInitKex)
    (digest : Std.Array U8 64#usize) (completed : session.CompletedRegistrationBinding)
    (fixed : RegistrationNativeInitTupleSource.Fixed started pin publicKey state)
    (retained : pending.init_fields.identity_key = state.started.message.identity_key)
    (validated : pqxdh.validate_init_kex started.message = .ok (.Ok verified))
    (resumed : pending.complete digest = .ok completed) :
    completed.beacon_identity_public_key = verified.beacon_identity_public_key := by
  have sameStarted : state.started = started := congrArg Prod.fst fixed
  have identity : pending.init_fields.identity_key = started.message.identity_key :=
    retained.trans (congrArg (fun value : pqxdh.BeaconStart => value.message.identity_key) sameStarted)
  exact RegistrationAdHashIdentity.completed_identity_from_validated pending started.message verified digest completed identity validated resumed

/-- Equality of the exact extracted public-key arrays retains equality of the original generated key vectors; no distributional injectivity of key generation is used. -/
theorem public_key_eq (first second : List.Vector UInt8 32)
    (same : PqxdhRootTableInitialization.rootArray first = PqxdhRootTableInitialization.rootArray second) :
    first = second := by
  apply List.Vector.toList_injective
  simpa only [PqxdhRootTableInitialization.rootArray_bytes] using congrArg absBytes same

end BeaconcryptCore.Computational.RegistrationNativeInitOwnerIdentity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitOwnerIdentity.completed_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitOwnerIdentity.completed_identity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitOwnerIdentity.public_key_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitOwnerIdentity.public_key_eq
