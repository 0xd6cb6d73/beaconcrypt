-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment

/-! Every ML payload emitted by the original outgoing Beacon Init controller has the Beacon role. The property is syntactic over all primitive replies, including failed signing or publication, and does not assume authentication or source security. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax
open RegistrationBeaconInitExecutor
variable {Encoded : Type}
attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.begin_beacon_init

def BeaconRole : Spec.Domain → Prop
  | .inl (.sign _ payload _) => payload.role = .beacon
  | _ => True

private theorem continue_all {Input : Type} (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded)))
    (all : ∀ value, AllQueriesSatisfy (next value) BeaconRole) : AllQueriesSatisfy (continueWith action next) BeaconRole := by
  cases action with
  | ok value => exact all value
  | fail error | div => trivial

private theorem ready_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitReady) : AllQueriesSatisfy (ready encode pending) BeaconRole := by
  unfold ready
  exact continue_all _ _ (fun _ => by trivial)

private theorem signing_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning)
    (role : payload.role = .beacon) : AllQueriesSatisfy (fromSigning encode payload digest pending) BeaconRole := by
  unfold fromSigning
  apply continue_all
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨role, fun _ => ?_⟩
  apply continue_all
  intro effect
  cases effect with
  | Ready selected => exact ready_all encode selected
  | _ => trivial

private theorem hash_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) : AllQueriesSatisfy (fromHash encode pending) BeaconRole := by
  unfold fromHash
  apply continue_all
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun _ => ?_⟩
  apply continue_all
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing_all encode _ _ selected rfl
  | _ => trivial

private theorem fingerprint_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) : AllQueriesSatisfy (fromFingerprint encode pending) BeaconRole := by
  unfold fromFingerprint
  apply continue_all
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun _ => ?_⟩
  apply continue_all
  intro effect
  cases effect with
  | HashRequested selected => exact hash_all encode selected
  | _ => trivial

private theorem ed_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) : AllQueriesSatisfy (fromEd encode pending) BeaconRole := by
  rw [fromEd.eq_def]
  apply continue_all
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun reply => ?_⟩
  cases resumed : pending.resume reply with
  | fail error | div => trivial
  | ok effect => cases effect with
    | Ed25519SigningRequested next => exact ed_all encode next
    | FingerprintRequested selected => exact fingerprint_all encode selected
    | _ => trivial
termination_by edRank pending
decreasing_by exact ed_rank pending reply next resumed

/-- The actual complete outgoing Init contains only Beacon-role ML payloads on every source branch. -/
theorem begin_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    AllQueriesSatisfy (begin encode control inputs coins pin mldsa) BeaconRole := by
  unfold begin
  apply continue_all
  intro effect
  cases effect with
  | Ed25519SigningRequested selected => exact ed_all encode selected
  | _ => trivial

end BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax.begin_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax.begin_all
