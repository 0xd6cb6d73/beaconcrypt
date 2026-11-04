-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter
/-! Exact shared-hash budgets for the literal effectful Init publication tree. Attached Ed signing and mutable serialization do not call the shared hash service; fingerprint and ML transcript hashing contribute the two possible calls, including every rejected or failed prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationHashBounds
open RegistrationNativePlatformBeaconPublication
open RegistrationNativePlatformWriter (Spec cryptoLift init)
variable {E : Type}
attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.BeaconEd25519Signing.resume registration.begin_beacon_init

def IsHash : (Spec E).Domain → Prop
  | .inl (.inl (.hash _)) => True
  | _ => False
instance : DecidablePred (IsHash (E := E)) := fun query => by
  cases query with
  | inr query => simp only [IsHash]; infer_instance
  | inl query => cases query with
    | inr query => simp only [IsHash]; infer_instance
    | inl query => cases query <;> simp only [IsHash] <;> infer_instance

private theorem continue_bound {Input A : Type} (action : RustM Input)
    (next : Input → OracleComp (Spec E) (RustM (RegistrationBeaconInitExecutor.Result A))) (cap : Nat)
    (bounded : ∀ value, (next value).IsQueryBoundP (IsHash (E := E)) cap) :
    (continueWith action next).IsQueryBoundP (IsHash (E := E)) cap := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => trivial

/-- The extracted mutable Init serializer is entirely in the external writer branch. -/
theorem init_bound (view : registration.SignedInitView) : (init E view).IsQueryBoundP (IsHash (E := E)) 0 := by
  unfold init
  apply (isQueryBoundP_false _ 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _
  simp [RegistrationNativePlatformWriter.writerLift, IsHash]

private theorem ready_bound (pending : registration.BeaconInitReady) :
    (ready (init E) pending).IsQueryBoundP (IsHash (E := E)) 0 := by
  unfold ready
  apply continue_bound
  intro view
  exact isQueryBoundP_bind (n := 0) (m := 0) (init_bound (E := E) view) (fun _ _ => isQueryBoundP_pure _ _ _)

private theorem signing_bound (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    (fromSigning (cryptoLift (E := E)) (init E) payload digest pending).IsQueryBoundP (IsHash (E := E)) 0 := by
  unfold fromSigning
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsHash, not_false_eq_true, true_or, ite_false]
  refine ⟨trivial, fun signature => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | Ready selected => exact ready_bound selected
  | _ => trivial

private theorem hash_bound (pending : registration.BeaconInitHash) :
    (fromHash (cryptoLift (E := E)) (init E) pending).IsQueryBoundP (IsHash (E := E)) 1 := by
  unfold fromHash
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsHash, not_true_eq_false, false_or, ite_true, Nat.sub_self]
  refine ⟨by omega, fun digest => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing_bound _ _ selected
  | _ => trivial

private theorem fingerprint_bound (pending : registration.BeaconFingerprint) :
    (fromFingerprint (cryptoLift (E := E)) (init E) pending).IsQueryBoundP (IsHash (E := E)) 2 := by
  unfold fromFingerprint
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsHash, not_true_eq_false, false_or, ite_true]
  refine ⟨by omega, fun digest => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | HashRequested selected => exact hash_bound selected
  | _ => trivial

/-- All attached-signing continuations precede at most the same two actual hash stages. -/
theorem ed_bound (pending : registration.BeaconEd25519Signing) :
    (fromEd (cryptoLift (E := E)) (init E) pending).IsQueryBoundP (IsHash (E := E)) 2 := by
  rw [fromEd.eq_def]
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsHash, not_false_eq_true, true_or, ite_false]
  refine ⟨trivial, fun reply => ?_⟩
  cases actual : pending.resume reply with
  | fail error | div => trivial
  | ok effect => cases effect with
    | Ed25519SigningRequested next => exact ed_bound next
    | FingerprintRequested next => exact fingerprint_bound next
    | _ => trivial
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next actual

/-- Actual source Init publication has two shared hash calls even with repeated signing/writer failures. -/
theorem begin_bound (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    (RegistrationNativePlatformWriter.begin E control inputs coins pin mldsa).IsQueryBoundP (IsHash (E := E)) 2 := by
  unfold RegistrationNativePlatformWriter.begin begin
  apply continue_bound
  intro effect
  cases effect with
  | Ed25519SigningRequested selected => exact ed_bound selected
  | _ => trivial
end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationHashBounds.init_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationHashBounds.init_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationHashBounds.ed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationHashBounds.ed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationHashBounds.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationHashBounds.begin_bound
