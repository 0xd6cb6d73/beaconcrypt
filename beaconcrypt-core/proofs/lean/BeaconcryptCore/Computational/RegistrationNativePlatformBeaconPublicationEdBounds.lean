-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter
/-! Literal effectful Init publication issues at most three attached Ed requests. The source rank bounds every continuation, including failed signatures and failed final writers. Hash, ML and external serializer requests contribute zero to this signing count. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationEdBounds
open RegistrationNativePlatformBeaconPublication
open RegistrationNativePlatformWriter (Spec cryptoLift init)
variable {E : Type}
attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.BeaconEd25519Signing.resume registration.begin_beacon_init

def IsSign : (Spec E).Domain → Prop
  | .inl (.inr _) => True
  | _ => False
instance : DecidablePred (IsSign (E := E)) := fun query => by
  cases query with
  | inr query => simp only [IsSign]; infer_instance
  | inl query => cases query with
    | inr query => simp only [IsSign]; infer_instance
    | inl query => cases query <;> simp only [IsSign] <;> infer_instance

private theorem continue_bound {Input A : Type} (action : RustM Input)
    (next : Input → OracleComp (Spec E) (RustM (RegistrationBeaconInitExecutor.Result A))) (cap : Nat)
    (bounded : ∀ value, (next value).IsQueryBoundP (IsSign (E := E)) cap) :
    (continueWith action next).IsQueryBoundP (IsSign (E := E)) cap := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => trivial

theorem init_bound (view : registration.SignedInitView) : (init E view).IsQueryBoundP (IsSign (E := E)) 0 := by
  unfold init
  apply (isQueryBoundP_false _ 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _
  simp [RegistrationNativePlatformWriter.writerLift, IsSign]

private theorem ready_bound (pending : registration.BeaconInitReady) :
    (ready (init E) pending).IsQueryBoundP (IsSign (E := E)) 0 := by
  unfold ready
  apply continue_bound
  intro view
  exact isQueryBoundP_bind (n := 0) (m := 0) (init_bound (E := E) view) (fun _ _ => isQueryBoundP_pure _ _ _)

private theorem signing_bound (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    (fromSigning (cryptoLift (E := E)) (init E) payload digest pending).IsQueryBoundP (IsSign (E := E)) 0 := by
  unfold fromSigning
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsSign, not_false_eq_true, true_or, ite_false]
  refine ⟨trivial, fun signature => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | Ready selected => exact ready_bound selected
  | _ => trivial

private theorem hash_bound (pending : registration.BeaconInitHash) :
    (fromHash (cryptoLift (E := E)) (init E) pending).IsQueryBoundP (IsSign (E := E)) 0 := by
  unfold fromHash
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsSign, not_false_eq_true, true_or, ite_false]
  refine ⟨trivial, fun digest => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing_bound _ _ selected
  | _ => trivial

private theorem fingerprint_bound (pending : registration.BeaconFingerprint) :
    (fromFingerprint (cryptoLift (E := E)) (init E) pending).IsQueryBoundP (IsSign (E := E)) 0 := by
  unfold fromFingerprint
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsSign, not_false_eq_true, true_or, ite_false]
  refine ⟨trivial, fun digest => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | HashRequested selected => exact hash_bound selected
  | _ => trivial

theorem ed_bound (pending : registration.BeaconEd25519Signing) :
    (fromEd (cryptoLift (E := E)) (init E) pending).IsQueryBoundP (IsSign (E := E)) (RegistrationBeaconInitExecutor.edRank pending) := by
  rw [fromEd.eq_def]
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsSign, not_true_eq_false, false_or, ite_true]
  refine ⟨?_, fun reply => ?_⟩
  · cases stage : pending.stage <;> simp [RegistrationBeaconInitExecutor.edRank, stage]
  · cases actual : pending.resume reply with
    | fail error | div => trivial
    | ok effect => cases effect with
      | Ed25519SigningRequested next =>
        exact (ed_bound next).mono (by have decrease := RegistrationBeaconInitExecutor.ed_rank pending reply next actual; omega)
      | FingerprintRequested next => exact (fingerprint_bound next).mono (Nat.zero_le _)
      | _ => trivial
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next actual

theorem begin_bound (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    (RegistrationNativePlatformWriter.begin E control inputs coins pin mldsa).IsQueryBoundP (IsSign (E := E)) 3 := by
  unfold RegistrationNativePlatformWriter.begin begin
  apply continue_bound
  intro effect
  cases effect with
  | Ed25519SigningRequested selected => exact (ed_bound selected).mono (by cases stage : selected.stage <;> simp [RegistrationBeaconInitExecutor.edRank, stage])
  | _ => trivial
end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationEdBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationEdBounds.init_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationEdBounds.init_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationEdBounds.ed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationEdBounds.ed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationEdBounds.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationEdBounds.begin_bound
