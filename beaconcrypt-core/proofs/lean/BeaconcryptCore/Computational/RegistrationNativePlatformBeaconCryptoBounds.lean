-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter

/-! The actual stateful Init publication has at most six crypto requests; every literal mutable writer request is retained and counted separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconCryptoBounds
open RegistrationNativePlatformBeaconPublication
open RegistrationBeaconInitExecutor (edRank ed_rank Result)
open RegistrationNativePlatformWriter (Spec cryptoLift init)
variable {E Input : Type}
def IsCrypto : (Spec E).Domain → Prop
  | .inl _ => True
  | .inr _ => False
instance : DecidablePred (IsCrypto (E := E)) := fun query => by
  cases query <;> dsimp [IsCrypto] <;> infer_instance
attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume registration.BeaconMldsaSigning.resume

private theorem continue_bound (action : RustM Input)
    (next : Input → OracleComp (Spec E) (RustM (Result (alloc.vec.Vec U8)))) (count : Nat)
    (bounded : ∀ value, (next value).IsQueryBoundP (IsCrypto (E := E)) count) :
    (continueWith action next).IsQueryBoundP (IsCrypto (E := E)) count := by
  cases action with
  | ok value => exact bounded value
  | fail error => trivial
  | div => trivial

private theorem ready_bound (pending : registration.BeaconInitReady) : (ready (init E) pending).IsQueryBoundP (IsCrypto (E := E)) 0 := by
  unfold ready
  apply continue_bound
  intro view
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · unfold init
    apply (isQueryBoundP_false _ 0).simulateQ_of_step (fun _ impossible => impossible.elim)
    intro query _
    simp [RegistrationNativePlatformWriter.writerLift, IsCrypto]
  · intro result _
    trivial

private theorem signing_bound (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning) :
    (fromSigning (cryptoLift (E := E)) (init E) payload digest pending).IsQueryBoundP (IsCrypto (E := E)) 1 := by
  unfold fromSigning
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsCrypto, ite_true]
  refine ⟨by decide, fun signature => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | Ready selected => exact ready_bound selected
  | _ => trivial

private theorem hash_bound (pending : registration.BeaconInitHash) : (fromHash (cryptoLift (E := E)) (init E) pending).IsQueryBoundP (IsCrypto (E := E)) 2 := by
  unfold fromHash
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsCrypto, ite_true]
  refine ⟨by decide, fun digest => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing_bound _ _ selected
  | _ => trivial

private theorem fingerprint_bound (pending : registration.BeaconFingerprint) : (fromFingerprint (cryptoLift (E := E)) (init E) pending).IsQueryBoundP (IsCrypto (E := E)) 3 := by
  unfold fromFingerprint
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsCrypto, ite_true]
  refine ⟨by decide, fun digest => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | HashRequested selected => exact hash_bound selected
  | _ => trivial

/-- The original attached-signing rank bounds every actual outgoing prefix, without assuming replies succeed. -/
theorem ed_bound (pending : registration.BeaconEd25519Signing) : (fromEd (cryptoLift (E := E)) (init E) pending).IsQueryBoundP (IsCrypto (E := E)) (edRank pending + 3) := by
  rw [fromEd.eq_def]
  apply continue_bound
  intro request
  simp only [cryptoLift, isQueryBoundP_query_bind_iff, IsCrypto, ite_true]
  refine ⟨by omega, fun reply => ?_⟩
  cases actual : pending.resume reply with
  | fail error => trivial
  | div => trivial
  | ok effect =>
      cases effect with
      | Ed25519SigningRequested next => exact (ed_bound next).mono (by have := ed_rank pending reply next actual; omega)
      | FingerprintRequested selected =>
          apply (fingerprint_bound selected).mono
          have positive : 1 ≤ edRank pending := by cases stage : pending.stage <;> simp [edRank, stage]
          omega
      | _ => trivial
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

attribute [local irreducible] registration.begin_beacon_init

/-- The literal native begin gate has the six-callback allowance on all error and optional-failure branches. -/
theorem begin_bound (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    (RegistrationNativePlatformWriter.begin E control inputs coins pin mldsa).IsQueryBoundP (IsCrypto (E := E)) 6 := by
  unfold RegistrationNativePlatformWriter.begin begin
  apply continue_bound
  intro effect
  cases effect with
  | Ed25519SigningRequested pending =>
      apply (ed_bound pending).mono
      cases stage : pending.stage <;> simp [edRank, stage]
  | _ => trivial

end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconCryptoBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconCryptoBounds.ed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconCryptoBounds.ed_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconCryptoBounds.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconCryptoBounds.begin_bound
