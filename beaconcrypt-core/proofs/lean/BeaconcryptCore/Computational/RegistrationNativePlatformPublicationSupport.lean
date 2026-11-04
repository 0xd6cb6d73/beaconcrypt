-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativeKemPublication
/-! Success-only source data provenance for the effectful publication controller is derived by replaying the same actual replies in its free Core executor. This is a support receipt, not an equality that erases writer failures or poststates. The writer condition is local to its successful signed-view encoding. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationSupport
open RegistrationBeaconInitExecutor (Spec Result)
variable {I S T P A B Encoded : Type} {base : OracleSpec I}
abbrev Work (S T P : Type) (base : OracleSpec I) (A : Type) := StateT S (StateT T (StateT P (OracleComp base))) A

def Possible (work : Work S T P base A) (value : A) : Prop :=
  ∃ first second previous result, result ∈ support (((work.run first).run second).run previous) ∧ result.1.1.1 = value

private theorem pure_possible (value actual : A) (possible : Possible (S := S) (T := T) (P := P) (base := base) (pure value) actual) :
    value = actual := by
  obtain ⟨first, second, previous, result, reached, same⟩ := possible
  simp only [StateT.run_pure, mem_support_pure_iff] at reached
  cases reached
  exact same

private theorem bind_possible (work : Work S T P base A) (next : A → Work S T P base B) (value : B)
    (possible : Possible (work >>= next) value) :
    ∃ middle, Possible work middle ∧ Possible (next middle) value := by
  obtain ⟨first, second, previous, result, reached, same⟩ := possible
  simp only [StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨middle, called, continued⟩ := reached
  exact ⟨middle.1.1.1, ⟨first, second, previous, middle, called, rfl⟩,
    ⟨middle.1.1.2, middle.1.2, middle.2, result, continued, same⟩⟩

private theorem continue_possible {Input : Type} (action : RustM Input)
    (next : Input → Work S T P base (RustM (Result Encoded))) (published : registration.PublishedBeaconInit Encoded)
    (possible : Possible (RegistrationNativePlatformBeaconPublication.continueWith action next) (.ok (.Ok published))) :
    ∃ value, action = .ok value ∧ Possible (next value) (.ok (.Ok published)) := by
  cases action with
  | fail error => cases pure_possible _ _ possible
  | div => cases pure_possible _ _ possible
  | ok value => exact ⟨value, rfl, possible⟩

attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume registration.BeaconMldsaSigning.resume

variable (impl : QueryImpl Spec (Work S T P base))
    (encode : registration.SignedInitView → Work S T P base (RustM (core.option.Option Encoded)))
    (pureEncode : registration.SignedInitView → core.option.Option Encoded)
    (encoding : ∀ view bytes, Possible (encode view) (.ok (.Some bytes)) → pureEncode view = .Some bytes)

include encoding

private theorem ready (pending : registration.BeaconInitReady) (published : registration.PublishedBeaconInit Encoded)
    (possible : Possible (RegistrationNativePlatformBeaconPublication.ready encode pending) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationBeaconInitExecutor.ready pureEncode pending) := by
  obtain ⟨view, requested, continued⟩ := continue_possible pending.message _ published possible
  obtain ⟨encoded, written, returned⟩ := bind_possible (encode view) _ _ continued
  have resultEq := pure_possible _ _ returned
  cases encoded with
  | fail error | div => cases resultEq
  | ok optional => cases optional with
    | none => simp [registration.BeaconInitReady.publish] at resultEq
    | some bytes =>
      have output : pureEncode view = .Some bytes := encoding view bytes written
      simp only [RegistrationBeaconInitExecutor.ready, RegistrationBeaconInitExecutor.continueWith, requested, output]
      rw [mem_support_pure_iff]
      exact resultEq.symm

omit encoding in
private theorem continue_replay {Input : Type} (action : RustM Input)
    (next : Input → Work S T P base (RustM (Result Encoded)))
    (old : Input → OracleComp Spec (RustM (Result Encoded)))
    (published : registration.PublishedBeaconInit Encoded)
    (replay : ∀ value, Possible (next value) (.ok (.Ok published)) → .ok (.Ok published) ∈ support (old value))
    (possible : Possible (RegistrationNativePlatformBeaconPublication.continueWith action next) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationBeaconInitExecutor.continueWith action old) := by
  obtain ⟨value, actual, continued⟩ := continue_possible action next published possible
  simp only [RegistrationBeaconInitExecutor.continueWith, actual]
  exact replay value continued

private theorem signing (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) (published : registration.PublishedBeaconInit Encoded)
    (possible : Possible (RegistrationNativePlatformBeaconPublication.fromSigning impl encode payload digest pending) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationBeaconInitExecutor.fromSigning pureEncode payload digest pending) := by
  unfold RegistrationNativePlatformBeaconPublication.fromSigning RegistrationBeaconInitExecutor.fromSigning at *
  apply continue_replay _ _ _ published _ possible
  intro request called
  obtain ⟨signature, _queried, continued⟩ := bind_possible _ _ _ called
  rw [mem_support_bind_iff]
  refine ⟨signature, mem_support_query _ _, ?_⟩
  apply continue_replay _ _ _ published _ continued
  intro effect resumed
  cases effect
  all_goals first
    | exact ready encode pureEncode encoding _ published resumed
    | cases pure_possible _ _ resumed

private theorem hash (pending : registration.BeaconInitHash) (published : registration.PublishedBeaconInit Encoded)
    (possible : Possible (RegistrationNativePlatformBeaconPublication.fromHash impl encode pending) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationBeaconInitExecutor.fromHash pureEncode pending) := by
  unfold RegistrationNativePlatformBeaconPublication.fromHash RegistrationBeaconInitExecutor.fromHash at *
  apply continue_replay _ _ _ published _ possible
  intro request called
  obtain ⟨digest, _queried, continued⟩ := bind_possible _ _ _ called
  rw [mem_support_bind_iff]
  refine ⟨digest, mem_support_query _ _, ?_⟩
  apply continue_replay _ _ _ published _ continued
  intro effect resumed
  cases effect
  all_goals first
    | exact signing impl encode pureEncode encoding _ _ _ published resumed
    | cases pure_possible _ _ resumed

private theorem fingerprint (pending : registration.BeaconFingerprint) (published : registration.PublishedBeaconInit Encoded)
    (possible : Possible (RegistrationNativePlatformBeaconPublication.fromFingerprint impl encode pending) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationBeaconInitExecutor.fromFingerprint pureEncode pending) := by
  unfold RegistrationNativePlatformBeaconPublication.fromFingerprint RegistrationBeaconInitExecutor.fromFingerprint at *
  apply continue_replay _ _ _ published _ possible
  intro request called
  obtain ⟨digest, _queried, continued⟩ := bind_possible _ _ _ called
  rw [mem_support_bind_iff]
  refine ⟨digest, mem_support_query _ _, ?_⟩
  apply continue_replay _ _ _ published _ continued
  intro effect resumed
  cases effect
  all_goals first
    | exact hash impl encode pureEncode encoding _ published resumed
    | cases pure_possible _ _ resumed

private theorem ed (pending : registration.BeaconEd25519Signing) (published : registration.PublishedBeaconInit Encoded)
    (possible : Possible (RegistrationNativePlatformBeaconPublication.fromEd impl encode pending) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationBeaconInitExecutor.fromEd pureEncode pending) := by
  rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def, RegistrationBeaconInitExecutor.fromEd.eq_def] at *
  apply continue_replay _ _ _ published _ possible
  intro request called
  obtain ⟨reply, _queried, continued⟩ := bind_possible _ _ _ called
  rw [mem_support_bind_iff]
  refine ⟨reply, mem_support_query _ _, ?_⟩
  generalize actual : pending.resume reply = action at continued ⊢
  cases action with
  | fail error =>
    cases pure_possible _ _ continued
  | div =>
    cases pure_possible _ _ continued
  | ok effect => cases effect with
    | Ed25519SigningRequested next =>
        exact ed next published continued
    | FingerprintRequested next =>
        exact fingerprint impl encode pureEncode encoding next published continued
    | _ =>
        cases pure_possible _ _ continued
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next actual

/-- Every successful effectful publication has the same successful Core publication using its locally proved pure encoding. This receipt does not remove any failed writer outcome from the actual execution. -/
theorem begin (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (published : registration.PublishedBeaconInit Encoded)
    (possible : Possible (RegistrationNativePlatformBeaconPublication.begin impl encode control inputs coins pin mldsa) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationBeaconInitExecutor.begin pureEncode control inputs coins pin mldsa) := by
  unfold RegistrationNativePlatformBeaconPublication.begin RegistrationBeaconInitExecutor.begin at *
  apply continue_replay _ _ _ published _ possible
  intro effect continued
  cases effect
  all_goals first
    | exact ed impl encode pureEncode encoding _ published continued
    | cases pure_possible _ _ continued

/-- Successful dynamic source publication retains the literal generated PQ payload, derived through every actual signing continuation. -/
theorem begin_key (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (published : registration.PublishedBeaconInit Encoded)
    (possible : Possible (RegistrationNativePlatformBeaconPublication.begin impl encode control inputs coins pin mldsa) (.ok (.Ok published))) :
    RegistrationNativeKemPublication.PublishedKey pureEncode (RegistrationRootInput.pqKey inputs.pq_public_key) published :=
  RegistrationNativeKemPublication.begin_key pureEncode control inputs coins pin mldsa published
    (begin impl encode pureEncode encoding control inputs coins pin mldsa published possible)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationSupport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationSupport.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationSupport.begin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationSupport.begin_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationSupport.begin_key
