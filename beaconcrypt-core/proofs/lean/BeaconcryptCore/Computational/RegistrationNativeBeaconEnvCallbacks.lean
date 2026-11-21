-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView

/-! Every concrete Beacon callback retains the exact source query and protocol state when its unrelated record-kind analysis input is cleared. Actual agreement and signing histories remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks
open RegistrationNativeBeaconFrontend (M Trusted Owner)
open RegistrationNativeBeaconEnvView (Stable)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- The actual shared World effect ignores the separate local record-kind ledger. -/
theorem effect_stable (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Stable (RegistrationNativeBeaconFrontend.effect query : M n KemSK mlSource Auxiliary _) :=
  RegistrationNativeBeaconEnvView.lift_stable _

/-- Generated KEM callbacks retain their exact source request and reply. -/
theorem kem_stable (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Stable (RegistrationNativeBeaconFrontend.kem query : M n KemSK mlSource Auxiliary _) :=
  RegistrationNativeBeaconEnvView.lift_stable _

/-- Actual local randomness keeps every original trusted draw. -/
theorem sample_stable (work : ProbComp Value) :
    Stable (RegistrationNativeBeaconFrontend.sample work : M n KemSK mlSource Auxiliary Value) :=
  RegistrationNativeBeaconEnvView.program_stable _ (fun query => effect_stable (.inl query)) work

/-- Hashing uses the literal source bytes and the existing shared World cache. -/
theorem hash_stable (request : registration.HashRequest) :
    Stable (RegistrationNativeBeaconFrontend.hash request : M n KemSK mlSource Auxiliary _) :=
  effect_stable _

/-- Phase replacement retains the full owner roster and all local Env coordinates. -/
theorem phase_stable (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    Stable (RegistrationNativeBeaconFrontend.updatePhase index phase : M n KemSK mlSource Auxiliary Unit) :=
  RegistrationNativeBeaconEnvView.modify_stable _

/-- Actual Ed signing history is retained before every native writer or packing failure. -/
theorem log_stable (index : Nat) (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Stable (RegistrationNativeBeaconFrontend.logEd index message signature : M n KemSK mlSource Auxiliary Unit) :=
  RegistrationNativeBeaconEnvView.modify_stable _

/-- All actual mandatory incoming authentication callbacks preserve their literal optional reply. -/
theorem authentication_stable (setup : Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    Stable (RegistrationNativeBeaconFrontend.authentication setup mlSource query : M n KemSK mlSource Auxiliary _) := by
  cases query with
  | hash request =>
      unfold RegistrationNativeBeaconFrontend.authentication
      apply RegistrationNativeBeaconEnvView.bind_stable
      · exact hash_stable request
      · intro digest; exact RegistrationNativeBeaconEnvView.pure_stable _
  | mldsa request | ed25519 request => exact RegistrationNativeBeaconEnvView.pure_stable _

/-- Ordinary local DH and indexed KEM callbacks keep all actual optional errors and source queries. -/
theorem primitive_stable (setup : Setup base KemSK) (owner : Owner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Stable (RegistrationNativeBeaconFrontend.primitive setup owner oneTime query : M n KemSK mlSource Auxiliary _) := by
  unfold RegistrationNativeBeaconFrontend.primitive
  apply RegistrationNativeBeaconEnvView.program_stable
  intro lower
  cases lower with
  | inl other => exact sample_stable _
  | inr other => exact kem_stable _

/-- The actual agreement primitive result is independent of unrelated instrumentation. -/
theorem agreement_core_stable (setup : Setup base KemSK) (owner : Owner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Stable (RegistrationNativeBeaconFrontend.agreementCore setup owner oneTime query : M n KemSK mlSource Auxiliary _) := by
  cases query <;> first
    | exact primitive_stable setup owner oneTime _
    | exact RegistrationNativeBeaconEnvView.pure_stable _

/-- Actual chronological agreement requests stay retained and do not read the separate record-kind ledger. -/
theorem agreement_stable (setup : Setup base KemSK) (owner : Owner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Stable (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query : M n KemSK mlSource Auxiliary _) := by
  unfold RegistrationNativeBeaconFrontend.agreement
  apply RegistrationNativeBeaconEnvView.bind_stable
  · exact RegistrationNativeBeaconEnvView.update_stable _ (fun _ => rfl)
  · intro result; exact agreement_core_stable setup owner oneTime query

/-- Every actual first-record callback retains its original hash, primitive reply and optional error. -/
theorem record_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) :
    Stable (RegistrationNativeBeaconFrontend.record setup wire query : M n KemSK mlSource Auxiliary _) := by
  unfold RegistrationNativeBeaconFrontend.record
  apply RegistrationNativeBeaconEnvView.bind_stable
  · exact RegistrationNativeBeaconEnvView.update_stable _ (fun _ => rfl)
  · intro result
    cases query <;> first
      | exact sample_stable _
      | apply RegistrationNativeBeaconEnvView.bind_stable
        · exact hash_stable _
        · intro digest; exact RegistrationNativeBeaconEnvView.pure_stable _

/-- Native abort executes its real terminal World phase effect. -/
theorem abort_stable (owner : Owner mlSource) :
    Stable (RegistrationNativeBeaconFrontend.abort owner : M n KemSK mlSource Auxiliary Unit) := by
  unfold RegistrationNativeBeaconFrontend.abort
  apply RegistrationNativeBeaconEnvView.bind_stable
  · exact effect_stable _
  · intro result; exact RegistrationNativeBeaconEnvView.pure_stable _

end BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.effect_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.effect_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.kem_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.kem_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.sample_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.sample_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.hash_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.hash_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.phase_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.phase_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.log_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.log_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.authentication_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.authentication_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.primitive_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.primitive_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.agreement_core_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.agreement_core_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.agreement_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.agreement_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.record_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.record_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.abort_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks.abort_stable
