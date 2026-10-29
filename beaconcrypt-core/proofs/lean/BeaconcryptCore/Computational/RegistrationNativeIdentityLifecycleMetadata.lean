-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch
import BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch

/-! Actual bundle and finish lifecycles retain every generated identity credential and fixed public prekey/PQ field. The proof follows the native controller and current-owner updates on all branches; private key-table persistence is a separate source invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleMetadata
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeIdentityMetadata
open RegistrationNativeIdentityFrontend (Owner)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem abort_value (owner : Owner source) {Value : Type} (value : Value) :
    Preserves (RegistrationNativeIdentityFrontend.abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner *> pure value) := by
  simpa only [seqRight_eq_bind] using bind_preserves _ _ (abort_preserves owner) (fun _ => pure_preserves value)

private theorem bundle_next (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Preserves (RegistrationNativeIdentityBundleSource.next (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact pure_preserves _
  | ok result => cases result with
    | Err error => exact pure_preserves _
    | Ok published => exact bind_preserves _ _ (phase_preserves index _) (fun _ =>
        bind_preserves _ _ (lift_preserves _) (fun _ => pure_preserves _))

private theorem bundled (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Preserves (RegistrationNativeIdentityBundleSource.bundled (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime) :=
  bind_preserves _ _ (simulate_preserves _ (outgoing_preserves setup index owner) _)
    (bundle_next index owner oneTime)

private theorem bundle_start (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) :
    Preserves (RegistrationNativeIdentityBundleDispatch.start (n := n) (Auxiliary := Auxiliary) setup wire index owner) := by
  cases phase : owner.phase with
  | fresh =>
      simp only [RegistrationNativeIdentityBundleDispatch.start, phase]
      exact bind_preserves _ _ (sample_preserves _) (bundled setup wire index owner)
  | freshWithCoins scalar =>
      simpa only [RegistrationNativeIdentityBundleDispatch.start, phase, pure_bind] using bundled setup wire index owner scalar
  | initSent pending scalar | established completed | aborted aborted =>
      simpa only [RegistrationNativeIdentityBundleDispatch.start, phase] using
        (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (.ok none : RustM (Option Pqxdh.Bytes)))

/-- Complete actual bundle execution leaves all generated credentials and fixed public fields at their original owner indices. -/
theorem bundle_preserves (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat) :
    Preserves (RegistrationNativeIdentityFrontend.bundle (n := n) (Auxiliary := Auxiliary) setup source wire index) := by
  intro current env result supported
  cases found : current[index]? with
  | none =>
      simp only [RegistrationNativeIdentityFrontend.bundle, StateT.run_bind, StateT.run_get,
        pure_bind, found, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some owner =>
      rw [RegistrationNativeIdentityBundleDispatch.new_run setup wire index owner current found env] at supported
      exact bundle_start setup wire index owner current env result supported

private theorem finish_record (index : Nat) (owner : Owner source) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Preserves (RegistrationNativeIdentityFinishRecord.after (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner reply) := by
  cases reply with
  | fail error | div => exact abort_value owner _
  | ok result => cases result with
    | Err error => exact abort_value owner _
    | Ok established =>
        apply bind_preserves _ _ (lift_preserves _)
        intro installed
        cases installed with
        | false => exact abort_value owner _
        | true => exact bind_preserves _ _ (phase_preserves index _) (fun _ => pure_preserves _)

private theorem finish_agreement (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (reply : RustM agreement.AgreementEffect) :
    Preserves (RegistrationNativeIdentityFinishSteps.afterAgreement (n := n) (Auxiliary := Auxiliary) setup wire index owner reply) := by
  cases reply with
  | fail error | div => exact abort_value owner _
  | ok effect => cases effect with
    | Rejected previous | ConvertPublic pending | ConvertSecret pending | GenerateEphemeral pending | Encapsulate pending
      | Decapsulate pending | Dh pending | RootKdf pending | ServerComplete completed => exact abort_value owner _
    | BeaconComplete completed =>
        exact bind_preserves _ _ (simulate_preserves _ (record_preserves setup wire) _) (finish_record index owner)

private theorem finish_authentication (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Preserves (RegistrationNativeIdentityFinishSteps.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact abort_value owner _
  | ok result => cases result with
    | Err previous => exact abort_value owner _
    | Ok accepted =>
        exact bind_preserves _ _ (simulate_preserves _ (agreement_preserves setup owner oneTime) _)
          (finish_agreement setup wire index owner)

private theorem finish_begin (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) :
    Preserves (RegistrationNativeIdentityFinishSteps.begin (n := n) (Auxiliary := Auxiliary) setup wire index owner pending oneTime packet) := by
  cases moved : pending.aborted_state with
  | fail error | div =>
      simpa only [RegistrationNativeIdentityFinishSteps.begin, moved] using
        (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) _)
  | ok aborted =>
      simp only [RegistrationNativeIdentityFinishSteps.begin, moved]
      exact bind_preserves _ _ (phase_preserves index _) (fun _ =>
        bind_preserves _ _ (simulate_preserves _ (authentication_preserves setup) _) (finish_authentication setup wire index owner oneTime))

private theorem finish_start (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (packet : Option registration.ResponsePacket) :
    Preserves (RegistrationNativeIdentityFinishDispatch.start (n := n) (Auxiliary := Auxiliary) setup wire index owner packet) := by
  cases phase : owner.phase with
  | initSent pending oneTime =>
      simpa only [RegistrationNativeIdentityFinishDispatch.start, phase] using finish_begin setup wire index owner pending oneTime packet
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simpa only [RegistrationNativeIdentityFinishDispatch.start, phase] using
        (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (.ok none : RustM (Option Pqxdh.Bytes)))

/-- Actual finish retains immutable public credentials and fields through abort, verifier failure, optional agreement/opening failure and successful kernel installation. -/
theorem finish_preserves (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) :
    Preserves (RegistrationNativeIdentityFrontend.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  intro current env result supported
  cases found : current[index]? with
  | none =>
      simp only [RegistrationNativeIdentityFrontend.finish, StateT.run_bind, StateT.run_get,
        pure_bind, found, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some owner =>
      rw [RegistrationNativeIdentityFinishDispatch.new_run setup wire index owner current found env packet] at supported
      exact finish_start setup wire index owner packet current env result supported

end BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleMetadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleMetadata.bundle_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleMetadata.bundle_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleMetadata.finish_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleMetadata.finish_preserves
