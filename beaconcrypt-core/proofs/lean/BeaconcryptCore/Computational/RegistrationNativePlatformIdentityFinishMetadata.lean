-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun

/-! Corrected assigned-ID finish retains every opaque generated identity credential and fixed public prekey/PQ field through every native result. Copy-before-install and changed sender-ID metadata affect the World without changing owner credentials or source rows. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishMetadata
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeIdentityMetadata
open RegistrationNativeIdentityFrontend (Owner)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem abort_value (owner : Owner source) {Value : Type} (value : Value) :
    Preserves (RegistrationNativeIdentityFrontend.abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner *> pure value) := by
  simpa only [seqRight_eq_bind] using bind_preserves _ _ (abort_preserves owner) (fun _ => pure_preserves value)

private theorem finish_record (index : Nat) (owner : Owner source) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Preserves (RegistrationNativePlatformIdentityFinishRecord.after (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner reply) := by
  cases reply with
  | fail error | div => exact abort_value owner _
  | ok result => cases result with
    | Err error => exact abort_value owner _
    | Ok established =>
        change Preserves (RegistrationNativePlatformIdentityFinishRecord.install index owner established)
        rw [RegistrationNativePlatformIdentityFinishRecord.install_exact]
        apply bind_preserves _ _ (lift_preserves _)
        intro installed
        cases installed with
        | false => exact abort_value owner _
        | true => exact bind_preserves _ _ (phase_preserves index _) (fun _ => pure_preserves _)

private theorem finish_agreement (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (reply : RustM agreement.AgreementEffect) :
    Preserves (RegistrationNativePlatformIdentityFinishSteps.afterAgreement (n := n) (Auxiliary := Auxiliary) setup wire index owner reply) := by
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
    Preserves (RegistrationNativePlatformIdentityFinishSteps.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime reply) := by
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
    Preserves (RegistrationNativePlatformIdentityFinishSteps.begin (n := n) (Auxiliary := Auxiliary) setup wire index owner pending oneTime packet) := by
  cases moved : pending.aborted_state with
  | fail error | div =>
      simpa only [RegistrationNativePlatformIdentityFinishSteps.begin, moved] using
        (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) _)
  | ok aborted =>
      simp only [RegistrationNativePlatformIdentityFinishSteps.begin, moved]
      exact bind_preserves _ _ (phase_preserves index _) (fun _ =>
        bind_preserves _ _ (simulate_preserves _ (authentication_preserves setup) _) (finish_authentication setup wire index owner oneTime))

private theorem finish_start (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (packet : Option registration.ResponsePacket) :
    Preserves (RegistrationNativePlatformIdentityFinishRun.start (n := n) (Auxiliary := Auxiliary) setup wire index owner packet) := by
  cases phase : owner.phase with
  | initSent pending oneTime =>
      simpa only [RegistrationNativePlatformIdentityFinishRun.start, phase] using finish_begin setup wire index owner pending oneTime packet
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simpa only [RegistrationNativePlatformIdentityFinishRun.start, phase] using
        (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (.ok none : RustM (Option Pqxdh.Bytes)))

/-- Actual finish retains immutable public credentials and fields through abort, verifier failure, optional agreement/opening failure and successful kernel installation. -/
theorem finish_preserves (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) :
    Preserves (RegistrationNativePlatformIdentityFinishRun.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  intro current env result supported
  cases found : current[index]? with
  | none =>
      simp only [RegistrationNativePlatformIdentityFinishRun.finish, StateT.run_bind, StateT.run_get,
        pure_bind, found, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some owner =>
      simp only [RegistrationNativePlatformIdentityFinishRun.finish, StateT.run_bind, StateT.run_get,
        pure_bind, found] at supported
      exact finish_start setup wire index owner packet current env result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishMetadata
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishMetadata.finish_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishMetadata.finish_preserves
