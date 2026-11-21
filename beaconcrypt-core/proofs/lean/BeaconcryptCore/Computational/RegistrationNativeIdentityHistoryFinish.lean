-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks

/-! The complete native response path preserves the ordinary indexed signing history through terminal abort, optional verification and agreement failures, sequence-one opening and actual consumed-kernel installation. The proof follows each concrete source continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryFinish
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityFrontend (Owner)
open RegistrationNativeIdentityHistoryInvariant
open RegistrationNativeIdentitySourceSimulation (NewState runNew)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem aborting (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index handle : Nat) (owner : Owner source) (value : Value) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index handle
      (RegistrationNativeIdentityFrontend.abort owner *> pure value) := by
  simp only [seqRight_eq_bind, RegistrationNativeIdentityFrontend.abort, bind_assoc, pure_bind]
  exact bind_preserves setup checks representation created index handle _ _
    (RegistrationNativeIdentityHistoryOutgoing.effect_preserves setup checks representation created index handle _)
    (fun _ => pure_preserves setup checks representation created index handle value)

private theorem after_record (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativeIdentityFinishRecord.after index owner reply) := by
  cases reply with
  | fail error | div => exact aborting setup checks representation created index owner.identity.handle owner _
  | ok result => cases result with
    | Err error => exact aborting setup checks representation created index owner.identity.handle owner _
    | Ok established =>
        apply bind_preserves setup checks representation created index owner.identity.handle _ _
          (RegistrationNativeIdentityHistoryOutgoing.effect_preserves setup checks representation created index owner.identity.handle _)
        intro installed
        cases installed with
        | false => exact aborting setup checks representation created index owner.identity.handle owner _
        | true =>
            exact bind_preserves setup checks representation created index owner.identity.handle _ _
              (phase_preserves setup checks representation created index owner.identity.handle index _)
              (fun _ => pure_preserves setup checks representation created index owner.identity.handle _)

private theorem after_agreement (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (reply : RustM agreement.AgreementEffect) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativeIdentityFinishSteps.afterAgreement setup wire index owner reply) := by
  cases reply with
  | fail error | div => exact aborting setup checks representation created index owner.identity.handle owner _
  | ok effect => cases effect with
    | Rejected previous | ConvertPublic pending | ConvertSecret pending | GenerateEphemeral pending | Encapsulate pending
      | Decapsulate pending | Dh pending | RootKdf pending | ServerComplete completed =>
        exact aborting setup checks representation created index owner.identity.handle owner _
    | BeaconComplete completed =>
        exact bind_preserves setup checks representation created index owner.identity.handle _ _
          (RegistrationNativeIdentityHistoryOutgoing.program_preserves setup checks representation created index owner.identity.handle _
            (RegistrationNativeIdentityHistoryCallbacks.record_preserves setup checks representation created index owner.identity.handle wire) _)
          (after_record setup checks representation created index owner)

private theorem after_authentication (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativeIdentityFinishSteps.afterAuthentication setup wire index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact aborting setup checks representation created index owner.identity.handle owner _
  | ok result => cases result with
    | Err previous => exact aborting setup checks representation created index owner.identity.handle owner _
    | Ok accepted =>
        exact bind_preserves setup checks representation created index owner.identity.handle _ _
          (RegistrationNativeIdentityHistoryOutgoing.program_preserves setup checks representation created index owner.identity.handle _
            (RegistrationNativeIdentityHistoryCallbacks.agreement_preserves setup checks representation created index owner oneTime) _)
          (after_agreement setup checks representation created wire index owner)

private theorem begin_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativeIdentityFinishSteps.begin setup wire index owner pending oneTime packet) := by
  cases moved : pending.aborted_state with
  | fail error | div =>
      simpa only [RegistrationNativeIdentityFinishSteps.begin, moved] using
        (pure_preserves (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created index owner.identity.handle _)
  | ok aborted =>
      simp only [RegistrationNativeIdentityFinishSteps.begin, moved]
      exact bind_preserves setup checks representation created index owner.identity.handle _ _
        (phase_preserves setup checks representation created index owner.identity.handle index _)
        (fun _ => bind_preserves setup checks representation created index owner.identity.handle _ _
          (RegistrationNativeIdentityHistoryOutgoing.program_preserves setup checks representation created index owner.identity.handle _
            (RegistrationNativeIdentityHistoryCallbacks.authentication_preserves setup checks representation created index owner.identity.handle) _)
          (after_authentication setup checks representation created wire index owner oneTime))

private theorem start_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (packet : Option registration.ResponsePacket) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativeIdentityFinishDispatch.start setup wire index owner packet) := by
  cases phase : owner.phase with
  | initSent pending oneTime =>
      simpa only [RegistrationNativeIdentityFinishDispatch.start, phase] using
        begin_preserves setup checks representation created wire index owner pending oneTime packet
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simpa only [RegistrationNativeIdentityFinishDispatch.start, phase] using
        (pure_preserves (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created index owner.identity.handle
          (.ok none : RustM (Option Pqxdh.Bytes)))

/-- Actual incoming finish retains all generated ownership receipts and exact ordinary joint signing history on every result. -/
theorem finish_holds (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket)
    (before : NewState n KemSK Auxiliary source) (result : RustM (Option Pqxdh.Bytes) × NewState n KemSK Auxiliary source)
    (prior : Holds setup.joint before.2.identities before.1.1)
    (supported : result ∈ support (runNew setup checks representation created
      (RegistrationNativeIdentityFrontend.finish setup source wire index packet) before)) :
    Holds setup.joint result.2.2.identities result.2.1.1 := by
  cases found : before.1.1[index]? with
  | none =>
      simp only [runNew, RegistrationNativeIdentityFrontend.finish, StateT.run_bind, StateT.run_get,
        pure_bind, found, StateT.run_pure, simulateQ_pure, map_pure, mem_support_pure_iff] at supported
      cases supported
      exact prior
  | some owner =>
      have same : runNew setup checks representation created (RegistrationNativeIdentityFrontend.finish setup source wire index packet) before =
          runNew setup checks representation created (RegistrationNativeIdentityFinishDispatch.start setup wire index owner packet) before := by
        unfold runNew
        rw [RegistrationNativeIdentityFinishDispatch.new_run setup wire index owner before.1.1 found before.1.2 packet]
      rw [same] at supported
      apply (start_preserves setup checks representation created wire index owner packet before result ⟨prior, ?_⟩ supported).1
      simp only [At, RegistrationNativeIdentityHistorySync.handles, List.getElem?_map, found, Option.map_some]

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryFinish.finish_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryFinish.finish_holds
