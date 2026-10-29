-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementMetadata
import BeaconcryptCore.Computational.RegistrationServerRecordExecutor
import BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor

/-!
The native agreement and initial-record controllers execute sequentially in one complete primitive state. The record stage receives the actual returned agreement capability and populated binding, and installs no fresh zero-counter kernel. Every agreement result is retained; a record result is present exactly when the relevant actual completion invokes that record controller. Optional primitive failures and source failures retain the state they reached.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationInitialRecord

open RegistrationAgreementShared

abbrev ServerResult := RustM agreement.AgreementEffect × Option (RustM RegistrationServerRecordExecutor.Result)
abbrev BeaconResult := RustM agreement.AgreementEffect × Option (RustM RegistrationBeaconRecordExecutor.Result)

noncomputable def server {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) (writer : RawCtxMixedShared.Writer)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (authenticated : registration.AuthenticatedInit) (application : Slice Std.U8) :
    StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp ServerResult := do
  let agreed ← simulateQ (implementation source primitive)
    (RegistrationAgreementExecutor.server control status authenticated)
  match agreed with
  | .ok (.ServerComplete capability) => do
      let completed ← RegistrationServerRecordExecutor.execute source writer control current availability capability application
      pure (agreed, some completed)
  | _ => pure (agreed, none)

noncomputable def beacon {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) (writer : RawCtxMixedShared.Writer)
    (authenticated : registration.AuthenticatedResponse) :
    StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp BeaconResult := do
  let agreed ← simulateQ (implementation source primitive) (RegistrationAgreementExecutor.beacon authenticated)
  match agreed with
  | .ok (.BeaconComplete capability) => do
      let completed ← RegistrationBeaconRecordExecutor.execute source writer capability
      pure (agreed, some completed)
  | _ => pure (agreed, none)

theorem server_cut {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) (writer : RawCtxMixedShared.Writer)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (authenticated : registration.AuthenticatedInit) (application : Slice Std.U8)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (agreed : RustM agreement.AgreementEffect)
    (completed : registration.ServerResponseHash)
    (supported : ((agreed, some (.ok (.Ok completed))), after) ∈ support
      ((server source primitive writer control status current availability authenticated application).run before)) :
    ∃ capability middle, agreed = .ok (.ServerComplete capability) ∧
      (.ok (.ServerComplete capability), middle) ∈ support
        ((simulateQ (implementation source primitive)
          (RegistrationAgreementExecutor.server control status authenticated)).run before) ∧
      (.ok (.Ok completed), after) ∈ support
        ((RegistrationServerRecordExecutor.execute source writer control current availability capability application).run middle) := by
  simp only [server, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, middle⟩, first, continued⟩ := supported
  cases reply with
  | fail error => simp at continued
  | div => simp at continued
  | ok phase =>
      cases phase
      all_goals try { simp at continued; done }
      case ServerComplete capability =>
        simp only [StateT.run_bind, mem_support_bind_iff] at continued
        obtain ⟨⟨result, reached⟩, ran, returned⟩ := continued
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at returned
        obtain ⟨⟨agreedSame, resultSame⟩, stateSame⟩ := returned
        subst agreed
        subst result
        subst reached
        exact ⟨capability, middle, rfl, first, ran⟩

theorem beacon_cut {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) (writer : RawCtxMixedShared.Writer)
    (authenticated : registration.AuthenticatedResponse)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (agreed : RustM agreement.AgreementEffect)
    (completed : registration.CompletedBeacon)
    (supported : ((agreed, some (.ok (.Ok completed))), after) ∈ support
      ((beacon source primitive writer authenticated).run before)) :
    ∃ capability middle, agreed = .ok (.BeaconComplete capability) ∧
      (.ok (.BeaconComplete capability), middle) ∈ support
        ((simulateQ (implementation source primitive)
          (RegistrationAgreementExecutor.beacon authenticated)).run before) ∧
      (.ok (.Ok completed), after) ∈ support
        ((RegistrationBeaconRecordExecutor.execute source writer capability).run middle) := by
  simp only [beacon, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, middle⟩, first, continued⟩ := supported
  cases reply with
  | fail error => simp at continued
  | div => simp at continued
  | ok phase =>
      cases phase
      all_goals try { simp at continued; done }
      case BeaconComplete capability =>
        simp only [StateT.run_bind, mem_support_bind_iff] at continued
        obtain ⟨⟨result, reached⟩, ran, returned⟩ := continued
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at returned
        obtain ⟨⟨agreedSame, resultSame⟩, stateSame⟩ := returned
        subst agreed
        subst result
        subst reached
        exact ⟨capability, middle, rfl, first, ran⟩

theorem server_consumed {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) (writer : RawCtxMixedShared.Writer)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (authenticated : registration.AuthenticatedInit) (application : Slice Std.U8)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (agreed : RustM agreement.AgreementEffect)
    (completed : registration.ServerResponseHash)
    (supported : ((agreed, some (.ok (.Ok completed))), after) ∈ support
      ((server source primitive writer control status current availability authenticated application).run before)) :
    completed.binding = authenticated.binding ∧
      ∃ selected : ratchet.concrete.SendSeal record_effects.SealFrameContext,
        completed.kernel = selected.advanced ∧ selected.sequence.val = 1 ∧
        selected.context.associated_data = authenticated.binding.associated_data := by
  obtain ⟨capability, middle, _agreed, first, recorded⟩ :=
    server_cut source primitive writer control status current availability authenticated application
      before after agreed completed supported
  have binding := RegistrationAgreementExecutor.interpreted_server_binding (implementation source primitive)
    before middle control status authenticated capability first
  obtain ⟨_pin, retained, selected, kernel, sequence, ad⟩ :=
    RegistrationServerRecordExecutor.execute_retains source writer control current availability capability application
      middle after completed recorded
  exact ⟨retained.trans binding, selected, kernel, sequence, by simpa only [binding] using ad⟩

theorem beacon_consumed {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) (writer : RawCtxMixedShared.Writer)
    (authenticated : registration.AuthenticatedResponse)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (agreed : RustM agreement.AgreementEffect)
    (completed : registration.CompletedBeacon)
    (supported : ((agreed, some (.ok (.Ok completed))), after) ∈ support
      ((beacon source primitive writer authenticated).run before)) :
    ∃ (capability : agreement.BeaconAgreement) (pending : registration.BeaconRecordAead) (plaintext : Slice Std.U8),
      agreed = .ok (.BeaconComplete capability) ∧ capability.binding = authenticated.pending.binding ∧
      completed.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
        authenticated.pending.binding capability.candidate.assigned_key_id ∧
      pending.agreement = capability ∧
      pending.pending.finish (.Some plaintext) = .ok (completed.kernel,
        .Some (⟨plaintext, capability.candidate.server_binding.identity_key_id, 1#u64⟩ :
          record.OpenedRecord (Slice Std.U8))) ∧ completed.application = plaintext.drop 8#usize := by
  obtain ⟨capability, middle, agreedSame, first, recorded⟩ :=
    beacon_cut source primitive writer authenticated before after agreed completed supported
  have binding := RegistrationAgreementExecutor.interpreted_beacon_binding (implementation source primitive)
    before middle authenticated capability first
  obtain ⟨retained, pending, plaintext, agreementSame, kernel, application⟩ :=
    RegistrationBeaconRecordExecutor.execute_consumed source writer capability middle after completed recorded
  exact ⟨capability, pending, plaintext, agreedSame, binding, by simpa only [binding] using retained,
    agreementSame, kernel, application⟩

end BeaconcryptCore.Computational.RegistrationInitialRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationInitialRecord.server_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitialRecord.server_cut
/-- info: 'BeaconcryptCore.Computational.RegistrationInitialRecord.beacon_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitialRecord.beacon_cut
/-- info: 'BeaconcryptCore.Computational.RegistrationInitialRecord.server_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitialRecord.server_consumed
/-- info: 'BeaconcryptCore.Computational.RegistrationInitialRecord.beacon_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitialRecord.beacon_consumed
