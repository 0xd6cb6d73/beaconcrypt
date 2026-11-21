-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallLedgerRestricted

/-! The literal original full secrecy ledger composes the raw native installation receipts. Secret test coins and fresh payloads remain above their actual sends; their complete ledger entry is retained while installation ordinals and physical hidden storage remain unchanged. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallLedger
open RegistrationNativeInstallOrdinals (messages handles Counts Hidden)
open RegistrationNativeInstallStep (RoleStep)
variable {n : Nat} {NativeState Reader Response : Type}

private theorem ledger_trace (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State)
    (result : RegistrationNativeInterface.FullSpec.Range query × RegistrationNativeLedger.State)
    (supported : result ∈ support ((RegistrationNativeLedger.handler crypto codec serverKeyId bounds query).run before)) :
    result.2.transcript = before.transcript ++ [⟨query, result.1⟩] := by
  cases query with
  | inl query =>
      rw [RegistrationNativeLedger.query_forward, support_map] at supported
      obtain ⟨reply, _reached, rfl⟩ := supported
      rfl
  | inr query =>
      rw [RegistrationNativeLedger.query_secrecy, support_map] at supported
      obtain ⟨reply, _reached, rfl⟩ := supported
      rfl

/-- Exact callback receipts extend the full original chronology and hidden-slot invariant. -/
theorem advance
    (events : NativeState → List RegistrationNativeG2Trace.Event)
    (slots : NativeState → PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n))
    (valid : NativeState → Prop) (selected : RegistrationNativeRelatedFamily.Message → Prop)
    (before after : RegistrationNativeLedger.State × NativeState) (entry : RegistrationNativeInterface.Entry)
    (prior : Holds events slots valid selected before) (stored : Storage slots valid before.2 after.2)
    (recorded : after.1.transcript = before.1.transcript ++ [entry])
    (steps : ∀ role, RoleStep role (events before.2) (events after.2) entry (slots after.2) selected) :
    Holds events slots valid selected after := by
  refine ⟨stored.1, ?_, ?_⟩
  · intro role
    rw [recorded]
    exact RegistrationNativeInstallStep.counts role _ _ _ _ _ _ (prior.2.1 role) (steps role)
  · rw [recorded]
    exact RegistrationNativeInstallStep.hidden _ _ _ _ _ _ _ prior.2.1 prior.2.2 stored.2 steps

variable (native : QueryImpl RegistrationNativeInterface.Spec (StateT NativeState ProbComp))
    (events : NativeState → List RegistrationNativeG2Trace.Event)
    (slots : NativeState → PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n))
    (valid : NativeState → Prop) (selected : RegistrationNativeRelatedFamily.Message → Prop)
    (storage : ∀ query before result, valid before → result ∈ support ((native query).run before) →
      Storage slots valid before result.2)
    (rawStep : ∀ query before result, valid before → result ∈ support ((native query).run before) →
      ∀ role, RoleStep role (events before) (events result.2) ⟨.inl query, result.1⟩ (slots result.2) selected)

include storage rawStep

/-- Every complete original ledger callback preserves the native successful-installation and hidden-slot invariant. -/
theorem full_step (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State × NativeState)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × NativeState))
    (prior : Holds events slots valid selected before)
    (supported : result ∈ support ((RegistrationNativeLedger.interpreted native crypto codec serverKeyId bounds query).run before)) :
    Holds events slots valid selected result.2 := by
  cases query with
  | inl query =>
      rw [RegistrationNativeLedger.interpreted, QueryImpl.flattenStateT_mapStateTBase_apply_run] at supported
      simp only [RegistrationNativeLedger.query_forward, simulateQ_map, simulateQ_spec_query,
        StateT.run_map, Functor.map_map, support_map] at supported
      obtain ⟨inner, called, rfl⟩ := supported
      exact advance events slots valid selected before _ ⟨.inl query, inner.1⟩ prior
        (storage query before.2 inner prior.1 called) rfl (rawStep query before.2 inner prior.1 called)
  | inr query =>
      rw [RegistrationNativeLedger.interpreted, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
      obtain ⟨inner, called, rfl⟩ := supported
      have kept := restricted native events slots valid selected storage rawStep _
        (RegistrationNativeLedger.secrecy_frame crypto codec serverKeyId bounds query before.1) before.2 inner prior.1 called
      have original : inner.1 ∈ support ((RegistrationNativeLedger.handler crypto codec serverKeyId bounds (.inr query)).run before.1) := by
        apply OracleComp.support_simulateQ_run'_subset native _ before.2
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst called
      apply advance events slots valid selected before _ ⟨.inr query, inner.1.1⟩ prior kept.1
        (ledger_trace crypto codec serverKeyId bounds (.inr query) before.1 inner.1 original)
      intro role
      apply RegistrationNativeInstallStep.of_quiet role _ _ _ _ _ (kept.2 role)
      cases role <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeInstallLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallLedger.advance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallLedger.advance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallLedger.full_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallLedger.full_step
