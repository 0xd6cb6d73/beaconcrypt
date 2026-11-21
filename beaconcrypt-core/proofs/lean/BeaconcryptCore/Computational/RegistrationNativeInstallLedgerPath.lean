-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallLedgerStep

/-! The installation ordinal and hidden-slot association holds at every cut of the same actual complete full-ledger path. Empty initialization discharges all chronology obligations; callback receipts are carried through the original adaptive secrecy controller. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallLedger
variable {n : Nat} {NativeState Reader Response Value : Type}
variable (native : QueryImpl RegistrationNativeInterface.Spec (StateT NativeState ProbComp))
    (events : NativeState → List RegistrationNativeG2Trace.Event)
    (slots : NativeState → PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n))
    (valid : NativeState → Prop) (selected : RegistrationNativeRelatedFamily.Message → Prop)
    (storage : ∀ query before result, valid before → result ∈ support ((native query).run before) →
      Storage slots valid before result.2)
    (rawStep : ∀ query before result, valid before → result ∈ support ((native query).run before) →
      ∀ role, RegistrationNativeInstallStep.RoleStep role (events before) (events result.2)
        ⟨.inl query, result.1⟩ (slots result.2) selected)

/-- Empty actual initialization has no phantom successful public handle or selected hidden-slot obligation. -/
theorem initial (before : NativeState) (prior : valid before) (empty : events before = []) :
    Holds events slots valid selected (RegistrationNativeLedger.empty, before) := by
  refine ⟨prior, ?_, ?_⟩
  · intro role
    simp only [RegistrationNativeInstallOrdinals.Counts, empty, RegistrationNativeLedger.empty,
      RegistrationNativeInstallOrdinals.messages, RegistrationNativeInstallOrdinals.handles, List.filterMap_nil]
    rfl
  · simp only [empty, RegistrationNativeLedger.empty]
    exact RegistrationNativeInstallHistory.hidden_empty (slots before) selected

include storage rawStep

/-- Every reached prefix preserves the same ledger-to-trace ordinals and actual hidden physical handles. -/
theorem path (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × NativeState} {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeLedger.interpreted native crypto codec serverKeyId bounds) before entries after)
    (prior : Holds events slots valid selected before) : Holds events slots valid selected after :=
  RegistrationNativeSecretWordTargetPath.preserves _ (Holds events slots valid selected)
    (fun query current result good reached => full_step native events slots valid selected storage rawStep
      crypto codec serverKeyId bounds query current result good reached) actual prior

/-- Every complete adaptive execution derives its installation invariant from actual empty chronology and local source receipts. -/
theorem run (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (work : OracleComp RegistrationNativeInterface.FullSpec Value) (before : NativeState)
    (result : Value × (RegistrationNativeLedger.State × NativeState))
    (prior : valid before) (empty : events before = [])
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeLedger.interpreted native crypto codec serverKeyId bounds) work).run
        (RegistrationNativeLedger.empty, before))) : Holds events slots valid selected result.2 := by
  obtain ⟨entries, actual⟩ := RegistrationNativeSecretWordTargetPath.program _ work
    (RegistrationNativeLedger.empty, before) result supported
  exact path native events slots valid selected storage rawStep crypto codec serverKeyId bounds actual
    (initial events slots valid selected before prior empty)

end BeaconcryptCore.Computational.RegistrationNativeInstallLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallLedger.initial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallLedger.initial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallLedger.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallLedger.path
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallLedger.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallLedger.run
