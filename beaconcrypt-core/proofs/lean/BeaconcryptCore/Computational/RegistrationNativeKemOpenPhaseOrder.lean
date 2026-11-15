-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseReceipts
import BeaconcryptCore.Computational.RegistrationNativeKemOptionalCut

/-! A candidate phase is assigned at most once and then survives every native operation. The stopped prefix is inactive by actual query syntax. These structural laws retain failed callbacks and complete private source state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemSwitchSource (Phase)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def Extends (before after : Phase) : Prop := before = none ∨ after = before

/-- An established private phase remains the same through any number of actual later source operations. -/
theorem extends_trans {first middle last : Phase} (left : Extends first middle) (right : Extends middle last) :
    Extends first last := by
  rcases left with inactive | same
  · exact Or.inl inactive
  · rw [same] at right
    exact right

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- A whole actual optional native source execution cannot replace an already established candidate, including when it aborts. -/
theorem work_extends (work : OracleComp (Spec n mlSource KemSK) Value) (before after : State n mlSource KemSK)
    (value : Option Value) (supported : (value, after) ∈ support (((simulateQ provider work).run).run before)) :
    Extends before.2 after.2 := by
  rcases before with ⟨first, none | label⟩
  · exact Or.inl rfl
  · rw [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchSource.post_program,
      support_map] at supported
    obtain ⟨result, _reached, returned⟩ := supported
    cases returned
    exact Or.inr rfl

/-- The complete original raw client retains the same established phase, without restricting its adaptive callbacks. -/
theorem raw_work_extends (parsed : Nat) (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before after : State n mlSource KemSK) (value : Option Value)
    (supported : (value, after) ∈ support
      (((simulateQ (RegistrationNativeKemOpenRawCounter.native setup checks wire route representation created credential
        selected pairs publicKey real parsed) work).run).run before)) : Extends before.2 after.2 := by
  apply work_extends setup checks wire route representation created credential selected pairs publicKey real _ before after value
  simpa only [RegistrationNativeKemOpenRawCounter.native, QueryImpl.simulateQ_compose] using supported

/-- The original full secrecy ledger retains every established candidate through all its hidden draws and actual callbacks. -/
theorem run_extends (parsed : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (work : OracleComp RegistrationNativeInterface.FullSpec Value) (ledger : RegistrationNativeLedger.State)
    (before after : State n mlSource KemSK) (value : Option (Value × RegistrationNativeLedger.State))
    (supported : (value, after) ∈ support
      (((RegistrationNativeKemOpenReceipts.run setup checks wire route representation created credential selected pairs publicKey real parsed
        bounds work ledger).run).run before)) : Extends before.2 after.2 :=
  raw_work_extends setup checks wire route representation created credential selected pairs publicKey real parsed _ before after value supported

private theorem scan_bound (work : OracleComp (Spec n mlSource KemSK) Value) :
    (RegistrationNativeKemGame.expose work 0).IsQueryBoundP
      (RegistrationNativeKemRouting.IsExposed (ambient := RegistrationNativeKemFrontendInterface.Ambient n mlSource)
        (KemSK := KemSK)) 0 := by
  change IsQueryBoundP (RegistrationNativeKemCut.scan
    (fun query => ((Spec n mlSource KemSK).query query : OracleComp (Spec n mlSource KemSK) _)) work 0) _ 0
  induction work using OracleComp.inductionOn with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind query next ih =>
      rcases query with query | (query | key)
      · rw [RegistrationNativeKemCut.scan_other]
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp only [RegistrationNativeKemRouting.IsExposed, not_false_eq_true]), fun reply => by simpa using ih reply⟩
      · rw [RegistrationNativeKemCut.scan_pool]
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp only [RegistrationNativeKemRouting.IsExposed, not_false_eq_true]), fun reply => by simpa using ih reply⟩
      · exact isQueryBoundP_pure _ _ _

/-- The actual stopped getter-zero prefix keeps its input phase because it executes no exposed getter. -/
theorem scan_phase (work : OracleComp (Spec n mlSource KemSK) Value)
    (before after : State n mlSource KemSK) (cut : RegistrationNativeKemCut.Cut
      (RegistrationNativeKemParsedRouting.Ambient n mlSource) KemSK Value)
    (supported : (some cut, after) ∈ support
      (((RegistrationNativeKemCut.scan provider work 0).run).run before)) : after.2 = before.2 := by
  apply RegistrationNativeKemOpenPhase.ordinary_program setup checks wire route representation created credential
    selected pairs publicKey real (RegistrationNativeKemGame.expose work 0) (scan_bound work) before after cut
  simpa only [RegistrationNativeKemGame.expose, RegistrationNativeKemCutStop.scan_simulate] using supported

end BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder.extends_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder.extends_trans
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder.work_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder.work_extends
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder.raw_work_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder.raw_work_extends
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder.run_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder.run_extends
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder.scan_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder.scan_phase
