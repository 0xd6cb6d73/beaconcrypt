-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMain

/-! Ordinary native work, local control updates and alias reporting introduce no indexed Ed identity. Their structural bills compose under the actual public Main state transformer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore
open RegistrationNativeIdentityMain (State M)
open PqxdhDynamicIdentityPool (IsCreate)
open PqxdhJointPhase1Reports (SourceClass ProtocolSpec)
variable {n : Nat} {KemSK Value Other : Type} {source : RegistrationNativeMldsa.Source}

abbrev Creates := SourceClass IsCreate

def Bound (work : M n KemSK source Value) (cap : Nat) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP Creates cap

theorem coins_zero (work : ProbComp Value) :
    (simulateQ RegistrationNativeIdentityMain.coins work).IsQueryBoundP Creates 0 := by
  apply OracleComp.IsQueryBoundP.simulateQ_of_step (OracleComp.isQueryBoundP_false work 0)
    (fun _ impossible => impossible.elim)
  intro query _
  simp [RegistrationNativeIdentityMain.coins, Creates, SourceClass, IsCreate, isQueryBoundP_query_iff]

theorem ordinary_zero (work : StateT (RegistrationNativeIdentityWorld.Context n KemSK) ProbComp Value) :
    Bound (RegistrationNativeIdentityMain.ordinary work : M n KemSK source Value) 0 := by
  intro before
  exact (isQueryBoundP_map_iff (p := Creates) _ _ 0).mpr (coins_zero _)

theorem pure_zero (value : Value) : Bound (pure value : M n KemSK source Value) 0 := by
  intro before
  simp only [StateT.run_pure]
  exact isQueryBoundP_pure Creates _ 0

theorem get_zero : Bound (get : M n KemSK source (State n KemSK source)) 0 := by
  intro before
  simp only [StateT.run_get]
  exact isQueryBoundP_pure Creates _ 0

theorem modify_zero (change : State n KemSK source → State n KemSK source) :
    Bound (modify change : M n KemSK source Unit) 0 := by
  intro before
  simp only [StateT.run_modify]
  exact isQueryBoundP_pure Creates _ 0

theorem bind_bound (work : M n KemSK source Value) (next : Value → M n KemSK source Other)
    (first later : Nat) (beforeBound : Bound work first) (afterBound : ∀ value, Bound (next value) later) :
    Bound (work >>= next) (first + later) := by
  intro before
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (beforeBound before) (fun result _ => afterBound result.1 result.2)

theorem emit_zero (reports : List PqxdhJointPhase1Reports.CandidateReport) :
    (RegistrationNativeIdentityMain.emit reports).IsQueryBoundP Creates 0 := by
  induction reports with
  | nil => exact isQueryBoundP_pure Creates _ 0
  | cons report rest ih =>
      simp only [RegistrationNativeIdentityMain.emit, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [Creates, SourceClass]), fun _ => ih⟩

theorem report_zero (packet : beaconcrypt_core.registration.InitPacket) :
    Bound (RegistrationNativeIdentityMain.report packet : M n KemSK source Unit) 0 := by
  unfold RegistrationNativeIdentityMain.report
  apply bind_bound _ _ 0 0 get_zero
  intro current before
  simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
  exact emit_zero _

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.coins_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.coins_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.ordinary_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.ordinary_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.pure_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.pure_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.get_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.get_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.modify_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.modify_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.bind_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.emit_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.emit_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.report_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore.report_zero
