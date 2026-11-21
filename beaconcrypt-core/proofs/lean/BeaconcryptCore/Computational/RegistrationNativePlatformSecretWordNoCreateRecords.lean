-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal
/-! Actual create, stateful Init publication and terminal-gated ordinary routes make no deferred Word material request. The three unused material branches of the separate ordinary dictionary are pure defaults; the complete dispatcher selects its proved material controllers instead. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateRecords
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformSecretWordOrdinary
open RegistrationNativeSecretWordTargetPoolFrame (IsCreate)
open RegistrationNativePlatformSecretWordNoCreateLocal (platform_zero)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem gate_free (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : A → Nat) (output : Option A) (before : Platform) :
    ((RegistrationNativePlatformOrdinaryGate.gate (fun amount => platform (n := n) (KemSK := KemSK) (reserve amount)) size output).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  cases output with
  | none => trivial
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run]
    apply isQueryBoundP_bind (n := 0) (m := 0) (platform_zero _ before)
    rintro ⟨result, after⟩ _
    cases result <;> trivial

theorem record_free (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform) :
    ((record (n := n) (KemSK := KemSK) reserve query).run before).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  rcases query with (send | raw) | ⟨owner, send | raw⟩
  · simp only [record, StateT.run]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨by simp [IsCreate], ?_⟩
    intro output
    simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, IsCreate, ite_false] using gate_free reserve _ output before.2
  · simp [record, StateT.run, isQueryBoundP_map_iff, IsCreate, isQueryBoundP_query_iff]
  · simp only [record, StateT.run]
    split
    · trivial
    · rw [isQueryBoundP_query_bind_iff]
      refine ⟨by simp [IsCreate], ?_⟩
      intro output
      simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, IsCreate, ite_false] using gate_free reserve _ output before.2
  · simp only [record, StateT.run]
    split
    · trivial
    · simp [isQueryBoundP_map_iff, IsCreate, isQueryBoundP_query_iff]


end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateRecords

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateRecords.record_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateRecords.record_free
