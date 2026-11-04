-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolFrame
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateLocal
/-! The actual local, external-platform and source build embeddings cannot create an extra private KEM row. Their full current reply and platform state are retained while the original indexed birth predicate is transported syntactically. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal
open RegistrationNativeSecretWordInterface (LocalSpec liftLocal)
open RegistrationNativeSecretWordTargetPoolFrame (IsCreate)
variable {n : Nat} {KemSK Platform A : Type}
theorem local_bound (selected : Bool) (work : OracleComp (LocalSpec n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (KemSK := KemSK)) count) :
    (simulateQ (liftLocal selected) work).IsQueryBoundP (IsCreate (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  rcases query with message | paired | other | pool | key
  · simp [liftLocal, IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
  · simp [liftLocal, IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
  · simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem,
      IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
  · cases pool <;> simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem,
      IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
  · cases selected <;> simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem,
      IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]


/-- Every actual external platform draw is an ordinary environment coin, preserving private birth allowance zero. -/
theorem platform_zero (work : StateT Platform ProbComp A) (before : Platform) :
    ((RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false (work.run before) 0)
  intro coin
  simp [RegistrationNativeSecretWordFrontend.effect, IsCreate, isQueryBoundP_query_iff]

/-- Every query of the actual material/effect source build language excludes private KEM birth. -/
theorem build_free (work : OracleComp (RegistrationNativePlatformSecretWordBuild.Spec n) A) :
    (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ
      RegistrationNativePlatformSecretWordBuild.wordEmbedding (KemSK := KemSK)) work).IsQueryBoundP
        (IsCreate (KemSK := KemSK)) 0 := by
  rw [QueryImpl.simulateQ_compose]
  apply local_bound false _ 0
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false work 0)
  intro query
  rcases query with message | effect | coin
  all_goals simp [RegistrationNativePlatformSecretWordBuild.wordEmbedding, RegistrationNativeSecretWordInterface.demand,
    RegistrationNativeSecretWordInterface.effect, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal.local_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal.platform_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal.platform_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal.build_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal.build_free
