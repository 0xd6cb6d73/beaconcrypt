-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot
/-! The candidate-independent root proxy makes at most one protected-key request and at most one suffix request at each actual material demand. World coins and both retained material caches add neither class of query. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps
open RegistrationNativePlatformRecordPartnerExposureRoot (Spec RootSpec coins material known demand handler)
open RegistrationNativePlatformRecordPartnerExposureSlots (State reserve)
open RegistrationNativeSecretWordServiceCaps (Kind)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
variable {n : Nat} {A : Type}

def Counted (kind : Kind) : (Spec n).Domain →Prop
  | .inl query=>RegistrationNativeSecretWordServiceCaps.Counted kind query
  | .inr _=>False
instance (kind : Kind) : DecidablePred (Counted (n := n) kind) := fun query=>by
  cases query <;> dsimp only [Counted] <;> infer_instance

def IsDemand : (RootSpec n).Domain →Prop
  | .inl _=>False
  | .inr _=>True
instance : DecidablePred (IsDemand (n := n)) := fun query=>by
  cases query <;> dsimp only [IsDemand] <;> infer_instance

private theorem coins_free (kind : Kind) (work : ProbComp A) :
    (simulateQ (coins (n := n)) work).IsQueryBoundP (Counted kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _=>False) _ _ 0 (isQueryBoundP_false work 0)
  intro query
  simp only [coins,QueryImpl.apply_compose,PqxdhRecordLiftInterface.coinLift,simulateQ_spec_query,
    RegistrationNativePlatformRecordPartnerExposureRoot.world,isQueryBoundP_query_iff,Counted]
  decide

/-- Hidden material44 cache hits and misses use only the existing World coin surface. -/
theorem material_free (kind : Kind) (slot : PqxdhRecordLiftInterface.Slot n) (before : State n) :
    ((material slot).run before).IsQueryBoundP (Counted kind) 0 := by
  simp only [material,StateT.run]
  split
  · trivial
  · rw [isQueryBoundP_map_iff]
    exact coins_free kind _

/-- Ordinary protected108 cache hits and misses use only the existing World coin surface. -/
theorem known_free (kind : Kind) (bytes : Pqxdh.Bytes) (before : State n) :
    ((known bytes).run before).IsQueryBoundP (Counted kind) 0 := by
  simp only [known,StateT.run]
  split
  · trivial
  · rw [isQueryBoundP_map_iff]
    exact coins_free kind _

/-- Every demand has one protected-key or suffix request at most, retaining refusal, allocation and both cache states. -/
theorem demand_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (message : Message)
    (before : State n) (kind : Kind) :
    ((demand source input inside message).run before).IsQueryBoundP (Counted kind) 1 := by
  simp only [demand,StateT.run]
  split
  · trivial
  · rename_i key realized
    split
    · apply isQueryBoundP_bind (n := 1) (m := 0)
      · cases kind <;> simp [Counted,RegistrationNativeSecretWordServiceCaps.Counted,
          RegistrationNativeSecretWordRecoveryCompiler.IsKey,RegistrationNativeSecretWordRecoveryCompiler.IsSuffix,
          RegistrationNativeSecretWord.IsKey,isQueryBoundP_query_iff]
      · intro _reply _possible
        split
        · split
          · trivial
          · rw [isQueryBoundP_map_iff]
            exact material_free kind _ _
        · rw [isQueryBoundP_map_iff]
          exact known_free kind _ _
    · split
      · cases kind <;> simp [Counted,RegistrationNativeSecretWordServiceCaps.Counted,
          RegistrationNativeSecretWordRecoveryCompiler.IsKey,RegistrationNativeSecretWordRecoveryCompiler.IsSuffix,
          isQueryBoundP_map_iff,isQueryBoundP_query_iff]
      · trivial

/-- Preparation notifications consume neither billed oracle class; actual demands consume at most one. -/
theorem handler_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool)
    (query : (RootSpec n).Domain) (before : State n) (kind : Kind) :
    ((handler source input inside query).run before).IsQueryBoundP (Counted kind) (if IsDemand (n := n) query then 1 else 0) := by
  cases query with
  | inl message=>trivial
  | inr message=>exact demand_bound source input inside message before kind

/-- The literal root callback demand cap transfers to both recovery bills without charging preparations. -/
theorem program_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool)
    (work : OracleComp (RootSpec n) A) (cap : Nat) (bounded : work.IsQueryBoundP (IsDemand (n := n)) cap)
    (before : State n) (kind : Kind) :
    ((simulateQ (handler source input inside) work).run before).IsQueryBoundP (Counted kind) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using handler_bound source input inside query current kind
  · intro query free current
    simpa only [ite_eq_right free] using handler_bound source input inside query current kind
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps.material_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps.material_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps.known_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps.known_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps.demand_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps.demand_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps.handler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps.program_bound
