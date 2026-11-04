-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFinalKey
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateChosen
import BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentReplay
/-! The actual guarded source's genuine wins use the SAME selected generated public key and full history as its ordinary reserved-family game. Other seeds are sampled inside the chosen-key adversary. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFamilyWins
open PqxdhJointIdentity (Primitives IdentitySeed Forgery)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
open RegistrationNativeIdentityCensorPacketClient (Found)
open RegistrationNativeIdentityTemplatePolicy (Public)
open RegistrationNativeIdentityTemplateLateIdentity (Witness)
open RegistrationNativeIdentityTemplatePublicRegistry (keys empty)
open RegistrationNativeIdentityTemplateGuardedLateFamily (program run project independent)
variable {count : Nat}
abbrev Result (count : Nat) := (Fin count → IdentitySeed) ×
  ((Option Witness × Public) × (PqxdhDynamicIdentityRouting.PublicState × PqxdhJointIdentityFreshness.GlobalState count))

/-- The complete ordinary family history equals the genuine successful service audit of that SAME projected source run. -/
theorem history (joint : Primitives) (count selected : Nat) (code : OracleComp Spec (Option Found))
    (publicBefore : Public) (result : Result count)
    (reached : result∈support (run joint count selected code empty publicBefore)) (target : Fin count) :
    result.2.2.2.histories target=RegistrationNativeIdentityHistory.history target.val (project result).2.transcript := by
  simp only [run,mem_support_bind_iff,mem_support_pure_iff] at reached
  obtain ⟨seeds,_sampled,finished,called,rfl⟩ := reached
  have audit := RegistrationNativeIdentityIndependentReplay.routed_initialized joint seeds
    (independent joint selected code empty publicBefore) finished called
  rw [audit,RegistrationNativeIdentityHistory.replay_history]
  rfl

private theorem selected_key (joint : Primitives) (target : Fin count) (result : Result count)
    (seed : IdentitySeed) (row : (project result).2.seeds[target.val]?=some seed) :
    joint.publicKeys seed=PqxdhJointIdentityFamily.familyPublic joint result.1 target := by
  have within := (List.getElem?_eq_some_iff.mp row).1
  change target.val < ((List.ofFn result.1).take result.2.2.1.created).length at within
  simp only [List.length_take,List.length_ofFn] at within
  have created : target.val < result.2.2.1.created := lt_of_lt_of_le within (Nat.min_le_left _ _)
  have lookup := PqxdhDynamicIdentityRouting.sourceState_lookup result.1 result.2.2.1 target.val created target.isLt
  change (PqxdhDynamicIdentityRouting.sourceState result.1 result.2.2.1).seeds[target.val]?=some seed at row
  rw [lookup] at row
  exact congrArg joint.publicKeys (Option.some.inj row).symm

/-- Genuine actual source wins have one ordinary joint weak-EUF bill, with final key equality and family audit alignment discharged from the same run. -/
theorem source_bound (joint : Primitives) (target : Fin (count+1)) (code : OracleComp Spec (Option Found))
    (allowed : code.AllQueriesSatisfy RegistrationNativeIdentityTemplateChosenSource.TemplateAllowed)
    (bounded : code.IsQueryBoundP RegistrationNativeIdentityTemplateCreateCounts.TargetCreate (count+1))
    (publicBefore : Public) (fallback : Forgery) :
    Pr{let result ← ((simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
      (program joint target.val code empty publicBefore)).run PqxdhDynamicIdentityPool.initialState)}[
        RegistrationNativeIdentityTemplateGuardedWins.GenuineWins joint target.val result=true] ≤
    PqxdhJointIdentity.advantage joint
      (RegistrationNativeIdentityTemplateGuardedLateChosen.reduction joint target code empty publicBefore fallback) := by
  have same := RegistrationNativeIdentityTemplateGuardedLateFamily.source_marginal joint (count+1) target.val code empty publicBefore bounded
  have eventEq := same.prEvent_eq (fun result => RegistrationNativeIdentityTemplateGuardedWins.GenuineWins joint target.val result=true)
  simp only [prEvent_map] at eventEq
  rw [eventEq]
  apply le_trans (b := Pr{let result ← (run joint (count+1) target.val code empty publicBefore)}[
    PqxdhJointIdentity.wins joint (PqxdhJointIdentityFamily.familyPublic joint result.1 target)
      ((result.2.1.1.map Prod.snd).getD fallback) (result.2.2.2.histories target)=true])
  · apply prEvent_mono_of_support
    intro result reached won
    have sourceReached : project result ∈ support ((simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
        (program joint target.val code empty publicBefore)).run PqxdhDynamicIdentityPool.initialState) := by
      rw [support_eq_of_evalDistEq same,support_map]
      exact ⟨result,reached,rfl⟩
    cases returned : result.2.1.1 with
    | none => simp only [RegistrationNativeIdentityTemplateGuardedWins.GenuineWins,project,returned,Option.any_none,Bool.false_eq_true] at won
    | some witness =>
      have candidateReturned : (project result).1.1=some witness := returned
      obtain ⟨seed,row,witnessKey⟩ := RegistrationNativeIdentityTemplateGuardedFinalKey.row joint target.val code publicBefore PqxdhDynamicIdentityPool.initialState
        (project result) sourceReached witness candidateReturned
      have key := witnessKey.trans (selected_key joint target result seed row)
      have audit := history joint (count+1) target.val code publicBefore result reached target
      have winsOwn : PqxdhJointIdentity.wins joint witness.1 witness.2
          (RegistrationNativeIdentityHistory.history target.val (project result).2.transcript)=true := by
        simpa only [RegistrationNativeIdentityTemplateGuardedWins.GenuineWins,project,returned,Option.any_some] using won
      simpa only [returned,Option.map_some,Option.getD_some,audit,←key] using winsOwn
  · exact (RegistrationNativeIdentityTemplateGuardedLateChosen.probability_eq joint target code allowed empty publicBefore fallback).le

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFamilyWins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFamilyWins.history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFamilyWins.history
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFamilyWins.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFamilyWins.source_bound
