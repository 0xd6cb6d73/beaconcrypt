-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedGame

/-! The challenge-retaining ordinary CCA adversary executes the unchanged candidate-independent native client under the actual online candidate provider. The candidate is used solely by its final pure observer. Original create/no-reveal bounds suffice for every candidate because the observer performs no queries. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedSource
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemEarlyObservedGame (branch candidateSource)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def reservedSource (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let localState ← initial
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  (simulateQ (RegistrationNativeKemCandidateReserved.reserved baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others)) pair.1 candidate)
    (RegistrationNativeKemEarlyGame.intercept chosen.1 pair.1 candidate (observe candidate <$> work))).run' (localState, PqxdhLiveKemBirth.empty)

/-- The original native query bills remove artificial router stopping for the complete challenge-retaining observation. -/
theorem reserved_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) (real : Bool)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK)) count)
    (noReveal : work.IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := ambient) (KemSK := KemSK)) 0) :
    branch baseImpl kem other initial work observe count selected real =
      reservedSource baseImpl kem other initial work observe count selected real := by
  rw [RegistrationNativeKemEarlyObservedGame.candidate_source]
  unfold candidateSource reservedSource
  simp only [RegistrationNativeKemTotalChallenge.sourcePrepare, RegistrationNativeKemEarlySource.empty_prepare,
    bind_assoc, pure_bind]
  apply bind_congr
  intro chosen
  apply bind_congr
  intro others
  apply bind_congr
  intro localState
  apply bind_congr
  intro pair
  apply bind_congr
  intro uniform
  have observedCreate : (observe (if real then pair.2 else uniform) <$> work).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK)) count := by
    simpa only [OracleComp.isQueryBoundP_map_iff] using bounded
  have observedReveal : (observe (if real then pair.2 else uniform) <$> work).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := ambient) (KemSK := KemSK)) 0 := by
    simpa only [OracleComp.isQueryBoundP_map_iff] using noReveal
  have actual := RegistrationNativeKemCandidateReservedProgram.program_source baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others)) pair.1 (if real then pair.2 else uniform)
    (RegistrationNativeKemEarlyGame.intercept chosen.1 pair.1 (if real then pair.2 else uniform)
      (observe (if real then pair.2 else uniform) <$> work)) count
    (RegistrationNativeKemEarlyBudget.create_bound _ _ _ _ count observedCreate)
    (RegistrationNativeKemEarlyBudget.reveal_bound _ _ _ _ 0 observedReveal)
    (localState, PqxdhDynamicKemRouter.empty) rfl (by simp [PqxdhDynamicKemRouter.empty])
  have mapped := congrArg (Functor.map (fun result => result.1.getD false)) actual
  simpa only [StateT.run'_eq, Functor.map_map, Function.comp_def, Prod.map_def, id_eq,
    RegistrationNativeKemPoolSource.project, PqxdhDynamicKemRouter.sourcePool, PqxdhDynamicKemRouter.empty,
    PqxdhLiveKemBirth.empty, List.take_zero, Option.getD_some, bind_pure_comp] using mapped

noncomputable def source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let localState ← initial
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  observe candidate <$> (simulateQ (RegistrationNativeKemEarlyOnline.online baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 candidate) work).run' ((localState, PqxdhLiveKemBirth.empty), none)

/-- The actual ordinary CCA game retains its challenge candidate across the unchanged whole native execution and applies it only to the final observation. -/
theorem branch_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) (real : Bool)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK)) count)
    (noReveal : work.IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := ambient) (KemSK := KemSK)) 0) :
    branch baseImpl kem other initial work observe count selected real =ᵈ
      source baseImpl kem other initial work observe count selected real := by
  rw [reserved_source baseImpl kem other initial work observe count selected real bounded noReveal]
  unfold reservedSource source
  apply _root_.EvalDistEq.bind_right
  intro chosen
  apply _root_.EvalDistEq.bind_right
  intro others
  apply _root_.EvalDistEq.bind_right
  intro localState
  apply _root_.EvalDistEq.bind_right
  intro pair
  apply _root_.EvalDistEq.bind_right
  intro uniform
  have result := (RegistrationNativeKemEarlyOnline.program_source baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 (if real then pair.2 else uniform)
    (observe (if real then pair.2 else uniform) <$> work) (localState, PqxdhLiveKemBirth.empty)).symm.map Prod.fst
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
    Function.comp_def, Prod.map_def, id_eq] using result

end BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedSource.reserved_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedSource.reserved_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedSource.branch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedSource.branch_source
