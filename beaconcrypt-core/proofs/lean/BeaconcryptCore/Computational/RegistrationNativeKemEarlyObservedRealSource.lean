-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyRealOnline
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedCorrectness

/-! The explicit real challenge-retaining source executes the unchanged complete native program with its genuine reserved KEM pool and real decapsulations. The candidate reaches only a pure final observer. Original create/no-reveal bills remove the artificial stopped-router state; no candidate-dependent prefix swap is used. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedRealSource
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def reservedSource (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let localState ← initial
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let _ ← $ᵗ MlKemSharedSecret
  (simulateQ (RegistrationNativeKemReservation.reserved baseImpl kem other
    (List.ofFn (selected.insertNth chosen others)))
    (RegistrationNativeKemEarlyGame.intercept chosen.1 pair.1 pair.2 (observe pair.2 <$> work))).run' (localState, PqxdhLiveKemBirth.empty)

/-- The actual real observed source retains the genuine full reserved pool under the original bills; every decapsulation remains its actual real computation. -/
theorem reserved_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1))
    (bounded : work.IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK)) count)
    (noReveal : work.IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := ambient) (KemSK := KemSK)) 0) :
    RegistrationNativeKemEarlyObservedCorrectness.sourceReal baseImpl kem other initial work observe count selected =
      reservedSource baseImpl kem other initial work observe count selected := by
  unfold RegistrationNativeKemEarlyObservedCorrectness.sourceReal reservedSource
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
  intro unused
  have observedCreate : (observe pair.2 <$> work).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK)) count := by
    simpa only [OracleComp.isQueryBoundP_map_iff] using bounded
  have observedReveal : (observe pair.2 <$> work).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := ambient) (KemSK := KemSK)) 0 := by
    simpa only [OracleComp.isQueryBoundP_map_iff] using noReveal
  have actual := RegistrationNativeKemPoolSource.program_source baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others))
    (RegistrationNativeKemEarlyGame.intercept chosen.1 pair.1 pair.2 (observe pair.2 <$> work)) count
    (RegistrationNativeKemEarlyBudget.create_bound _ _ _ _ count observedCreate)
    (RegistrationNativeKemEarlyBudget.reveal_bound _ _ _ _ 0 observedReveal)
    (localState, PqxdhDynamicKemRouter.empty) rfl (by simp [PqxdhDynamicKemRouter.empty])
  have mapped := congrArg (Functor.map (fun result => result.1.getD false)) actual
  simpa only [RegistrationNativeKemEarlyGame.sourcePost, StateT.run'_eq, Functor.map_map,
    Function.comp_def, Prod.map_def, id_eq, RegistrationNativeKemPoolSource.project,
    PqxdhDynamicKemRouter.sourcePool, PqxdhDynamicKemRouter.empty, PqxdhLiveKemBirth.empty,
    List.take_zero, Option.getD_some, bind_pure_comp] using mapped

noncomputable def source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let localState ← initial
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let _ ← $ᵗ MlKemSharedSecret
  observe pair.2 <$> (simulateQ (RegistrationNativeKemEarlyRealOnline.online baseImpl kem other
    (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 pair.2) work).run' ((localState, PqxdhLiveKemBirth.empty), none)

/-- The explicit real challenge-retaining source runs the unchanged client online with genuine real decapsulation, retaining the final candidate observation. -/
theorem source_real (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1))
    (bounded : work.IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK)) count)
    (noReveal : work.IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := ambient) (KemSK := KemSK)) 0) :
    RegistrationNativeKemEarlyObservedCorrectness.sourceReal baseImpl kem other initial work observe count selected =ᵈ
      source baseImpl kem other initial work observe count selected := by
  rw [reserved_source baseImpl kem other initial work observe count selected bounded noReveal]
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
  intro unused
  have result := (RegistrationNativeKemEarlyRealOnline.program_source baseImpl kem other
    (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 pair.2
    (observe pair.2 <$> work) (localState, PqxdhLiveKemBirth.empty)).symm.map Prod.fst
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
    Function.comp_def, Prod.map_def, id_eq] using result

/-- The unchanged complete real native execution with a retained pure candidate observation pays one explicit ordinary CCA advantage and one unconditional correctness loss. -/
theorem source_close (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1))
    (bounded : work.IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK)) count)
    (noReveal : work.IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := ambient) (KemSK := KemSK)) 0) :
    (source baseImpl kem other initial work observe count selected).boolDistance
      (RegistrationNativeKemEarlyObservedGame.branch baseImpl kem other initial work observe count selected false) ≤
      (kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (kemAmbientImpl baseImpl))
        (RegistrationNativeKemEarlyObservedGame.adversary baseImpl kem other initial work observe count selected).toINDCCA).toReal +
      RegistrationNativeKemEarlyCorrectness.correctnessError baseImpl kem := by
  have equal := (source_real baseImpl kem other initial work observe count selected bounded noReveal).prEvent_eq (fun result => result = true)
  have bound := RegistrationNativeKemEarlyObservedCorrectness.source_close baseImpl kem functional other initial work observe count selected
  simpa only [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton, equal] using bound

end BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedRealSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedRealSource.reserved_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedRealSource.reserved_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedRealSource.source_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedRealSource.source_real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedRealSource.source_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedRealSource.source_close
