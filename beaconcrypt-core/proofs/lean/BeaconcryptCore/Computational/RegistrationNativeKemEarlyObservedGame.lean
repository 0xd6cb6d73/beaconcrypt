-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyOnline

/-! The ordinary CCA challenge supplies its candidate explicitly to a pure final observer of the unchanged native program. The running program and its query bills remain candidate independent. The adversary retains that challenge value across the complete execution, including inactive and mismatched getter paths. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedGame
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl runtimeOfImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (Context)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def adversary (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) : OneKeyAdversary kem where
  Context := Context ambient KemSK Auxiliary count
  preChallenge := RegistrationNativeKemGame.prepare baseImpl kem other initial (pure false) count selected 0
  postChallenge := fun transcript candidate =>
    RegistrationNativeKemEarlyGame.resume kem other (observe candidate <$> work) selected transcript candidate

noncomputable def branch (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) (real : Bool) : ProbComp Bool :=
  simulateQ (kemAmbientImpl baseImpl) (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl))
    (adversary baseImpl kem other initial work observe count selected) real)

/-- Retaining the supplied challenge candidate in a pure final observer costs exactly one explicit ordinary CCA advantage. -/
theorem branch_distance (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) :
    (branch baseImpl kem other initial work observe count selected true).boolDistance
      (branch baseImpl kem other initial work observe count selected false) =
      (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (adversary baseImpl kem other initial work observe count selected).toINDCCA).toReal := by
  rw [ProbComp.boolDistance_eq_toReal_boolDist]
  exact congrArg ENNReal.toReal (oneKey_indCCAAdvantage_eq_branchDist kem
    (runtimeOfImpl (kemAmbientImpl baseImpl)) (adversary baseImpl kem other initial work observe count selected)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_pure _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_bind _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_liftProbComp _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_noFail_bool _)).symm

noncomputable def expanded (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let context ← RegistrationNativeKemTotalChallenge.sourcePrepare baseImpl kem other initial (pure false) count selected 0 chosen
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  PqxdhDynamicKemPost.evaluate baseImpl kem chosen.2 pair.1
    (RegistrationNativeKemEarlyGame.resume kem other (observe candidate <$> work) selected ⟨chosen.1, pair.1, context⟩ candidate)

/-- The actual challenge-retaining adversary has its literal complete prephase and candidate-dependent pure post-observation. -/
theorem expanded_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) (real : Bool) :
    branch baseImpl kem other initial work observe count selected real =
      expanded baseImpl kem other initial work observe count selected real := by
  simp only [branch, adversary, oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, expanded,
    simulateQ_bind, bind_assoc, pure_bind, PqxdhInitializerSecrecy.runtimeOfImpl_liftProbComp,
    PqxdhInitializerSecrecy.simulateQ_kemAmbient_liftProbComp]
  apply bind_congr
  intro chosen
  have same := RegistrationNativeKemChallenge.prepare_source baseImpl kem other initial (pure false) count selected 0 chosen
  change simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (kem.IND_CCA_preChallengeImpl chosen.2)
      (RegistrationNativeKemGame.prepare baseImpl kem other initial (pure false) count selected 0 chosen.1)) = _ at same
  rw [same]
  rfl

noncomputable def candidateSource (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let context ← RegistrationNativeKemTotalChallenge.sourcePrepare baseImpl kem other initial (pure false) count selected 0 chosen
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  let result ← (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen context.others)) pair.1 candidate)
    (RegistrationNativeKemEarlyGame.intercept chosen.1 pair.1 candidate (observe candidate <$> work))).run).run context.state)
  pure (result.1.getD false)

/-- The complete observed branches retain the actual candidate source semantics from the initial native query. -/
theorem candidate_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) (real : Bool) :
    branch baseImpl kem other initial work observe count selected real =
      candidateSource baseImpl kem other initial work observe count selected real := by
  rw [expanded_source]
  unfold expanded candidateSource
  apply bind_congr
  intro chosen
  apply bind_congr
  intro context
  apply bind_congr
  intro pair
  apply bind_congr
  intro uniform
  have same := RegistrationNativeKemCandidateSource.post_program baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen context.others)) chosen.1 chosen.2
    (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using
      PqxdhLiveKemSelection.selected_index [] selected chosen context.others)
    pair.1 (if real then pair.2 else uniform)
    (RegistrationNativeKemEarlyGame.intercept chosen.1 pair.1 (if real then pair.2 else uniform)
      (observe (if real then pair.2 else uniform) <$> work)) context.state
  rw [PqxdhDynamicKemRouter.selected_reservation] at same
  simpa only [RegistrationNativeKemEarlyGame.resume, PqxdhDynamicKemPost.evaluate,
    simulateQ_map, simulateQ_pure, bind_pure_comp] using congrArg (Functor.map (fun result => result.1.getD false)) same

end BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedGame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedGame.branch_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedGame.branch_distance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedGame.expanded_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedGame.expanded_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedGame.candidate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedGame.candidate_source
