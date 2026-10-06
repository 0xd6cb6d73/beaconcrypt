-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemResume

/-! One ordinary IND-CCA adversary runs the literal initialized source prefix to an actual encapsulation occurrence and resumes its exact callback. These games filter inactive selection and selected-key reveal stops; they are not an unfiltered global protocol secrecy assertion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemGame
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhRegistrationJointKemCommands
open PqxdhRegistrationJointKemChallenge PqxdhRegistrationJointKemResume
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A : Type}

/-- Only the original public source decision contributes to the event; inactive selection and later reveal stops produce false. The reduction never tests private context fields to choose its decision. -/
def decision {count : Nat} (result : ResultState KemSK A Bool count) : Bool :=
  match result.2 with
  | some (some outcome, _) => outcome.1.1
  | _ => false

/-- The constructed ordinary adversary receives only a public challenge key and a private candidate reply, then runs the actual initialized source compiler and its saved callback. -/
noncomputable def adversary (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) : OneKeyAdversary setup.kem where
  Context := Context KemSK A Bool count
  preChallenge := pre setup codec checks ensureInit supplied client runtime count selected occurrence
  postChallenge transcript candidate := decision <$> post setup count selected transcript candidate

/-- The source-ordered prefix has its actual constructor and the selected-first reservations already justified separately; the remaining candidate branch uses the ordinary blocked CCA interpreter. Both branches retain the challenger encapsulation and the branch-independent uniform draw. -/
noncomputable def branch (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePre setup codec checks ensureInit supplied client runtime count selected occurrence chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2 encapsulated.1
    (post setup count selected ⟨chosen.1, encapsulated.1, context⟩ (if real then encapsulated.2 else uniform))

/-- The real cut game resumes the literal source callback through the original stopped source interpreter. It retains the harmless challenger ghost draw so its resource ledger also records that work. -/
noncomputable def sourceReal (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePre setup codec checks ensureInit supplied client runtime count selected occurrence chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let _ ← $ᵗ MlKemSharedSecret
  decision <$> sourcePost setup count selected chosen ⟨chosen.1, encapsulated.1, context⟩ encapsulated.2

set_option backward.isDefEq.respectTransparency false in
/-- The complete fixed branch of the constructed ordinary adversary equals the explicit source-cut branch, including failed initialization and every inactive or stopped continuation. -/
theorem branch_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (real : Bool) :
    simulateQ (kemAmbientImpl setup.baseImpl)
      (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup codec checks ensureInit supplied client runtime count selected occurrence) real) =
      branch setup codec checks ensureInit supplied client runtime count selected occurrence real := by
  simp only [oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, adversary, branch,
    simulateQ_bind, bind_assoc, pure_bind, runtimeOfImpl_liftProbComp,
    simulateQ_kemAmbient_liftProbComp, simulateQ_map]
  apply bind_congr
  intro chosen
  have same := pre_source setup codec checks ensureInit supplied client runtime count selected occurrence chosen
  change simulateQ (kemAmbientImpl setup.baseImpl)
    (simulateQ (setup.kem.IND_CCA_preChallengeImpl chosen.2)
      (pre setup codec checks ensureInit supplied client runtime count selected occurrence chosen.1)) = _ at same
  rw [same]
  rfl

/-- The real branch is the actual stopped source cut on generated keys, by ordinary recipient correctness. Every saved native/owner continuation remains unchanged before the original public decision is projected. -/
theorem branch_real (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (correct : MlKem768RecipientCorrectness setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) :
    branch setup codec checks ensureInit supplied client runtime count selected occurrence true =
      sourceReal setup codec checks ensureInit supplied client runtime count selected occurrence := by
  unfold branch sourceReal
  apply bind_congr_of_forall_mem_support
  intro chosen generated
  apply bind_congr
  intro context
  apply bind_congr_of_forall_mem_support
  intro encapsulated supported
  apply bind_congr
  intro uniform
  exact congrArg (fun work => decision <$> work)
    (supported_source setup functional correct count selected chosen generated context
      encapsulated.1 encapsulated.2 supported)

/-- The explicit real source-cut game and its challenge-candidate replacement have exactly one constructed ordinary ML-KEM IND-CCA advantage. This is an occurrence/creation-index filtered hop, not a global selection or freshness theorem. -/
theorem advantage (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (correct : MlKem768RecipientCorrectness setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) :
    (sourceReal setup codec checks ensureInit supplied client runtime count selected occurrence).boolDistAdvantage
      (branch setup codec checks ensureInit supplied client runtime count selected occurrence false) =
      setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup codec checks ensureInit supplied client runtime count selected occurrence).toINDCCA := by
  have exactHop := oneKey_indCCAAdvantage_eq_branchDist setup.kem
    (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (adversary setup codec checks ensureInit supplied client runtime count selected occurrence)
    (runtimeOfImpl_evalDist_pure (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_bind (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_liftProbComp setup.baseImpl)
    (runtimeOfImpl_noFail_bool (kemAmbientImpl setup.baseImpl))
  simpa only [oneKeyBranch, runtimeOfImpl_evalDist, branch_source,
    branch_real setup functional correct, ProbComp.boolDistAdvantage, SPMF.boolDistAdvantage,
    MeasureTheory.Measure.boolDist, probOutput_def, evalDist_apply_singleton] using exactHop.symm

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemGame

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemGame.branch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemGame.branch_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemGame.branch_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemGame.branch_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemGame.advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemGame.advantage
