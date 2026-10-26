-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds
import BeaconcryptCore.Computational.RawCtxSupportedSample

/-! The ordinary KEM adversary saves a forward proof annotation of its exact executable prephase. Erasure retains literal query syntax for every challenger public key and all typed oracle replies; there is no runtime support test, conditioning or unreachable-context budget premise. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemCertified
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhRegistrationJointKemCommands
open PqxdhRegistrationJointKemChallenge PqxdhRegistrationJointKemResume
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A : Type}

abbrev Saved (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) :=
  (target : MlKem768PublicKey) × {context : Context KemSK A Bool count //
    context ∈ support (pre setup codec checks ensureInit supplied client runtime count selected occurrence target)}

/-- The complete source prephase acquires only an erased proof that its actual returned context was produced by that very executable oracle program. -/
noncomputable def annotatedPre (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (target : MlKem768PublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec)
      (Saved setup codec checks ensureInit supplied client runtime count selected occurrence) :=
  (fun result => ⟨target, result⟩) <$> RawCtxSupportedSample.certify
    (pre setup codec checks ensureInit supplied client runtime count selected occurrence target)
    (fun context => context ∈ support (pre setup codec checks ensureInit supplied client runtime count selected occurrence target))
    (fun _ reached => reached)

/-- Proof erasure restores exactly the same executable prephase, including every query and all replies under an arbitrary public challenger key. -/
theorem prefix_erase (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (target : MlKem768PublicKey) :
    (fun result => result.2.val) <$> annotatedPre setup codec checks ensureInit supplied client runtime count selected occurrence target =
      pre setup codec checks ensureInit supplied client runtime count selected occurrence target := by
  simpa only [annotatedPre, Functor.map_map] using RawCtxSupportedSample.erase
    (pre setup codec checks ensureInit supplied client runtime count selected occurrence target) _ _

/-- Bounded ordinary adversary context contains only the exact source value and an erased support certificate. Its runtime postphase ignores the certificate. -/
noncomputable def adversary (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) : OneKeyAdversary setup.kem where
  Context := Saved setup codec checks ensureInit supplied client runtime count selected occurrence
  preChallenge := annotatedPre setup codec checks ensureInit supplied client runtime count selected occurrence
  postChallenge transcript candidate := PqxdhRegistrationJointKemGame.decision <$>
    post setup count selected ⟨transcript.publicKey, transcript.ciphertext, transcript.context.2.val⟩ candidate

set_option backward.isDefEq.respectTransparency false in
/-- The proof-carrying adversary has exactly the same entire ordinary KEM fixed-branch program; its certificate introduces no query, branch or extra observation. -/
theorem branch_erase (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (real : Bool) :
    oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
      (adversary setup codec checks ensureInit supplied client runtime count selected occurrence) real =
    oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
      (PqxdhRegistrationJointKemGame.adversary setup codec checks ensureInit supplied client runtime count selected occurrence) real := by
  simp only [oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, adversary,
    PqxdhRegistrationJointKemGame.adversary, bind_assoc, pure_bind]
  apply bind_congr
  intro chosen
  have same := congrArg (simulateQ (setup.kem.IND_CCA_preChallengeImpl chosen.2))
    (prefix_erase setup codec checks ensureInit supplied client runtime count selected occurrence chosen.1)
  simp only [simulateQ_map] at same
  rw [← same, bind_map_left]

/-- The actual source-cut advantage is one ordinary KEM advantage for the exact proof-carrying bounded-context adversary. Certificate erasure leaves the source game unchanged. -/
theorem advantage (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (correct : MlKem768RecipientCorrectness setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) :
    (PqxdhRegistrationJointKemGame.sourceReal setup codec checks ensureInit supplied client runtime count selected occurrence).boolDistance
      (PqxdhRegistrationJointKemGame.branch setup codec checks ensureInit supplied client runtime count selected occurrence false) =
      (setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup codec checks ensureInit supplied client runtime count selected occurrence).toINDCCA).toReal := by
  have exactHop := oneKey_indCCAAdvantage_eq_branchDist setup.kem
    (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (adversary setup codec checks ensureInit supplied client runtime count selected occurrence)
    (runtimeOfImpl_evalDist_pure (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_bind (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_liftProbComp setup.baseImpl)
    (runtimeOfImpl_noFail_bool (kemAmbientImpl setup.baseImpl))
  simpa only [oneKeyBranch, branch_erase, runtimeOfImpl_evalDist,
    PqxdhRegistrationJointKemGame.branch_source, PqxdhRegistrationJointKemGame.branch_real setup functional correct,
    ProbComp.boolDistance, MeasureTheory.Measure.toReal_boolDist,
    prEvent_eq_evalDist_singleton] using congrArg ENNReal.toReal exactHop.symm

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemCertified

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCertified.prefix_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCertified.prefix_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCertified.branch_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCertified.branch_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCertified.advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCertified.advantage
