-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCertified

/-! The ordinary raw-ordinal KEM adversary saves a forward proof annotation of its exact executable prephase, as `KemCertified` does for the encapsulation-ordinal adversary. Erasure retains literal query syntax for every challenger public key and all typed oracle replies; there is no runtime support test, conditioning or unreachable-context budget premise. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawCertified
open PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemChallenge (Context)
open PqxdhRegistrationJointKemResume (post)
open PqxdhRegistrationJointKemRawChallenge (preRaw)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- A saved context of the raw-ordinal prephase together with an erased proof that it was produced by that executable prephase at the recorded public key. -/
abbrev Saved (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :=
  (target : MlKem768PublicKey) × {context : Context KemSK A Bool count //
    context ∈ support (preRaw setup codec checks ensureInit supplied decision work runtime count selected index target)}

/-- The complete raw-ordinal prephase acquires only an erased proof that its returned context was produced by that very executable oracle program. -/
noncomputable def annotatedPre (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec)
      (Saved setup codec checks ensureInit supplied decision work runtime count selected index) :=
  (fun result => ⟨target, result⟩) <$> RawCtxSupportedSample.certify
    (preRaw setup codec checks ensureInit supplied decision work runtime count selected index target)
    (fun context => context ∈ support
      (preRaw setup codec checks ensureInit supplied decision work runtime count selected index target))
    (fun _ reached => reached)

/-- Proof erasure restores exactly the same executable raw-ordinal prephase, including every query and all replies under an arbitrary public challenger key. -/
theorem prefix_erase (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey) :
    (fun result => result.2.val) <$>
      annotatedPre setup codec checks ensureInit supplied decision work runtime count selected index target =
      preRaw setup codec checks ensureInit supplied decision work runtime count selected index target := by
  simpa only [annotatedPre, Functor.map_map] using RawCtxSupportedSample.erase
    (preRaw setup codec checks ensureInit supplied decision work runtime count selected index target) _ _

/-- The bounded ordinary raw-ordinal adversary: its context contains only the exact source value and an erased support certificate, and its postphase ignores the certificate. -/
noncomputable def adversary (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : OneKeyAdversary setup.kem where
  Context := Saved setup codec checks ensureInit supplied decision work runtime count selected index
  preChallenge := annotatedPre setup codec checks ensureInit supplied decision work runtime count selected index
  postChallenge transcript candidate := PqxdhRegistrationJointKemGame.decision <$>
    post setup count selected ⟨transcript.publicKey, transcript.ciphertext, transcript.context.2.val⟩ candidate

set_option backward.isDefEq.respectTransparency false in
/-- The proof-carrying raw-ordinal adversary has exactly the same ordinary fixed-branch program as the plain one; its certificate introduces no query, branch or extra observation. -/
theorem branch_erase (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
      (adversary setup codec checks ensureInit supplied decision work runtime count selected index) real =
    oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
      (PqxdhRegistrationJointKemRawGame.adversary setup codec checks ensureInit supplied decision work runtime count
        selected index) real := by
  simp only [oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, adversary,
    PqxdhRegistrationJointKemRawGame.adversary, bind_assoc, pure_bind]
  apply bind_congr
  intro chosen
  have same := congrArg (simulateQ (setup.kem.IND_CCA_preChallengeImpl chosen.2))
    (prefix_erase setup codec checks ensureInit supplied decision work runtime count selected index chosen.1)
  simp only [simulateQ_map] at same
  rw [← same, bind_map_left]

/-- The real raw-ordinal game and its candidate replacement are within one ordinary one-key ML-KEM IND-CCA advantage of the exact proof-carrying adversary plus one ordinary ML-KEM correctness error, both with coefficient one (theorem T3 of the plan). Certificate erasure leaves the game unchanged; no perfect-correctness premise is used. -/
theorem advantage (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (PqxdhRegistrationJointKemRawGame.sourceReal setup codec checks ensureInit supplied decision work runtime count
      selected index).boolDistAdvantage
      (PqxdhRegistrationJointKemRawGame.branch setup codec checks ensureInit supplied decision work runtime count
        selected index false) ≤
      setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup codec checks ensureInit supplied decision work runtime count selected index).toINDCCA +
        PqxdhRegistrationJointKemRawGame.correctnessError setup := by
  have certified := oneKey_indCCAAdvantage_eq_branchDist setup.kem
    (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (adversary setup codec checks ensureInit supplied decision work runtime count selected index)
    (runtimeOfImpl_evalDist_pure (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_bind (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_liftProbComp setup.baseImpl)
    (runtimeOfImpl_noFail_bool (kemAmbientImpl setup.baseImpl))
  have plain := oneKey_indCCAAdvantage_eq_branchDist setup.kem
    (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (PqxdhRegistrationJointKemRawGame.adversary setup codec checks ensureInit supplied decision work runtime count
      selected index)
    (runtimeOfImpl_evalDist_pure (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_bind (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_liftProbComp setup.baseImpl)
    (runtimeOfImpl_noFail_bool (kemAmbientImpl setup.baseImpl))
  have same : setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
      (adversary setup codec checks ensureInit supplied decision work runtime count selected index).toINDCCA =
      setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawGame.adversary setup codec checks ensureInit supplied decision work runtime
          count selected index).toINDCCA := by
    rw [certified, plain]
    simp only [oneKeyBranch, branch_erase]
  rw [same]
  exact PqxdhRegistrationJointKemRawGame.advantageRaw_error setup functional codec checks ensureInit supplied
    decision work runtime count selected index

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawCertified

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawCertified.prefix_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawCertified.prefix_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawCertified.branch_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawCertified.branch_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawCertified.advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawCertified.advantage
