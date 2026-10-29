-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness
import BeaconcryptCore.Computational.RegistrationNativeKemTotalSource

/-! The reserved genuine key is challenged before the whole protocol program. Its ordinary CCA prephase samples only independent other keys and initial auxiliary state. Thus exact selected-handle challenge-ciphertext decapsulations use the supplied candidate even before the selected parsed getter, while current birth and reveal stopping remain the actual indexed service rules. The first exposed getter receives the challenge only when its public key matches; completed and nonmatching executions remain present. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemEarlyGame
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl runtimeOfImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (Context post stopped)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def intercept (publicKey : MlKem768PublicKey) (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (Spec ambient KemSK) Bool) : OracleComp (Spec ambient KemSK) Bool := do
  let cut ← RegistrationNativeKemGame.expose work 0
  RegistrationNativeKemTotalGame.continuation publicKey ciphertext candidate (some cut)

noncomputable def resume (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (work : OracleComp (Spec ambient KemSK) Bool)
    {count : Nat} (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (Context ambient KemSK Auxiliary count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec base) Bool := do
  let result ← (((simulateQ (post kem other selected.val
    (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey transcript.context.others)
    transcript.ciphertext candidate)
    (intercept transcript.publicKey transcript.ciphertext candidate work)).run).run transcript.context.state)
  pure (result.1.getD false)

noncomputable def adversary (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) : OneKeyAdversary kem where
  Context := Context ambient KemSK Auxiliary count
  preChallenge := RegistrationNativeKemGame.prepare baseImpl kem other initial (pure false) count selected 0
  postChallenge := resume kem other work selected

noncomputable def branch (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (real : Bool) : ProbComp Bool :=
  simulateQ (kemAmbientImpl baseImpl) (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl))
    (adversary baseImpl kem other initial work count selected) real)

/-- The early candidate experiment is one explicitly constructed ordinary IND-CCA adversary with an empty protocol prephase. -/
theorem branch_distance (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) :
    (branch baseImpl kem other initial work count selected true).boolDistance
      (branch baseImpl kem other initial work count selected false) =
      (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (adversary baseImpl kem other initial work count selected).toINDCCA).toReal := by
  rw [ProbComp.boolDistance_eq_toReal_boolDist]
  exact congrArg ENNReal.toReal (oneKey_indCCAAdvantage_eq_branchDist kem
    (runtimeOfImpl (kemAmbientImpl baseImpl)) (adversary baseImpl kem other initial work count selected)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_pure _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_bind _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_liftProbComp _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_noFail_bool _)).symm

noncomputable def sourcePost (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (context : Context ambient KemSK Auxiliary count)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (work : OracleComp (Spec ambient KemSK) Bool) : ProbComp Bool := do
  let result ← (((simulateQ (stopped baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen context.others)))
    (intercept chosen.1 challenge candidate work)).run).run context.state)
  pure (result.1.getD false)

/-- One genuine recipient-correctness fact restores the entire protocol, including selected challenge-ciphertext decapsulations before its first getter. -/
theorem resume_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (context : Context ambient KemSK Auxiliary count)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (work : OracleComp (Spec ambient KemSK) Bool)
    (agreement : kem.decaps chosen.2 challenge = pure (some candidate)) :
    PqxdhDynamicKemPost.evaluate baseImpl kem chosen.2 challenge
      (resume kem other work selected ⟨chosen.1, challenge, context⟩ candidate) =
      sourcePost baseImpl kem other selected chosen context challenge candidate work := by
  have same := RegistrationNativeKemSource.post_program baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen context.others)) chosen.1 chosen.2
    (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using
      PqxdhLiveKemSelection.selected_index [] selected chosen context.others)
    challenge candidate agreement (intercept chosen.1 challenge candidate work) context.state
  rw [PqxdhDynamicKemRouter.selected_reservation] at same
  simpa only [resume, sourcePost, PqxdhDynamicKemPost.evaluate, simulateQ_map,
    simulateQ_pure, bind_pure_comp] using congrArg (Functor.map (fun result => result.1.getD false)) same

end BeaconcryptCore.Computational.RegistrationNativeKemEarlyGame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyGame.branch_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyGame.branch_distance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyGame.resume_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyGame.resume_source
