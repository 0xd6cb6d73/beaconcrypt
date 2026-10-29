-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness

/-! Private protocol startup can be sampled inside one ordinary KEM adversary. The sample precedes the actual protocol prephase and is independent of the challenge key generation; its complete concrete context is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemMixture
open PqxdhKemIndCca
open PqxdhInitializerSecrecy
variable {ι KemSK Sample : Type} {base : OracleSpec ι}

noncomputable def adversary (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (sample : ProbComp Sample) (family : Sample → OneKeyAdversary kem) : OneKeyAdversary kem where
  Context := (value : Sample) × (family value).Context
  preChallenge key := do
    let value ← PqxdhPrivateKemSource.ccaCoins sample
    let context ← (family value).preChallenge key
    pure ⟨value, context⟩
  postChallenge transcript candidate :=
    (family transcript.context.1).postChallenge
      ⟨transcript.publicKey, transcript.ciphertext, transcript.context.2⟩ candidate

noncomputable def branch (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (adv : OneKeyAdversary kem) (real : Bool) : ProbComp Bool :=
  simulateQ (kemAmbientImpl baseImpl) (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl)) adv real)

/-- One concrete ordinary KEM branch is the exact startup mixture of its concrete conditional branches. -/
theorem branch_mixture (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (sample : ProbComp Sample) (family : Sample → OneKeyAdversary kem) (real : Bool) :
    EvalDistEq (branch baseImpl kem (adversary kem sample family) real)
      (sample >>= fun value => branch baseImpl kem (family value) real) := by
  simp only [branch, oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, adversary,
    simulateQ_bind, bind_assoc, pure_bind, runtimeOfImpl_liftProbComp,
    simulateQ_kemAmbient_liftProbComp]
  have samples (secret : KemSK) : simulateQ (kemAmbientImpl baseImpl)
      (simulateQ (kem.IND_CCA_preChallengeImpl secret) (PqxdhPrivateKemSource.ccaCoins sample)) = sample :=
    PqxdhPrivateKemSource.evalKem_coins baseImpl kem secret sample
  simp only [samples, simulateQ_pure, pure_bind]
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- A concrete startup mixture is one ordinary IND-CCA reduction, with no sum or supremum over startup outcomes. -/
theorem branch_distance (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (sample : ProbComp Sample)
    (family : Sample → OneKeyAdversary kem) :
    (branch baseImpl kem (adversary kem sample family) true).boolDistance
      (branch baseImpl kem (adversary kem sample family) false) =
      (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (adversary kem sample family).toINDCCA).toReal := by
  rw [ProbComp.boolDistance_eq_toReal_boolDist]
  exact congrArg ENNReal.toReal (oneKey_indCCAAdvantage_eq_branchDist kem
    (runtimeOfImpl (kemAmbientImpl baseImpl)) (adversary kem sample family)
    (runtimeOfImpl_evalDist_pure _) (runtimeOfImpl_evalDist_bind _)
    (runtimeOfImpl_evalDist_liftProbComp _) (runtimeOfImpl_noFail_bool _)).symm

end BeaconcryptCore.Computational.RegistrationNativeKemMixture

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemMixture.branch_mixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemMixture.branch_mixture
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemMixture.branch_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemMixture.branch_distance
