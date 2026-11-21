-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemFutureGame

/-! This total native reduction retains completed and nonmatching branches. A matching future-reserved key receives the challenge pair; an unmatched pending getter runs its actual public encapsulation. The indexed post service still substitutes the candidate on the selected handle's challenge ciphertext, including in the unmatched branch. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemTotalGame
open PqxdhKemIndCca
open PqxdhInitializerSecrecy
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (Context prepare post)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

def continuation (publicKey : MlKem768PublicKey) (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    Option (RegistrationNativeKemCut.Cut ambient KemSK Bool) → OracleComp (Spec ambient KemSK) Bool
  | none => pure false
  | some (.complete result) => pure result
  | some (.pending key next) => if key = publicKey then next (ciphertext, candidate)
      else (Spec ambient KemSK).query (.inr (.inr key)) >>= next

noncomputable def resume (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) {count : Nat} (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (Context ambient KemSK Auxiliary count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec base) Bool := do
  let result ← (((simulateQ (post kem other selected.val
    (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey transcript.context.others)
    transcript.ciphertext candidate)
    (continuation transcript.publicKey transcript.ciphertext candidate transcript.context.cut)).run).run transcript.context.state)
  pure (result.1.getD false)

noncomputable def adversary (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    OneKeyAdversary kem where
  Context := Context ambient KemSK Auxiliary count
  preChallenge := prepare baseImpl kem other initial work count selected index
  postChallenge := resume kem other selected

noncomputable def branch (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1))
    (index : Nat) (real : Bool) : ProbComp Bool :=
  simulateQ (kemAmbientImpl baseImpl) (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl))
    (adversary baseImpl kem other initial work count selected index) real)

/-- The total native branches have one ordinary IND-CCA advantage without a decision-implies-mark premise. -/
theorem branch_distance (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (branch baseImpl kem other initial work count selected index true).boolDistance
      (branch baseImpl kem other initial work count selected index false) =
      (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (adversary baseImpl kem other initial work count selected index).toINDCCA).toReal := by
  rw [ProbComp.boolDistance_eq_toReal_boolDist]
  exact congrArg ENNReal.toReal (oneKey_indCCAAdvantage_eq_branchDist kem
    (runtimeOfImpl (kemAmbientImpl baseImpl)) (adversary baseImpl kem other initial work count selected index)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_pure _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_bind _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_liftProbComp _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_noFail_bool _)).symm

end BeaconcryptCore.Computational.RegistrationNativeKemTotalGame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTotalGame.branch_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTotalGame.branch_distance
