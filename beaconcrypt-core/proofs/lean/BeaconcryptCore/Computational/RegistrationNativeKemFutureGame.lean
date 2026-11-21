-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemGame

/-! The selected private KEM slot is genuinely reserved from its key-generation distribution, while its public creation may occur after the selected Server getter. The cut compares only its actual getter key with the reserved challenge key. Creation still controls all private decapsulation access through the unchanged indexed router, so a future selected owner cannot decapsulate before creation. The saved adversary context contains no selected secret. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemFutureGame
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (Context prepare)
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl runtimeOfImpl)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

def active (publicKey key : MlKem768PublicKey) : Bool := decide (key = publicKey)

noncomputable def resume (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) {count : Nat} (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (Context ambient KemSK Auxiliary count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec base) Bool :=
  match transcript.context.cut with
  | none => pure false
  | some (.complete _) => pure false
  | some (.pending key next) =>
      if active transcript.publicKey key then do
        let result ← (((simulateQ (RegistrationNativeKemGame.post kem other selected.val
          (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey transcript.context.others)
          transcript.ciphertext candidate) (next (transcript.ciphertext, candidate))).run).run transcript.context.state)
        pure (result.1.getD false)
      else pure false

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

/-- A matching genuine reserved key activates independently of whether its public owner is already created. -/
theorem active_key (publicKey key : MlKem768PublicKey) (same : key = publicKey) : active publicKey key = true := by
  simp only [active, same, decide_true]

/-- The future-reserved native two branches have exactly one ordinary IND-CCA advantage. -/
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

end BeaconcryptCore.Computational.RegistrationNativeKemFutureGame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFutureGame.active_key' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFutureGame.active_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFutureGame.branch_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFutureGame.branch_distance
