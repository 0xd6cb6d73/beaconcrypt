-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCut
import BeaconcryptCore.Computational.PqxdhDynamicKemPost

/-! The native indexed KEM cut gives an executable ordinary one-key CCA adversary. The saved context contains the full local state, indexed ownership monitor and exact native continuation, but no selected secret. The active cut checks both its actual public getter and activation of the generated owner. Cross-key byte aliases remain distinct creation indices. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemGame
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemCut (Cut)
open PqxdhKemIndCca
open PqxdhPrivateKemSource (ccaCoins ccaAmbient)
open PqxdhInitializerSecrecy (kemAmbientImpl runtimeOfImpl)
variable {κ ι KemSK Auxiliary Result : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

abbrev State (Auxiliary KemSK : Type) := Auxiliary × PqxdhDynamicKemRouter.State KemSK

/-- A local callback cannot inspect the KEM pool: the pool is a separate private coordinate. -/
def combine {m : Type → Type} [Monad m]
    (coins : {Value : Type} → ProbComp Value → m Value)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (encapsulate : MlKem768PublicKey → m (MlKem768Ciphertext × MlKemSharedSecret))
    (pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
      (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) m))) :
    QueryImpl (Spec ambient KemSK) (OptionT (StateT (State Auxiliary KemSK) m)) := fun query =>
  OptionT.mk fun before => match query with
  | .inl query => (fun result => (some result.1, (result.2, before.2))) <$> coins ((other query).run before.1)
  | .inr (.inl query) => (fun result => (result.1, (before.1, result.2))) <$> ((pool query).run).run before.2
  | .inr (.inr key) => (fun result => (some result, before)) <$> encapsulate key

def pre (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) :=
  combine ccaCoins other (fun key => ccaAmbient (kem.encaps key))
    (PqxdhDynamicKemRouter.pre kem selected reservation)

noncomputable def post (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :=
  combine ccaCoins other (fun key => ccaAmbient (kem.encaps key))
    (PqxdhDynamicKemRouter.post kem selected reservation challenge candidate)

def stopped (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) :=
  combine (fun work => work) other (fun key => simulateQ (kemAmbientImpl baseImpl) (kem.encaps key))
    (PqxdhDynamicKemRouter.source baseImpl kem selected pairs)

noncomputable def expose (work : OracleComp (Spec ambient KemSK) Result) (index : Nat) :
    OracleComp (Spec ambient KemSK) (Cut ambient KemSK Result) :=
  RegistrationNativeKemCut.scan (fun query => (Spec ambient KemSK).query query) work index

structure Context (ambient : OracleSpec κ) (KemSK Auxiliary : Type) (count : Nat) where
  others : Fin count → MlKem768PublicKey × KemSK
  cut : Option (Cut ambient KemSK Bool)
  state : State Auxiliary KemSK

noncomputable def prepare (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1))
    (index : Nat) (publicKey : MlKem768PublicKey) :
    OracleComp (MlKemCCAOracleSpec base) (Context ambient KemSK Auxiliary count) := do
  let others ← ccaCoins (PqxdhLiveKemSelection.sampleFamily
    (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count)
  let localState ← ccaCoins initial
  let result ← (((simulateQ (pre kem other selected.val
    (PqxdhDynamicKemRouter.selectedReservation selected publicKey others)) (expose work index)).run).run
      (localState, PqxdhDynamicKemRouter.empty))
  pure ⟨others, result.1, result.2⟩

/-- This is a real created-owner test, rather than an assertion of honesty from arbitrary accepted bytes. -/
def active {count : Nat} (selected : Fin (count + 1)) (publicKey key : MlKem768PublicKey)
    (context : Context ambient KemSK Auxiliary count) : Bool :=
  decide (key = publicKey ∧ selected.val < context.state.2.created)

noncomputable def resume (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) {count : Nat} (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (Context ambient KemSK Auxiliary count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec base) Bool :=
  match transcript.context.cut with
  | none => pure false
  | some (.complete _) => pure false
  | some (.pending key next) =>
      if active selected transcript.publicKey key transcript.context then do
        let result ← (((simulateQ (post kem other selected.val
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

/-- The actual native cut's two branches have exactly the ordinary one-key CCA advantage, with coefficient one. -/
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

end BeaconcryptCore.Computational.RegistrationNativeKemGame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemGame.branch_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemGame.branch_distance
