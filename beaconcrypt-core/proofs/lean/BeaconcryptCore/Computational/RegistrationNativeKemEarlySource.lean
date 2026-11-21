-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyCorrectness

/-! Sampling the reserved selected key's challenge before the protocol does not change the real source. Before the first exposed getter, the original stopped source has not received that independently sampled ciphertext or secret. Swapping its genuine prefix with that sample therefore recovers the already proved complete source reconstruction, including runs with no getter, rejected getters and later-born designated owners. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemEarlySource
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (Context State stopped expose)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

/-- The early CCA prephase samples only independent other keys and the literal initial auxiliary state. -/
theorem empty_prepare (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK) :
    RegistrationNativeKemChallenge.sourcePrepare baseImpl kem other initial (pure false) count selected 0 chosen = (do
      let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
      let localState ← initial
      pure (⟨others, some (.complete false), (localState, PqxdhDynamicKemRouter.empty)⟩ : Context ambient KemSK Auxiliary count)) := by
  have exposed : expose (pure false : OracleComp (Spec ambient KemSK) Bool) 0 = pure (.complete false) := rfl
  simp only [RegistrationNativeKemChallenge.sourcePrepare, exposed,
    simulateQ_pure, OptionT.run_pure, StateT.run_pure, pure_bind]

/-- The early source executes its actual complete prefix before resuming the same optional cut and continuation. -/
theorem post_cut (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (context : Context ambient KemSK Auxiliary count)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (work : OracleComp (Spec ambient KemSK) Bool) :
    RegistrationNativeKemEarlyGame.sourcePost baseImpl kem other selected chosen context challenge candidate work = (do
      let leading ← (((simulateQ (stopped baseImpl kem other selected.val
        (List.ofFn (selected.insertNth chosen context.others))) (expose work 0)).run).run context.state)
      RegistrationNativeKemTotalChallenge.sourcePost baseImpl kem other selected chosen
        ⟨chosen.1, challenge, ⟨context.others, leading.1, leading.2⟩⟩ candidate) := by
  simp only [RegistrationNativeKemEarlyGame.sourcePost, RegistrationNativeKemEarlyGame.intercept,
    simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind, bind_pure_comp]
  apply bind_congr
  rintro ⟨none | cut, after⟩
  · simp only [Option.elim_none, StateT.run_pure, map_pure, Option.getD_none,
      RegistrationNativeKemTotalChallenge.sourcePost, RegistrationNativeKemTotalGame.continuation,
      simulateQ_pure, OptionT.run_pure, pure_bind, Option.getD_some]
  · simp only [Option.elim_some, RegistrationNativeKemTotalChallenge.sourcePost, bind_pure_comp]

noncomputable def samplePair (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (key : MlKem768PublicKey) :
    ProbComp (MlKem768Ciphertext × MlKemSharedSecret) := do
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)
  let _ ← $ᵗ MlKemSharedSecret
  pure pair

/-- The actual early real branch equals the original complete reserved native source, without a temporal or source-simulation premise. -/
theorem source_real (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) :
    EvalDistEq (RegistrationNativeKemEarlyCorrectness.sourceReal baseImpl kem other initial work count selected)
      (RegistrationNativeKemTotalSource.source baseImpl kem other initial work count selected) := by
  refine _root_.EvalDistEq.trans ?_
    (RegistrationNativeKemTotalSource.source_real baseImpl kem other initial work count selected 0)
  unfold RegistrationNativeKemEarlyCorrectness.sourceReal RegistrationNativeKemTotalCorrectness.sourceReal
  simp only [RegistrationNativeKemTotalChallenge.sourcePrepare, empty_prepare]
  simp only [RegistrationNativeKemChallenge.sourcePrepare, bind_assoc, pure_bind]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro chosen _generated
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro others _sampled
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro localState _initialized
  simp only [post_cut]
  have swapped := OracleComp.EvalDistEq.bind_bind_swap (samplePair baseImpl kem chosen.1)
    ((((simulateQ (stopped baseImpl kem other selected.val (List.ofFn (selected.insertNth chosen others)))
      (expose work 0)).run).run (localState, PqxdhDynamicKemRouter.empty)))
    (fun pair leading => RegistrationNativeKemTotalChallenge.sourcePost baseImpl kem other selected chosen
      ⟨chosen.1, pair.1, ⟨others, leading.1, leading.2⟩⟩ pair.2)
  simpa only [samplePair, bind_assoc, pure_bind] using swapped

/-- The original reserved native source has one ordinary CCA loss and one correctness loss against the early candidate replacement, with no restriction on when an owner finishes. -/
theorem source_close (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) :
    (RegistrationNativeKemTotalSource.source baseImpl kem other initial work count selected).boolDistance
      (RegistrationNativeKemEarlyGame.branch baseImpl kem other initial work count selected false) ≤
      (kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (kemAmbientImpl baseImpl))
        (RegistrationNativeKemEarlyGame.adversary baseImpl kem other initial work count selected).toINDCCA).toReal +
      RegistrationNativeKemEarlyCorrectness.correctnessError baseImpl kem := by
  have equal := (source_real baseImpl kem other initial work count selected).prEvent_eq (fun result => result = true)
  have bound := RegistrationNativeKemEarlyCorrectness.source_close baseImpl kem functional other initial work count selected
  simpa only [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton, equal] using bound

end BeaconcryptCore.Computational.RegistrationNativeKemEarlySource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlySource.empty_prepare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlySource.empty_prepare
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlySource.post_cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlySource.post_cut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlySource.source_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlySource.source_real
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlySource.source_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlySource.source_close
