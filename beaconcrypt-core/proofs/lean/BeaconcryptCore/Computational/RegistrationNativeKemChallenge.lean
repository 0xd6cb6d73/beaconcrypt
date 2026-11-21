-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSource

/-! The native one-key adversary has the exact actual stopped native prephase and literal saved continuation. Real-candidate recipient agreement identifies its complete postphase with actual indexed source execution. The only supplied equality concerns ordinary KEM decapsulation, never a protocol or game simulation. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemChallenge
open PqxdhKemIndCca
open PqxdhPrivateKemSource (evalKem evalKem_coins)
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (State Context expose active stopped prepare resume)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def sourcePrepare (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (initial : ProbComp Auxiliary) (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    ProbComp (Context ambient KemSK Auxiliary count) := do
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let localState ← initial
  let result ← (((simulateQ (stopped baseImpl kem other selected.val (List.ofFn (selected.insertNth chosen others)))
    (expose work index)).run).run (localState, PqxdhDynamicKemRouter.empty))
  pure ⟨others, result.1, result.2⟩

/-- Exact actual native source prephase, including every creation, optional callback, stopped reveal and private state field. -/
theorem prepare_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (initial : ProbComp Auxiliary) (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    evalKem baseImpl kem chosen.2 (prepare baseImpl kem other initial work count selected index chosen.1) =
      sourcePrepare baseImpl kem other initial work count selected index chosen := by
  simp only [prepare, sourcePrepare, evalKem, simulateQ_bind]
  rw [show simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl kem chosen.2)
      (PqxdhPrivateKemSource.ccaCoins (PqxdhLiveKemSelection.sampleFamily
        (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count))) = _ from evalKem_coins baseImpl kem chosen.2 _]
  apply bind_congr
  intro others
  rw [show simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl kem chosen.2)
      (PqxdhPrivateKemSource.ccaCoins initial)) = initial from evalKem_coins baseImpl kem chosen.2 initial]
  apply bind_congr
  intro localState
  have same := RegistrationNativeKemSource.pre_program baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others)) chosen.1 chosen.2
    (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using
      PqxdhLiveKemSelection.selected_index [] selected chosen others)
    (expose work index) (localState, PqxdhDynamicKemRouter.empty)
  rw [PqxdhDynamicKemRouter.selected_reservation] at same
  simpa only [evalKem, simulateQ_pure, bind_pure_comp] using congrArg
    (Functor.map (fun result => (⟨others, result.1, result.2⟩ : Context ambient KemSK Auxiliary count))) same

noncomputable def sourcePost (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    {count : Nat} (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (transcript : MlKemChallengeTranscript (Context ambient KemSK Auxiliary count)) (candidate : MlKemSharedSecret) :
    ProbComp Bool :=
  match transcript.context.cut with
  | none => pure false
  | some (.complete _) => pure false
  | some (.pending key next) =>
      if active selected transcript.publicKey key transcript.context then do
        let result ← (((simulateQ (stopped baseImpl kem other selected.val
          (List.ofFn (selected.insertNth chosen transcript.context.others)))
          (next (transcript.ciphertext, candidate))).run).run transcript.context.state)
        pure (result.1.getD false)
      else pure false

/-- Correctness on the actual selected ciphertext recovers the complete actual native postphase, preserving all repeated decapsulations and full private state. -/
theorem resume_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    {count : Nat} (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (context : Context ambient KemSK Auxiliary count) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (agreement : kem.decaps chosen.2 challenge = pure (some candidate)) :
    PqxdhDynamicKemPost.evaluate baseImpl kem chosen.2 challenge
      (resume kem other selected ⟨chosen.1, challenge, context⟩ candidate) =
      sourcePost baseImpl kem other selected chosen ⟨chosen.1, challenge, context⟩ candidate := by
  cases cutFound : context.cut with
  | none => simp [resume, sourcePost, cutFound, PqxdhDynamicKemPost.evaluate]
  | some cut =>
    cases cut with
    | complete result => simp [resume, sourcePost, cutFound, PqxdhDynamicKemPost.evaluate]
    | pending key next =>
      simp only [resume, sourcePost, cutFound]
      split
      · have same := RegistrationNativeKemSource.post_program baseImpl kem other selected.val
          (List.ofFn (selected.insertNth chosen context.others)) chosen.1 chosen.2
          (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using
            PqxdhLiveKemSelection.selected_index [] selected chosen context.others)
          challenge candidate agreement (next (challenge, candidate)) context.state
        rw [PqxdhDynamicKemRouter.selected_reservation] at same
        simpa only [PqxdhDynamicKemPost.evaluate, simulateQ_pure, simulateQ_map, bind_pure_comp] using congrArg
          (Functor.map (fun result => result.1.getD false)) same
      · rfl

end BeaconcryptCore.Computational.RegistrationNativeKemChallenge

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemChallenge.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemChallenge.prepare_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemChallenge.resume_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemChallenge.resume_source
