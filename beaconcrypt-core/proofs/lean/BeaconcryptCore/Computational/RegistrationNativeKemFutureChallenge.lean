-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemFutureGame
import BeaconcryptCore.Computational.RegistrationNativeKemChallenge

/-! The reserved-future-key cut retains the exact actual stopped native prephase and complete continuation. The private router still gates access by actual creation. Real-candidate source agreement charges ordinary decapsulation correctness, while final target activation does not silently require an earlier owner birth. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemFutureChallenge
open PqxdhKemIndCca
open RegistrationNativeKemGame (Context stopped)
open RegistrationNativeKemFutureGame (active resume)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable abbrev sourcePrepare := @RegistrationNativeKemChallenge.sourcePrepare

noncomputable def sourcePost (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    {count : Nat} (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (transcript : MlKemChallengeTranscript (Context ambient KemSK Auxiliary count)) (candidate : MlKemSharedSecret) :
    ProbComp Bool :=
  match transcript.context.cut with
  | none => pure false
  | some (.complete _) => pure false
  | some (.pending key next) =>
      if active transcript.publicKey key then do
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

end BeaconcryptCore.Computational.RegistrationNativeKemFutureChallenge

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFutureChallenge.resume_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFutureChallenge.resume_source
