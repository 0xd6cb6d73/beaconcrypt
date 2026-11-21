-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemTotalGame
import BeaconcryptCore.Computational.RegistrationNativeKemChallenge

/-! Correctness connects the total indexed post service to the complete actual source continuation, including unmatched-key work and every repeated selected-handle decapsulation. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemTotalChallenge
open PqxdhKemIndCca
open RegistrationNativeKemGame (Context stopped)
open RegistrationNativeKemTotalGame (continuation resume)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable abbrev sourcePrepare := @RegistrationNativeKemChallenge.sourcePrepare

noncomputable def sourcePost (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    {count : Nat} (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (transcript : MlKemChallengeTranscript (Context ambient KemSK Auxiliary count)) (candidate : MlKemSharedSecret) :
    ProbComp Bool := do
  let result ← (((simulateQ (stopped baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen transcript.context.others)))
    (continuation transcript.publicKey transcript.ciphertext candidate transcript.context.cut)).run).run transcript.context.state)
  pure (result.1.getD false)

/-- One actual correctness fact recovers the entire real postphase, without discarding completed or unmatched branches. -/
theorem resume_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    {count : Nat} (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (context : Context ambient KemSK Auxiliary count) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (agreement : kem.decaps chosen.2 challenge = pure (some candidate)) :
    PqxdhDynamicKemPost.evaluate baseImpl kem chosen.2 challenge
      (resume kem other selected ⟨chosen.1, challenge, context⟩ candidate) =
      sourcePost baseImpl kem other selected chosen ⟨chosen.1, challenge, context⟩ candidate := by
  have same := RegistrationNativeKemSource.post_program baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen context.others)) chosen.1 chosen.2
    (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using
      PqxdhLiveKemSelection.selected_index [] selected chosen context.others)
    challenge candidate agreement (continuation chosen.1 challenge candidate context.cut) context.state
  rw [PqxdhDynamicKemRouter.selected_reservation] at same
  simpa only [resume, sourcePost, PqxdhDynamicKemPost.evaluate, simulateQ_pure,
    simulateQ_map, bind_pure_comp] using congrArg (Functor.map (fun result => result.1.getD false)) same

end BeaconcryptCore.Computational.RegistrationNativeKemTotalChallenge

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTotalChallenge.resume_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTotalChallenge.resume_source
