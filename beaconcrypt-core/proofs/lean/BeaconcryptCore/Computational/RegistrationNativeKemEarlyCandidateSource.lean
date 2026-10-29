-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyBudget
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource

/-! The early CCA branch is the explicit actual indexed candidate source for the entire protocol, not only for a suffix after its first getter. This equality keeps all optional failures, birth checks, exact-ciphertext substitutions and private source states. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemEarlyCandidateSource
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let context ← RegistrationNativeKemTotalChallenge.sourcePrepare baseImpl kem other initial (pure false) count selected 0 chosen
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  let result ← (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen context.others)) pair.1 candidate)
    (RegistrationNativeKemEarlyGame.intercept chosen.1 pair.1 candidate work)).run).run context.state)
  pure (result.1.getD false)

/-- Both complete early ordinary-CCA branches have the actual explicit candidate source semantics from the start, without a correctness or activity premise. -/
theorem branch_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (real : Bool) :
    RegistrationNativeKemEarlyGame.branch baseImpl kem other initial work count selected real =
      source baseImpl kem other initial work count selected real := by
  rw [RegistrationNativeKemEarlyCorrectness.branch_source]
  unfold RegistrationNativeKemEarlyCorrectness.branch source
  apply bind_congr
  intro chosen
  apply bind_congr
  intro context
  apply bind_congr
  intro pair
  apply bind_congr
  intro uniform
  have same := RegistrationNativeKemCandidateSource.post_program baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen context.others)) chosen.1 chosen.2
    (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using
      PqxdhLiveKemSelection.selected_index [] selected chosen context.others)
    pair.1 (if real then pair.2 else uniform)
    (RegistrationNativeKemEarlyGame.intercept chosen.1 pair.1 (if real then pair.2 else uniform) work) context.state
  rw [PqxdhDynamicKemRouter.selected_reservation] at same
  simpa only [RegistrationNativeKemEarlyGame.resume, PqxdhDynamicKemPost.evaluate,
    simulateQ_map, simulateQ_pure, bind_pure_comp] using congrArg (Functor.map (fun result => result.1.getD false)) same

end BeaconcryptCore.Computational.RegistrationNativeKemEarlyCandidateSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyCandidateSource.branch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyCandidateSource.branch_source
