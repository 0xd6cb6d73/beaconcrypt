-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidatePool
import BeaconcryptCore.Computational.RegistrationNativeKemTotalSource

/-! The native KEM hybrid has a concrete source interpreter: unchanged ordinary callbacks and public encapsulations, with candidate substitution only for the created selected handle's challenge ciphertext. The full source prephase remains unrestricted. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (State Context post)
open PqxdhDynamicKemPost (evaluate)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

def source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :=
  RegistrationNativeKemGame.combine (fun work => work) other
    (fun key => simulateQ (kemAmbientImpl baseImpl) (kem.encaps key))
    (RegistrationNativeKemCandidatePool.source baseImpl kem selected pairs challenge candidate)

/-- The interpreted actual postphase callback has exactly the explicit candidate-source state and reply, without correctness or target assumptions. -/
theorem post_step (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (key : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (key, secret)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : (Spec ambient KemSK).Domain) (before : State Auxiliary KemSK) :
    evaluate baseImpl kem secret challenge
      (((post kem other selected (PqxdhDynamicKemRouter.redact selected pairs) challenge candidate query).run).run before) =
      (((source baseImpl kem other selected pairs challenge candidate query).run).run before) := by
  rcases query with query | (query | publicKey)
  · simp only [post, source, RegistrationNativeKemGame.combine, OptionT.run_mk, StateT.run,
      evaluate, simulateQ_map]
    exact congrArg (Functor.map (fun result => (some result.1, (result.2, before.2))))
      (PqxdhDynamicKemJointRouter.post_coins baseImpl kem secret challenge ((other query).run before.1))
  · simp only [post, source, RegistrationNativeKemGame.combine, OptionT.run_mk, StateT.run,
      evaluate, simulateQ_map]
    exact congrArg (Functor.map (fun result => (result.1, (before.1, result.2))))
      (RegistrationNativeKemCandidatePool.post_step baseImpl kem selected pairs key secret present challenge candidate query before.2)
  · simp only [post, source, RegistrationNativeKemGame.combine, OptionT.run_mk, StateT.run,
      evaluate, simulateQ_map]
    exact congrArg (Functor.map (fun result => (some result, before)))
      (PqxdhDynamicKemPost.ambient baseImpl kem secret challenge (kem.encaps publicKey))

/-- Arbitrary native postphase programs retain their complete optional result, local state, indexed history and stop reasons under the explicit source. -/
theorem post_program (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (key : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (key, secret)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    evaluate baseImpl kem secret challenge
      (((simulateQ (post kem other selected (PqxdhDynamicKemRouter.redact selected pairs) challenge candidate) work).run).run before) =
      (((simulateQ (source baseImpl kem other selected pairs challenge candidate) work).run).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
      unfold evaluate
      simp only [simulateQ_bind]
      rw [show simulateQ (kemAmbientImpl baseImpl)
        (simulateQ (kem.IND_CCA_postChallengeImpl secret challenge)
          (((post kem other selected (PqxdhDynamicKemRouter.redact selected pairs) challenge candidate query).run).run before)) = _ from
            post_step baseImpl kem other selected pairs key secret present challenge candidate query before]
      apply bind_congr
      rintro ⟨none | answer, after⟩
      · rfl
      · exact ih answer after

noncomputable def total (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let context ← RegistrationNativeKemTotalChallenge.sourcePrepare baseImpl kem other initial work count selected index chosen
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  let result ← (((simulateQ (source baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen context.others)) pair.1 candidate)
    (RegistrationNativeKemTotalGame.continuation chosen.1 pair.1 candidate context.cut)).run).run context.state)
  pure (result.1.getD false)

/-- Both total ordinary CCA branches have the explicit native candidate-source semantics, including inactive dummy-ciphertext substitutions and unrestricted prechallenge decapsulation. -/
theorem total_branch (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    RegistrationNativeKemTotalGame.branch baseImpl kem other initial work count selected index real =
      total baseImpl kem other initial work count selected index real := by
  rw [RegistrationNativeKemTotalCorrectness.branch_source]
  unfold RegistrationNativeKemTotalCorrectness.branch total
  apply bind_congr
  intro chosen
  apply bind_congr
  intro context
  apply bind_congr
  intro pair
  apply bind_congr
  intro uniform
  have same := post_program baseImpl kem other selected.val (List.ofFn (selected.insertNth chosen context.others))
    chosen.1 chosen.2
    (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using
      PqxdhLiveKemSelection.selected_index [] selected chosen context.others)
    pair.1 (if real then pair.2 else uniform)
    (RegistrationNativeKemTotalGame.continuation chosen.1 pair.1 (if real then pair.2 else uniform) context.cut) context.state
  rw [PqxdhDynamicKemRouter.selected_reservation] at same
  simpa only [RegistrationNativeKemTotalGame.resume, evaluate, simulateQ_pure,
    simulateQ_map, bind_pure_comp] using congrArg (Functor.map (fun result => result.1.getD false)) same

end BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource.post_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource.post_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource.post_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource.post_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource.total_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource.total_branch
