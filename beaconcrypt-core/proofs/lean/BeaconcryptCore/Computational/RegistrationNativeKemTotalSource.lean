-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness
import BeaconcryptCore.Computational.RegistrationNativeKemCutStop

/-! The total real-candidate source reconstructs the entire native program. Completed cuts and unmatched getters remain in the original distribution, without an event-to-mark premise. The private reserved family and all prefix effects are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemTotalSource
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (Context State stopped expose)
open RegistrationNativeKemCut (Cut scan finish)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def finishSource (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    {count : Nat} (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (context : Context ambient KemSK Auxiliary count) : ProbComp Bool :=
  match context.cut with
  | none => pure false
  | some cut => do
      let result ← (((finish (stopped baseImpl kem other selected.val
        (List.ofFn (selected.insertNth chosen context.others))) cut).run).run context.state)
      pure (result.1.getD false)

private theorem post_finish (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    {count : Nat} (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (context : Context ambient KemSK Auxiliary count) :
    EvalDistEq (do
      let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
      RegistrationNativeKemTotalChallenge.sourcePost baseImpl kem other selected chosen
        ⟨chosen.1, pair.1, context⟩ pair.2)
      (finishSource baseImpl kem other selected chosen context) := by
  cases found : context.cut with
  | none =>
      simp only [RegistrationNativeKemTotalChallenge.sourcePost,
        RegistrationNativeKemTotalGame.continuation, found, simulateQ_pure, OptionT.run_pure,
        StateT.run_pure, pure_bind, finishSource]
      exact OracleComp.EvalDistEq.bind_const _ _
  | some cut =>
      cases cut with
      | complete value =>
          simp only [RegistrationNativeKemTotalChallenge.sourcePost,
            RegistrationNativeKemTotalGame.continuation, found, simulateQ_pure, OptionT.run_pure,
            StateT.run_pure, pure_bind, Option.getD_some, finishSource, finish]
          exact OracleComp.EvalDistEq.bind_const _ _
      | pending key next =>
          by_cases matching : key = chosen.1
          · subst key
            simp only [RegistrationNativeKemTotalChallenge.sourcePost,
              RegistrationNativeKemTotalGame.continuation, found, ite_true, finishSource, finish,
              RegistrationNativeKemGame.stopped, RegistrationNativeKemGame.combine,
              OptionT.run_bind, OptionT.run_mk]
            simp only [Option.elimM]
            rw [StateT.run_bind]
            simp only [StateT.run, bind_map_left,
              Option.elim_some, bind_assoc]
            rfl
          · simp only [RegistrationNativeKemTotalChallenge.sourcePost,
              RegistrationNativeKemTotalGame.continuation, found, matching, ite_false,
              finishSource, finish, simulateQ_bind, simulateQ_spec_query]
            exact OracleComp.EvalDistEq.bind_const _ _

private theorem after_scan (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    {count : Nat} (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (others : Fin count → MlKem768PublicKey × KemSK) (before : State Auxiliary KemSK)
    (work : OracleComp (Spec ambient KemSK) Bool) (index : Nat) :
    (do let result ← (((simulateQ (stopped baseImpl kem other selected.val
        (List.ofFn (selected.insertNth chosen others))) (expose work index)).run).run before)
        finishSource baseImpl kem other selected chosen ⟨others, result.1, result.2⟩) =
      (do let result ← (((simulateQ (stopped baseImpl kem other selected.val
        (List.ofFn (selected.insertNth chosen others))) work).run).run before)
          pure (result.1.getD false)) := by
  have execution := RegistrationNativeKemCut.scan_finish (stopped baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others))) work index
  rw [← RegistrationNativeKemCutStop.scan_simulate] at execution
  have runEq := congrArg (fun (program : OptionT (StateT (State Auxiliary KemSK) ProbComp) Bool) =>
    ((program.run).run before)) execution
  have observed := congrArg (Functor.map (fun result => result.1.getD false)) runEq
  simp only [OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind] at observed
  simp only [bind_pure_comp]
  rw [← observed]
  congr 1
  funext result
  rcases result with ⟨none | cut, after⟩
  · simp only [finishSource, Option.elim_none, StateT.run_pure,
      map_pure, Option.getD_none]
  · simp only [finishSource, Option.elim_some, bind_pure_comp]

noncomputable def source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (initial : ProbComp Auxiliary) (work : OracleComp (Spec ambient KemSK) Bool)
    (count : Nat) (selected : Fin (count + 1)) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let localState ← initial
  let result ← (((simulateQ (stopped baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others))) work).run).run
      (localState, PqxdhDynamicKemRouter.empty))
  pure (result.1.getD false)

/-- The entire real-candidate reduction source is the original reserved native program, including completed and unmatched executions. -/
theorem source_real (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (initial : ProbComp Auxiliary) (work : OracleComp (Spec ambient KemSK) Bool)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    EvalDistEq (RegistrationNativeKemTotalCorrectness.sourceReal baseImpl kem other initial work count selected index)
      (source baseImpl kem other initial work count selected) := by
  unfold RegistrationNativeKemTotalCorrectness.sourceReal source
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro chosen _generated
  simp only [RegistrationNativeKemTotalChallenge.sourcePrepare, RegistrationNativeKemChallenge.sourcePrepare,
    bind_assoc, pure_bind]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro others _sampled
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro localState _initial
  rw [← after_scan baseImpl kem other selected chosen others
    (localState, PqxdhDynamicKemRouter.empty) work index]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro prefixResult _prefix
  have removed : EvalDistEq (do
      let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
      let _ ← $ᵗ MlKemSharedSecret
      RegistrationNativeKemTotalChallenge.sourcePost baseImpl kem other selected chosen
        ⟨chosen.1, pair.1, ⟨others, prefixResult.1, prefixResult.2⟩⟩ pair.2)
      (do let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
          RegistrationNativeKemTotalChallenge.sourcePost baseImpl kem other selected chosen
            ⟨chosen.1, pair.1, ⟨others, prefixResult.1, prefixResult.2⟩⟩ pair.2) :=
    OracleComp.EvalDistEq.bind_congr_of_support _ (fun _ _ => OracleComp.EvalDistEq.bind_const _ _)
  exact removed.trans (post_finish baseImpl kem other selected chosen ⟨others, prefixResult.1, prefixResult.2⟩)

end BeaconcryptCore.Computational.RegistrationNativeKemTotalSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTotalSource.source_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTotalSource.source_real
