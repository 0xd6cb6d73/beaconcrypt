import BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport

/-! The original complete wrapper syntax preserves target-publication membership after its chosen challenge whenever its competing-publication flag remains clear. These observations apply to the literal saved remainder without reconstructing an interpreted prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication
open PqxdhInitialPostContext PqxdhRecordConfidentialityChallenge
open PqxdhFirstRecordConfidentiality (AdvSpec)
variable {ι M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
local notation "Snapshot" => NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B
local notation "sourceImpl" => PqxdhInitialOriginPost.compiler (X := X) (Response := Response) mark sender route decode

/-- On every original source reply path, only the actual returned record adds a publication with the marker installed before that callback. -/
theorem step_publication (query : (PostSpec extra S B).Domain)
    (before : Snapshot) (result : (PostSpec extra S B).Range query × Snapshot)
    (supported : result ∈ support ((sourceImpl query).run before))
    (publication : RawCtxPublishedRecords.Publication S B) :
    (publication, true) ∈ result.2.2.published ↔
      (publication, true) ∈ before.2.published ∨
      publication ∈ publications query result.1 ∧ before.2.installed publication.1 = some true := by
  rcases query with (query | query) | ⟨index, raw⟩
  all_goals simp only [PqxdhInitialOriginPost.compiler, StateT.run, bind_pure_comp, support_map] at supported
  all_goals obtain ⟨completed, _, rfl⟩ := supported
  · exact PqxdhInitialOriginPost.record_member before.2 query completed.1 publication true
  · simp only [publications, List.not_mem_nil, false_and, or_false]
  · cases tag : completed.2 <;> simp only [PqxdhInitialOriginPost.finish, tag,
      publications, List.not_mem_nil, false_and, or_false]

/-- After the chosen challenge, the complete original wrapper cannot add a target publication while its literal competing-publication flag remains clear. The statement holds on all source reply paths. -/
theorem used_program (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Result) (before : State) (ambient : Snapshot)
    (result : (Result × State) × Snapshot)
    (supported : result ∈ support ((simulateQ sourceImpl
      ((simulateQ (handler owner number bit) client).run before)).run ambient))
    (used : before.pair.isSome) (clear : result.1.2.otherTarget = false) :
    ((owner, number), true) ∈ result.2.2.published ↔
      ((owner, number), true) ∈ ambient.2.published := by
  induction client using OracleComp.inductionOn generalizing before ambient with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, actual, later⟩ := supported
      have kept : Kept step.1.2 result.1.2 := by
        apply run_kept owner number bit (next step.1.1) step.1.2 result.1
        apply support_simulateQ_run'_subset sourceImpl _ step.2
        simpa only [StateT.run'_eq, support_map, Set.mem_image] using
          (show ∃ value ∈ support ((simulateQ sourceImpl
            ((simulateQ (handler owner number bit) (next step.1.1)).run step.1.2)).run step.2),
            value.1 = result.1 from ⟨result, later, rfl⟩)
      rcases query with query | ⟨left, right⟩
      · simp only [handler, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query] at actual
        change step ∈ support (StateT.run _ ambient) at actual
        rw [StateT.run_map, support_map] at actual
        obtain ⟨reply, returned, rfl⟩ := actual
        have excluded := ((observe_target owner number before query reply.1).mp (kept.2 clear)).2
        exact (ih _ _ _ later used).trans (by
          simpa only [excluded, false_and, or_false] using
            step_publication mark sender route decode query ambient reply returned (owner, number))
      · simp only [handler, StateT.run, used, true_or, ite_true, simulateQ_pure] at actual
        change step ∈ support (pure ((none, before), ambient)) at actual
        simp only [mem_support_pure_iff] at actual
        subst step
        exact ih _ _ _ later used

/-- A true output of the unchanged complete wrapper supplies the exact clear flag needed for historical target-publication membership. -/
theorem wrapped_publication (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Bool) (before : State) (ambient : Snapshot)
    (result : Bool × Snapshot)
    (supported : result ∈ support ((simulateQ sourceImpl
      (PqxdhLaterChallengeCapture.wrapped owner number bit client before)).run ambient))
    (used : before.pair.isSome) (accepted : result.1 = true) :
    ((owner, number), true) ∈ result.2.2.published ↔
      ((owner, number), true) ∈ ambient.2.published := by
  simp only [PqxdhLaterChallengeCapture.wrapped, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨final, actual, rfl⟩ := supported
  have clear : final.1.2.otherTarget = false := by
    classical
    simp only [output, Bool.and_eq_true, decide_eq_true_eq] at accepted
    exact accepted.2.2.2
  exact used_program mark sender route decode owner number bit client before ambient final actual used clear

/-- A resumed actual capture with its unchanged full wrapper and a true output has exactly the target-publication membership already present before that captured callback, provided the wrapper had already chosen its challenge there. -/
theorem captured_publication {Local Other : Type}
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Local ProbComp))
    (ambient : Snapshot) (state reached : Local)
    (tag : PqxdhLaterChallengeCapture.Capture extra M P I D K Bool S B)
    (joined : PqxdhLaterChallengeCapture.Joined owner number bit tag)
    (supported : RawCtxForwardScan.Cut.pending tag.2.callback reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode
          ((handler owner number bit tag.2.request.query).run tag.2.request.before) ambient.1 ambient.2)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode
          ((handler owner number bit tag.2.request.query).run tag.2.request.before) ambient.1 ambient.2) state))
    (afterImpl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Other ProbComp))
    (before : Other)
    (reply : (Base extra RatchetChain I D K X Response Shared S B).Range
      (PqxdhInitialOriginContext.frame mark sender route decode tag.1).1)
    (result : (Bool × Snapshot) × Other)
    (completed : result ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame mark sender route decode tag.1).2 reply)).run before))
    (used : tag.2.request.before.pair.isSome) (accepted : result.1.1 = true) :
    ((owner, number), true) ∈ result.1.2.2.published ↔
      ((owner, number), true) ∈ ambient.2.published := by
  rcases tag with ⟨context, details⟩
  change context = PqxdhLaterChallengeCapture.append
    (fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (details.request.next reply.1) reply.2)
    details.callback at joined
  subst context
  apply wrapped_publication (X := X) (Response := Response) mark sender route decode owner number bit
    (((AdvSpec extra S B).query details.request.query : OracleComp (AdvSpec extra S B) _) >>= details.request.next)
    details.request.before ambient result.1 _ used accepted
  simpa only [PqxdhLaterChallengeCapture.wrapped, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, map_bind] using
    (PqxdhLaterChallengeRemainderSupport.appended_support mark sender route decode selected selection impl
      ((handler owner number bit details.request.query).run details.request.before)
      (fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (details.request.next reply.1) reply.2)
      ambient.1 ambient.2 state reached details.callback supported afterImpl before reply result completed)

end BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication.step_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication.step_publication
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication.used_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication.used_program
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication.wrapped_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication.wrapped_publication
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication.captured_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication.captured_publication
