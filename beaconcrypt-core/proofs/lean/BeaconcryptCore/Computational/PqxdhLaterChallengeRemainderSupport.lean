import BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication

/-! A saved callback continuation retains its original all-reply source syntax. These support inclusions concern only logical observations of the returned value; they do not reconstruct an interpreted prefix, its cache or its probability. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport

/-- Every result of the literal saved continuation is an all-reply result of the same original program containing that dependent occurrence. -/
theorem occurrence_support {ι Result : Type} {spec : OracleSpec.{0, 0} ι}
    (query : spec.Domain) (next : spec.Range query → OracleComp spec Result)
    (client : OracleComp spec Result) (occurs : RawCtxQueryOccurrence.Occurs query next client)
    (reply : spec.Range query) : support (next reply) ⊆ support client := by
  induction client using OracleComp.inductionOn with
  | pure value => exact False.elim occurs
  | query_bind head tail ih =>
      rcases RawCtxQueryOccurrence.query_cases query head next tail occurs with same | ⟨value, inside⟩
      · rcases Sigma.mk.inj_iff.mp same with ⟨same, continuation⟩
        subst head
        cases eq_of_heq continuation
        exact fun value supported => (mem_support_bind_iff _ _ _).2 ⟨reply, mem_support_query query reply, supported⟩
      · exact fun result supported => (mem_support_bind_iff _ _ _).2
          ⟨value, mem_support_query head value, ih value inside supported⟩

/-- A completed saved callback has an output from the original callback's all-reply syntax, even when its suffix uses a different complete backend. This is not a claim about the original interpreted prefix or its probability. -/
theorem pending_support {Tag ι Result State Other : Type} {base : OracleSpec.{0, 0} ι}
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp))
    (frame : Tag → RawCtxForwardAnnotation.Frame base Result)
    (client : OracleComp (RawCtxForwardAnnotation.Spec Tag base) Result)
    (covered : RawCtxForwardCoverage.Covered privateQuery client)
    (sound : RawCtxForwardAnnotation.Sound frame client) (state reached : State) (tag : Tag)
    (supported : RawCtxForwardScan.Cut.pending tag reached ∈ support
      (RawCtxForwardScan.scan privateQuery selected selection impl client covered state))
    (afterImpl : QueryImpl base (StateT Other ProbComp)) (before : Other)
    (reply : base.Range (frame tag).1) (result : Result × Other)
    (completed : result ∈ support ((simulateQ afterImpl ((frame tag).2 reply)).run before)) :
    result.1 ∈ support (simulateQ RawCtxForwardAnnotation.erase client) := by
  apply occurrence_support (frame tag).1 (frame tag).2 _
    (RawCtxForwardScan.pending_origin privateQuery selected selection impl frame client covered sound state reached tag supported).2 reply
  apply support_simulateQ_run'_subset afterImpl ((frame tag).2 reply) before
  simpa only [StateT.run'_eq, support_map, Set.mem_image] using
    (show ∃ value ∈ support ((simulateQ afterImpl ((frame tag).2 reply)).run before), value.1 = result.1 from
      ⟨result, completed, rfl⟩)

section Source
open CoreModels Aeneas beaconcrypt_core ratchet ratchet.concrete PqxdhInitialPostContext
variable {ι M P I D K X Response Shared Origin Value Result State Other : Type}
    {extra : OracleSpec ι} {S B : Nat}

/-- The concrete saved Post callback has an original all-reply result after its complete saved continuation returns. Its prefix is the actual covered source program, and its resumed backend is retained explicitly. -/
theorem source_support (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (client : OracleComp (PostSpec extra S B) Value)
    (front : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (state reached : State)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Value Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode client front trace)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode client front trace) state))
    (afterImpl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Other ProbComp))
    (before : Other)
    (reply : (Base extra RatchetChain I D K X Response Shared S B).Range
      (PqxdhInitialOriginContext.frame mark sender route decode context).1)
    (result : (Value × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) × Other)
    (completed : result ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame mark sender route decode context).2 reply)).run before)) :
    result.1 ∈ support ((simulateQ (PqxdhInitialOriginPost.compiler (X := X) (Response := Response) mark sender route decode) client).run (front, trace)) := by
  rw [← PqxdhInitialOriginForwardPost.program_erase]
  exact pending_support PqxdhInitialOriginForwardPost.selected selected selection impl
    (PqxdhInitialOriginContext.frame mark sender route decode) _
    (PqxdhInitialOriginForwardPost.program_covered mark sender route decode client front trace)
    (PqxdhInitialOriginForwardPost.program_sound mark sender route decode client front trace)
    state reached context supported afterImpl before reply result completed

/-- The actual appended descriptor retains the complete outside program after its saved callback. Only all-reply output support is transported; the changed backend and its effects remain in the completed-run premise. -/
theorem appended_support (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (client : OracleComp (PostSpec extra S B) Value)
    (next : Value → OracleComp (PostSpec extra S B) Result)
    (front : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (state reached : State)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Value Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode client front trace)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode client front trace) state))
    (afterImpl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Other ProbComp))
    (before : Other)
    (reply : (Base extra RatchetChain I D K X Response Shared S B).Range
      (PqxdhInitialOriginContext.frame mark sender route decode (PqxdhLaterChallengeCapture.append next context)).1)
    (result : (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) × Other)
    (completed : result ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame mark sender route decode (PqxdhLaterChallengeCapture.append next context)).2 reply)).run before)) :
    result.1 ∈ support ((simulateQ (PqxdhInitialOriginPost.compiler (X := X) (Response := Response) mark sender route decode) (client >>= next)).run (front, trace)) := by
  revert reply
  rw [PqxdhLaterChallengeCapture.frame_append (X := X) (Response := Response) mark sender route decode next context]
  simp only [RawCtxForwardAnnotationComposition.appendFrame]
  intro reply completed
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at completed
  obtain ⟨middle, callback, outside⟩ := completed
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨middle.1, source_support mark sender route decode selected selection impl client front trace
    state reached context supported afterImpl before reply middle callback, ?_⟩
  apply support_simulateQ_run'_subset afterImpl _ middle.2
  simpa only [PqxdhLaterChallengeCapture.resumeOutside, StateT.run'_eq, support_map, Set.mem_image] using
    (show ∃ value ∈ support ((simulateQ afterImpl
      (PqxdhLaterChallengeCapture.resumeOutside mark sender route decode next middle.1)).run middle.2),
      value.1 = result.1 from ⟨result, outside, rfl⟩)

end Source
end BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport.occurrence_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport.occurrence_support
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport.pending_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport.pending_support
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport.source_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport.source_support
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport.appended_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderSupport.appended_support
