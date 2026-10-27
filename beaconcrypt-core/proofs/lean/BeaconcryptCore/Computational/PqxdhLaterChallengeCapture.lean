import BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource

/-! Carry the actual wrapper state and continuation while constructing the existing saved source descriptors. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeCapture
open PqxdhInitialPostContext PqxdhInitialOriginForwardPost RawCtxForwardAnnotation
variable {ι M P I D K X Response Shared Origin Value Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Append the actual outside program to the explicitly carried descriptor, without recovering or comparing any saved function. -/
noncomputable def append (next : Value → OracleComp (PostSpec extra S B) Result)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Value Origin S B) :
    PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B :=
  ⟨match context.original with
    | .inl (.record request before outside inner) =>
        .inl (.record request before (fun reply => outside reply >>= next) inner)
    | .inl (.finish index before control candidate outside inner) =>
        .inl (.finish index before control candidate (fun reply => outside reply >>= next) inner)
    | .inr builder => .inr { builder with outside := fun reply => builder.outside reply >>= next },
    context.trace, context.origin⟩

/-- A source continuation is appended with the exact current frontend and installation trace. -/
noncomputable def resumeOutside (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (next : Value → OracleComp (PostSpec extra S B) Result)
    (result : Value × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :
    OracleComp (Base extra RatchetChain I D K X Response Shared S B)
      (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :=
  (simulateQ (PqxdhInitialOriginPost.compiler mark sender route read) (next result.1)).run result.2

/-- Appending a descriptor retains the literal pending request and the complete source continuation. -/
theorem frame_append (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (next : Value → OracleComp (PostSpec extra S B) Result)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Value Origin S B) :
    PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route read (append next context) =
      RawCtxForwardAnnotationComposition.appendFrame (resumeOutside mark sender route read next)
        (PqxdhInitialOriginContext.frame mark sender route read context) := by
  rcases context with ⟨original, trace, origin⟩
  rcases original with (⟨request, before, outside, inner⟩ | ⟨index, before, control, candidate, outside, inner⟩) | builder
  all_goals simp only [append, PqxdhInitialOriginContext.frame, PqxdhInitialOriginContext.resume,
    PqxdhInitialOriginContext.complete, RawCtxForwardAnnotationComposition.appendFrame,
    simulateQ_bind, StateT.run_bind, bind_assoc]
  all_goals rfl

private theorem map_plain {α : Type}
    (changeTag : PqxdhInitialOriginContext.Context extra M P I D K Value Origin S B →
      PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) α) :
    simulateQ (fun query => (liftM ((Spec extra M P I D K X Response Shared Result Origin S B).query
      (query.1.map changeTag, query.2)) : OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) _)) (simulateQ plain client) = simulateQ plain client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, plain, Option.map_none]
    exact bind_congr ih

private theorem map_lift {Tag Middle Last κ ν α : Type} {base : OracleSpec κ} {more : OracleSpec ν}
    (first : Tag → Middle) (second : Middle → Last)
    (client : OracleComp (RawCtxForwardAnnotation.Spec Tag base) α) :
    simulateQ (fun query => (liftM ((RawCtxForwardAnnotation.Spec Last (base + more)).query
      (query.1.map second, query.2)) : OracleComp (RawCtxForwardAnnotation.Spec Last (base + more)) _))
      (RawCtxForwardAnnotationLift.lift first client) =
      RawCtxForwardAnnotationLift.lift (second ∘ first) client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [RawCtxForwardAnnotationLift.lift, RawCtxForwardAnnotationLift.adapter,
      simulateQ_bind, simulateQ_spec_query]
    rcases query with ⟨_ | tag, query⟩ <;> exact bind_congr ih

/-- Splicing the actual remaining source program into each carried descriptor is the same annotated source program, not merely the same returned value. -/
theorem program_append (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp (PostSpec extra S B) Value) (next : Value → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    (do let result ← mapTags (append next)
          (program (X := X) (Response := Response) mark sender route read work before trace)
        program mark sender route read (next result.1) result.2.1 result.2.2) =
      program mark sender route read (work >>= next) before trace := by
  induction work using OracleComp.inductionOn generalizing before trace with
  | pure value => rfl
  | query_bind query outside ih =>
    simp only [bind_assoc, program_query]
    rcases query with (request | request) | ⟨index, raw⟩
    all_goals dsimp only
    case query_bind.inr =>
      unfold PqxdhInitialOriginForwardPost.finish
      cases phase : (before.roles.1.2 index).beacon.phase
      case initSent control prekey oneTime kem =>
        simp only [mapTags, simulateQ_bind, bind_assoc, QueryImpl.simulateQ_compose]
        rw [map_plain]
        refine bind_congr fun prepared => ?_
        cases prepared with
        | none => exact ih _ _ _
        | some prepared =>
          simp only [simulateQ_bind, map_plain, bind_assoc]
          refine bind_congr fun kernel => ?_
          cases kernel with
          | none => exact ih _ _ _
          | some kernel =>
            simp only [simulateQ_bind, map_plain, bind_assoc]
            refine bind_congr fun application => ?_
            cases application with
            | none => exact ih _ _ _
            | some application =>
              simp only [simulateQ_bind, ownerLift, map_lift, bind_assoc]
              exact bind_congr fun result => ih _ _ _
      all_goals exact ih _ _ _
    case query_bind.inl.inl =>
      simp only [record, mapTags, simulateQ_bind, map_lift, bind_assoc]
      exact bind_congr fun result => ih _ _ _
    case query_bind.inl.inr =>
      simp only [mapTags, simulateQ_bind, map_plain, bind_assoc]
      exact bind_congr fun reply => ih reply before trace

/-- Values generated at an actual wrapper callback, before its source execution. The reply-dependent continuation is carried directly. -/
structure Request (extra : OracleSpec ι) (S B : Nat) where
  query : (PqxdhFirstRecordConfidentiality.AdvSpec extra S B).Domain
  before : PqxdhRecordConfidentialityChallenge.State
  next : (PqxdhFirstRecordConfidentiality.AdvSpec extra S B).Range query →
    OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool

/-- Retain the descriptor generated inside this very callback, before its outside continuation is extended. No function is recovered from the extended descriptor. -/
structure Details (extra : OracleSpec ι) (M P I D K Origin : Type) (S B : Nat) where
  request : Request extra S B
  callback : PqxdhInitialOriginContext.Context extra M P I D K
    ((PqxdhFirstRecordConfidentiality.AdvSpec extra S B).Range request.query × PqxdhRecordConfidentialityChallenge.State) Origin S B

abbrev Capture (extra : OracleSpec ι) (M P I D K Origin : Type) (S B : Nat) :=
  PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B × Details extra M P I D K Origin S B

/-- The literal existing public wrapper, from its actual current state. -/
noncomputable def wrapped (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (current : PqxdhRecordConfidentialityChallenge.State) : OracleComp (PostSpec extra S B) Bool :=
  PqxdhRecordConfidentialityChallenge.output number <$>
    (simulateQ (PqxdhRecordConfidentialityChallenge.handler owner number bit) work).run current

/-- Construct richer descriptors with the existing complete source compiler for each actual wrapper callback. No source call, reply or branch is changed. -/
noncomputable def captured (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool) :
    PqxdhRecordConfidentialityChallenge.State → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
    OracleComp (RawCtxForwardAnnotation.Spec (Capture extra M P I D K Origin S B)
      (Base extra RatchetChain I D K X Response Shared S B))
      (Bool × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :=
  OracleComp.recOn work
    (fun result current before trace => pure (PqxdhRecordConfidentialityChallenge.output number (result, current), (before, trace)))
    (fun query next recurse current before trace => do
      let result ← mapTags
        (fun context => (append (fun reply => wrapped owner number bit (next reply.1) reply.2) context,
          (⟨⟨query, current, next⟩, context⟩ : Details extra M P I D K Origin S B)))
        (program mark sender route read
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current) before trace)
      recurse result.1.1 result.1.2 result.2.1 result.2.2)

theorem tags_bind {Tag Other κ α β : Type} {base : OracleSpec κ}
    (changeTag : Tag → Other) (work : OracleComp (RawCtxForwardAnnotation.Spec Tag base) α)
    (next : α → OracleComp (RawCtxForwardAnnotation.Spec Tag base) β) :
    mapTags changeTag (work >>= next) = mapTags changeTag work >>= fun value => mapTags changeTag (next value) :=
  simulateQ_bind _ _ _

theorem tags_compose {Tag Middle Last κ α : Type} {base : OracleSpec κ}
    (first : Tag → Middle) (second : Middle → Last) (work : OracleComp (RawCtxForwardAnnotation.Spec Tag base) α) :
    mapTags second (mapTags first work) = mapTags (second ∘ first) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [mapTags, simulateQ_bind, simulateQ_spec_query]
    rcases query with ⟨_ | tag, query⟩ <;> exact bind_congr ih

/-- Removing only the generated wrapper capture restores every original descriptor and the complete original query tree. -/
theorem captured_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    mapTags Prod.fst (captured (X := X) (Response := Response) mark sender route read owner number bit work current before trace) =
      program mark sender route read (wrapped owner number bit work current) before trace := by
  induction work using OracleComp.inductionOn generalizing current before trace with
  | pure value => rfl
  | query_bind query next ih =>
    change mapTags Prod.fst (do
      let result ← mapTags
        (fun context => (append (fun reply : (PqxdhFirstRecordConfidentiality.AdvSpec extra S B).Range query × PqxdhRecordConfidentialityChallenge.State => wrapped owner number bit (next reply.1) reply.2) context,
          (⟨⟨query, current, next⟩, context⟩ : Details extra M P I D K Origin S B)))
        (program mark sender route read
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current) before trace)
      captured mark sender route read owner number bit (next result.1.1) result.1.2 result.2.1 result.2.2) = _
    rw [tags_bind, tags_compose]
    simp only [ih]
    change (do
      let result ← mapTags (append (fun reply : (PqxdhFirstRecordConfidentiality.AdvSpec extra S B).Range query × PqxdhRecordConfidentialityChallenge.State => wrapped owner number bit (next reply.1) reply.2))
        (program mark sender route read
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current) before trace)
      program mark sender route read (wrapped owner number bit (next result.1.1) result.1.2) result.2.1 result.2.2) = _
    rw [program_append mark sender route read
      ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current)
      (fun reply : (PqxdhFirstRecordConfidentiality.AdvSpec extra S B).Range query × PqxdhRecordConfidentialityChallenge.State => wrapped owner number bit (next reply.1) reply.2) before trace]
    simp only [wrapped, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]

/-- Changing only carried descriptor data preserves all-reply coverage of exactly the same private requests. -/
theorem covered_tags {Tag Other κ α : Type} {base : OracleSpec κ}
    (changeTag : Tag → Other) (selected : base.Domain → Bool)
    (work : OracleComp (RawCtxForwardAnnotation.Spec Tag base) α) :
    RawCtxForwardCoverage.Covered selected (mapTags changeTag work) ↔ RawCtxForwardCoverage.Covered selected work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    change ((query.1.map changeTag).isSome = selected query.2 ∧
      ∀ reply, RawCtxForwardCoverage.Covered selected (mapTags changeTag (next reply))) ↔ _
    simp only [Option.isSome_map, ih]
    rfl

/-- The actual captured source has a descriptor at every selected primitive request under every oracle reply. No supported-result test is used by its scanner. -/
theorem captured_covered (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    RawCtxForwardCoverage.Covered selected
      (captured (X := X) (Response := Response) mark sender route read owner number bit work current before trace) := by
  rw [← covered_tags Prod.fst, captured_erase]
  exact program_covered mark sender route read _ before trace

/-- Project carried metadata only; complete decisions and the full scanner state remain literal. -/
def cutMap {Tag Other α Local : Type} (changeTag : Tag → Other) :
    RawCtxForwardScan.Cut Tag α Local → RawCtxForwardScan.Cut Other α Local
  | .complete value state => .complete value state
  | .pending tag state => .pending (changeTag tag) state

/-- The shared-ROM scanner commutes with metadata projection through the complete source query tree. -/
theorem scan_tags {Tag Other κ α Local : Type} {base : OracleSpec κ}
    (changeTag : Tag → Other) (privateQuery : base.Domain → Bool)
    (chosen : base.Domain → Local → Bool)
    (selection : ∀ query state, chosen query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT Local (OracleComp AdaptiveCtxSharedHash.HashSpec)))
    (work : OracleComp (RawCtxForwardAnnotation.Spec Tag base) α)
    (covered : RawCtxForwardCoverage.Covered privateQuery work) (state : Local) :
    cutMap changeTag <$> RawCtxSharedPrefixScan.scan privateQuery chosen selection impl work covered state =
      RawCtxSharedPrefixScan.scan privateQuery chosen selection impl (mapTags changeTag work)
        ((covered_tags changeTag privateQuery work).mpr covered) state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    change cutMap changeTag <$> (if selected : chosen query.2 state = true then _ else _) =
      (if selected : chosen query.2 state = true then _ else _)
    split <;> simp only [*, map_pure, map_bind]
    · change pure (RawCtxForwardScan.Cut.pending (Result := α) (changeTag (query.1.get _)) state) =
        (pure (RawCtxForwardScan.Cut.pending ((query.1.map changeTag).get _) state) : OracleComp AdaptiveCtxSharedHash.HashSpec _)
      exact congrArg (fun tag => pure (RawCtxForwardScan.Cut.pending tag state)) Option.get_map.symm
    · exact bind_congr fun result => ih result.1 (covered.2 result.1) result.2

/-- The original full-state scanner commutes with metadata projection through the complete source query tree. -/
theorem native_scan_tags {Tag Other κ α Local : Type} {base : OracleSpec κ}
    (changeTag : Tag → Other) (privateQuery : base.Domain → Bool)
    (chosen : base.Domain → Local → Bool)
    (selection : ∀ query state, chosen query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT Local ProbComp))
    (work : OracleComp (RawCtxForwardAnnotation.Spec Tag base) α)
    (covered : RawCtxForwardCoverage.Covered privateQuery work) (state : Local) :
    cutMap changeTag <$> RawCtxForwardScan.scan privateQuery chosen selection impl work covered state =
      RawCtxForwardScan.scan privateQuery chosen selection impl (mapTags changeTag work)
        ((covered_tags changeTag privateQuery work).mpr covered) state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    change cutMap changeTag <$> (if selected : chosen query.2 state = true then _ else _) =
      (if selected : chosen query.2 state = true then _ else _)
    split <;> simp only [*, map_pure, map_bind]
    · change pure (RawCtxForwardScan.Cut.pending (Result := α) (changeTag (query.1.get _)) state) =
        (pure (RawCtxForwardScan.Cut.pending ((query.1.map changeTag).get _) state) : ProbComp _)
      exact congrArg (fun tag => pure (RawCtxForwardScan.Cut.pending tag state)) Option.get_map.symm
    · exact bind_congr fun result => ih result.1 (covered.2 result.1) result.2

/-- The actual captured wrapper gives exactly the original carried cut after metadata projection, including completed decisions and every reached local state. -/
theorem captured_scan {Local : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, chosen query state = true → selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B)
      (StateT Local (OracleComp AdaptiveCtxSharedHash.HashSpec))) (state : Local) :
    cutMap Prod.fst <$> RawCtxSharedPrefixScan.scan selected chosen selection impl
      (captured mark sender route read owner number bit work current before trace)
      (captured_covered mark sender route read owner number bit work current before trace) state =
      RawCtxSharedPrefixScan.scan selected chosen selection impl
        (program mark sender route read (wrapped owner number bit work current) before trace)
        (program_covered mark sender route read _ before trace) state := by
  rw [scan_tags]
  simp only [captured_erase]

/-- The retained callback-local descriptor and actual wrapper continuation produce the original saved descriptor by literal composition. -/
noncomputable def Joined (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (tag : Capture extra M P I D K Origin S B) : Prop :=
  tag.1 = append (fun reply => wrapped owner number bit (tag.2.request.next reply.1) reply.2) tag.2.callback

theorem all_true {Tag κ α : Type} {base : OracleSpec κ}
    (work : OracleComp (RawCtxForwardAnnotation.Spec Tag base) α) :
    RawCtxForwardTags.All (fun _ => True) work := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨fun _ _ => trivial, ih⟩

/-- Each generated capture contains its original callback descriptor and complete actual wrapper remainder; this is checked over every source reply, before any scan. -/
theorem captured_joined (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    RawCtxForwardTags.All (Joined owner number bit)
      (captured (X := X) (Response := Response) mark sender route read owner number bit work current before trace) := by
  induction work using OracleComp.inductionOn generalizing current before trace with
  | pure value => trivial
  | query_bind query next ih =>
    change RawCtxForwardTags.All _ (_ >>= _)
    refine RawCtxForwardTags.bind_all _ _ _ ?_ (fun result => ih _ _ _ _)
    refine RawCtxForwardTags.map_all (fun _ => True) (Joined owner number bit) _ ?_ _ (all_true _)
    intro context _
    rfl

/-- Every returned shared-ROM descriptor retains its syntactic certificate, independently of the particular replies supplied to earlier original callbacks. -/
theorem shared_scan_all {Tag κ α Local : Type} {base : OracleSpec κ}
    (privateQuery : base.Domain → Bool) (chosen : base.Domain → Local → Bool)
    (selection : ∀ query state, chosen query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT Local (OracleComp AdaptiveCtxSharedHash.HashSpec)))
    (predicate : Tag → Prop) (work : OracleComp (RawCtxForwardAnnotation.Spec Tag base) α)
    (covered : RawCtxForwardCoverage.Covered privateQuery work) (valid : RawCtxForwardTags.All predicate work)
    (state reached : Local) (tag : Tag)
    (supported : RawCtxForwardScan.Cut.pending tag reached ∈ support
      (RawCtxSharedPrefixScan.scan privateQuery chosen selection impl work covered state)) : predicate tag := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [RawCtxSharedPrefixScan.scan] at supported
    cases supported
  | query_bind query next ih =>
    change RawCtxForwardScan.Cut.pending tag reached ∈ support
      (if selected : chosen query.2 state = true then _ else _) at supported
    split at supported
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact valid.1 _ (Option.some_get _).symm
    · simp only [support_bind, Set.mem_iUnion] at supported
      obtain ⟨answer, _answered, later⟩ := supported
      exact ih answer.1 (covered.2 answer.1) (valid.2 answer.1) answer.2 later

end BeaconcryptCore.Computational.PqxdhLaterChallengeCapture

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.frame_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.frame_append
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.program_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.program_append
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.tags_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.tags_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.tags_compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.tags_compose
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.captured_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.captured_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.covered_tags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.covered_tags
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.captured_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.captured_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.scan_tags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.scan_tags
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.native_scan_tags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.native_scan_tags
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.captured_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.captured_scan
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.all_true' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.all_true
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.captured_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.captured_joined
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.shared_scan_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapture.shared_scan_all
