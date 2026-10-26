import BeaconcryptCore.Computational.PqxdhLaterChallengeSampler

/-! Classify the actual captured source cut using its executed callback prefix. Syntactic composition alone supplies no challenge chronology or input-log fact. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology
open RawCtxForwardAnnotation RawCtxForwardCoverage RawCtxForwardScan

/-- Sequential scanning either retains a cut in the actual first callback or continues with that callback's complete returned value and state. -/
theorem native_bind {Tag ι Value Result State : Type} {base : OracleSpec ι}
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp))
    (work : OracleComp (Spec Tag base) Value) (next : Value → OracleComp (Spec Tag base) Result)
    (covered : Covered privateQuery work) (following : ∀ value, Covered privateQuery (next value))
    (combined : Covered privateQuery (work >>= next)) (state : State) :
    scan privateQuery selected selection impl (work >>= next) combined state =
      (do
        let cut ← scan privateQuery selected selection impl work covered state
        match cut with
        | .complete value current => scan privateQuery selected selection impl (next value) (following value) current
        | .pending tag current => pure (.pending tag current)) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query tail ih =>
      simp only [bind_assoc] at combined ⊢
      cases chosen : selected query.2 state with
      | true =>
          rw [scan_cut privateQuery selected selection impl query _ _ state chosen,
            scan_cut privateQuery selected selection impl query tail covered state chosen]
          rfl
      | false =>
          rw [scan_other privateQuery selected selection impl query _ _ state chosen,
            scan_other privateQuery selected selection impl query tail covered state chosen]
          simp only [bind_assoc]
          exact bind_congr fun reply => ih reply.1 (covered.2 reply.1) (combined.2 reply.1) reply.2

/-- A completed scanned callback has actually executed the same full erased callback, with its exact returned value and backend state. -/
theorem native_complete {Tag ι Value State : Type} {base : OracleSpec ι}
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp))
    (work : OracleComp (Spec Tag base) Value) (covered : Covered privateQuery work)
    (state reached : State) (value : Value)
    (supported : Cut.complete value reached ∈ support (scan privateQuery selected selection impl work covered state)) :
    (value, reached) ∈ support ((simulateQ impl (simulateQ erase work)).run state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [scan_pure, mem_support_pure_iff] at supported
      cases supported
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff]
  | query_bind query next ih =>
      cases chosen : selected query.2 state with
      | true =>
          rw [scan_cut privateQuery selected selection impl query next covered state chosen, mem_support_pure_iff] at supported
          cases supported
      | false =>
          rw [scan_other privateQuery selected selection impl query next covered state chosen, mem_support_bind_iff] at supported
          obtain ⟨reply, actual, later⟩ := supported
          simp only [simulateQ_bind, simulateQ_spec_query, erase, StateT.run_bind, mem_support_bind_iff]
          exact ⟨reply, actual, ih reply.1 (covered.2 reply.1) reply.2 later⟩

/-- A supported pending cut is inside the current callback or after an actual complete callback execution, with its full returned state retained. -/
theorem native_pending_cases {Tag ι Value Result State : Type} {base : OracleSpec ι}
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp))
    (work : OracleComp (Spec Tag base) Value) (next : Value → OracleComp (Spec Tag base) Result)
    (covered : Covered privateQuery work) (following : ∀ value, Covered privateQuery (next value))
    (combined : Covered privateQuery (work >>= next)) (state reached : State) (tag : Tag)
    (supported : Cut.pending tag reached ∈ support (scan privateQuery selected selection impl (work >>= next) combined state)) :
    (Cut.pending tag reached ∈ support (scan privateQuery selected selection impl work covered state)) ∨
      ∃ value current,
        (value, current) ∈ support ((simulateQ impl (simulateQ erase work)).run state) ∧
        Cut.pending tag reached ∈ support (scan privateQuery selected selection impl (next value) (following value) current) := by
  rw [native_bind privateQuery selected selection impl work next covered following combined state, mem_support_bind_iff] at supported
  obtain ⟨cut, earlier, later⟩ := supported
  cases cut with
  | complete value current =>
      exact Or.inr ⟨value, current, native_complete privateQuery selected selection impl work covered state current value earlier, later⟩
  | pending actual current =>
      simp only [mem_support_pure_iff] at later
      cases later
      exact Or.inl earlier

/-- Mapping a callback descriptor keeps its actual supported cut and state; the returned metadata comes from that exact original descriptor. -/
theorem native_pending_map {Tag Other ι Value State : Type} {base : OracleSpec ι}
    (changeTag : Tag → Other)
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp))
    (work : OracleComp (Spec Tag base) Value) (covered : Covered privateQuery work)
    (state reached : State) (tag : Other)
    (supported : Cut.pending tag reached ∈ support (scan privateQuery selected selection impl (mapTags changeTag work)
      ((PqxdhLaterChallengeCapture.covered_tags changeTag privateQuery work).mpr covered) state)) :
    ∃ original, changeTag original = tag ∧
      Cut.pending original reached ∈ support (scan privateQuery selected selection impl work covered state) := by
  rw [← PqxdhLaterChallengeCapture.native_scan_tags changeTag privateQuery selected selection impl work covered state, support_map] at supported
  obtain ⟨cut, earlier, same⟩ := supported
  cases cut with
  | complete value current => cases same
  | pending original current =>
      simp only [PqxdhLaterChallengeCapture.cutMap, Cut.pending.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨original, rfl, earlier⟩

section Source
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open PqxdhInitialPostContext PqxdhInitialOriginForwardPost
variable {ι M P I D K X Response Shared Origin Local Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Local ProbComp))

abbrev FullState := (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B) × Local

/-- Reassociate the existing original Post compiler and its complete callback interpreter. This forwards exactly the old public requests, with no new scheduler or state gate. -/
noncomputable def postImpl : QueryImpl (PostSpec extra S B)
    (StateT (FullState (M := M) (P := P) (I := I) (D := D) (K := K) (Origin := Origin) (Local := Local) (S := S) (B := B)) ProbComp) :=
  fun query before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((simulateQ impl ((PqxdhInitialOriginPost.compiler mark sender route read query).run before.1)).run before.2)

/-- Complete adaptive Post interpretation preserves the exact frontend, origin trace and backend state under reassociation. -/
theorem post_program (work : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B) (state : Local) :
    (simulateQ (postImpl mark sender route read impl) work).run (before, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((simulateQ impl ((simulateQ (PqxdhInitialOriginPost.compiler mark sender route read) work).run before)).run state) := by
  induction work using OracleComp.inductionOn generalizing before state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp only [postImpl, StateT.run, bind_map_left]
      exact bind_congr fun reply => ih reply.1.1 reply.1.2 reply.2

/-- A wrapper capture comes from the actual reached adversary request and its callback-local cut, with the complete original frontend/trace/backend prefix retained. -/
theorem captured_reaches
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, chosen query state = true → PqxdhInitialForwardPost.selected query = true)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (current : PqxdhRecordConfidentialityChallenge.State)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (state reached : Local)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (supported : Cut.pending (context, details) reached ∈ support
      (scan PqxdhInitialForwardPost.selected chosen selection impl
        (PqxdhLaterChallengeCapture.captured mark sender route read owner number bit work current before trace)
        (PqxdhLaterChallengeCapture.captured_covered mark sender route read owner number bit work current before trace) state)) :
    ∃ front history ambient,
      PqxdhRecordConfidentialityTrace.Reaches (postImpl mark sender route read impl) owner number bit
        work current ((before, trace), state)
        ((PqxdhFirstRecordConfidentiality.AdvSpec extra S B).query details.request.query >>= details.request.next)
        details.request.before ((front, history), ambient) ∧
      Cut.pending details.callback reached ∈ support
        (scan PqxdhInitialForwardPost.selected chosen selection impl
          (program mark sender route read ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history)
          (program_covered mark sender route read ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history) ambient) := by
  induction work using OracleComp.inductionOn generalizing current before trace state with
  | pure value =>
      simp only [PqxdhLaterChallengeCapture.captured] at supported
      cases supported
  | query_bind query next ih =>
      let liftTag := fun callback : PqxdhInitialOriginContext.Context extra M P I D K
          ((PqxdhFirstRecordConfidentiality.AdvSpec extra S B).Range query × PqxdhRecordConfidentialityChallenge.State) Origin S B =>
        (PqxdhLaterChallengeCapture.append
          (fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (next reply.1) reply.2) callback,
          (⟨⟨query, current, next⟩, callback⟩ : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B))
      have headCovered := (PqxdhLaterChallengeCapture.covered_tags liftTag PqxdhInitialForwardPost.selected
        (program (X := X) (Response := Response) mark sender route read
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current) before trace)).mpr
        (program_covered mark sender route read ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current) before trace)
      rcases native_pending_cases PqxdhInitialForwardPost.selected chosen selection impl _ _ headCovered
        (fun value => PqxdhLaterChallengeCapture.captured_covered mark sender route read owner number bit
          (next value.1.1) value.1.2 value.2.1 value.2.2)
        (PqxdhLaterChallengeCapture.captured_covered mark sender route read owner number bit
          (((PqxdhFirstRecordConfidentiality.AdvSpec extra S B).query query : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) _) >>= next) current before trace)
        state reached (context, details) supported with inside | later
      · obtain ⟨callback, same, pending⟩ := native_pending_map liftTag PqxdhInitialForwardPost.selected chosen selection impl
          (program mark sender route read ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current) before trace)
          (program_covered mark sender route read ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current) before trace)
          state reached (context, details) inside
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        exact ⟨before, trace, state, .here _ _ _, pending⟩
      · obtain ⟨value, backend, actual, remaining⟩ := later
        obtain ⟨front, history, ambient, reachedRequest, pending⟩ := ih value.1.1 value.1.2 value.2.1 value.2.2 backend remaining
        rw [erase_mapTags, program_erase] at actual
        have step : (value.1, (value.2, backend)) ∈ support
            ((simulateQ (postImpl mark sender route read impl)
              ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current)).run ((before, trace), state)) := by
          rw [post_program, support_map]
          exact ⟨(value, backend), actual, rfl⟩
        exact ⟨front, history, ambient, .later query next current ((before, trace), state) (value.1, (value.2, backend)) _ _ _ step reachedRequest, pending⟩

/-- A captured wrapper callback occurs after an actual complete initial Builder result. An initial Builder cut carries `none` and cannot supply this witness. -/
theorem builder_reaches
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, chosen query state = true → PqxdhInitialForwardPost.selected query = true)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (origin : Origin) (index : Fin S)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (state reached : Local)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (supported : Cut.pending (context, some details) reached ∈ support
      (scan PqxdhInitialForwardPost.selected chosen selection impl
        (PqxdhLaterChallengeBuilderCapture.capturedBuilder mark origin sender route read index before trace source initial metadata ready owner number bit adversary)
        (PqxdhLaterChallengeBuilderCapture.builder_covered mark origin sender route read index before trace source initial metadata ready owner number bit adversary) state)) :
    ∃ built backend front history ambient,
      (built, backend) ∈ support ((simulateQ impl (simulateQ erase
        (PqxdhInitialOriginForwardBuilder.program source mark origin sender route read initial index metadata ready pure before trace))).run state) ∧
      PqxdhRecordConfidentialityTrace.Reaches (postImpl mark sender route read impl) owner number bit
        (adversary built.1) PqxdhRecordConfidentialityChallenge.initial (built.2, backend)
        ((PqxdhFirstRecordConfidentiality.AdvSpec extra S B).query details.request.query >>= details.request.next)
        details.request.before ((front, history), ambient) ∧
      Cut.pending details.callback reached ∈ support
        (scan PqxdhInitialForwardPost.selected chosen selection impl
          (program mark sender route read ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history)
          (program_covered mark sender route read ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history) ambient) := by
  unfold PqxdhLaterChallengeBuilderCapture.capturedBuilder at supported
  rcases native_pending_cases PqxdhInitialForwardPost.selected chosen selection impl _ _
    ((PqxdhLaterChallengeCapture.covered_tags _ _ _).mpr
      (PqxdhInitialOriginForwardBuilder.program_covered source mark origin sender route read initial index metadata ready pure before trace))
    (fun built => (PqxdhLaterChallengeCapture.covered_tags _ _ _).mpr
      (PqxdhLaterChallengeCapture.captured_covered mark sender route read owner number bit
        (adversary built.1) PqxdhRecordConfidentialityChallenge.initial built.2.1 built.2.2))
    (PqxdhLaterChallengeBuilderCapture.builder_covered mark origin sender route read index before trace source initial metadata ready owner number bit adversary)
    state reached (context, some details) supported with inside | later
  · obtain ⟨callback, same, pending⟩ := native_pending_map _ PqxdhInitialForwardPost.selected chosen selection impl _
      (PqxdhInitialOriginForwardBuilder.program_covered source mark origin sender route read initial index metadata ready pure before trace)
      state reached (context, some details) inside
    cases same
  · obtain ⟨built, backend, actual, remaining⟩ := later
    obtain ⟨tag, same, pending⟩ := native_pending_map _ PqxdhInitialForwardPost.selected chosen selection impl _
      (PqxdhLaterChallengeCapture.captured_covered mark sender route read owner number bit
        (adversary built.1) PqxdhRecordConfidentialityChallenge.initial built.2.1 built.2.2)
      backend reached (context, some details) remaining
    have exactTag : tag = (context, details) := Prod.ext (Prod.mk.inj same).1 (Option.some.inj (Prod.mk.inj same).2)
    obtain ⟨front, history, ambient, reachedRequest, cut⟩ := captured_reaches mark sender route read impl chosen selection owner number bit
      (adversary built.1) PqxdhRecordConfidentialityChallenge.initial built.2.1 built.2.2 backend reached context details (exactTag ▸ pending)
    rw [erase_mapTags] at actual
    exact ⟨built, backend, front, history, ambient, actual, reachedRequest, cut⟩

end Source

section Shared
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open PqxdhInitialPostContext PqxdhNativeSharedPrefix
open PqxdhLaterChallengeBuilderCapture CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I D K X Response Shared Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (depth : Nat)

/-- Evaluating the literal captured shared scanner is the full audited native scan with the same capture. Private logs, candidates and the complete shared cache stay in the result. -/
theorem shared_source (state : Local A N C) (cache : CtxRO.QueryCache) :
    RawCtxSharedPrefixScan.restore attach <$>
      (simulateQ hashImpl (sharedCarried mark origin sender route read index before trace source writer stage
        pre application initializer selector aux initial metadata ready owner number bit adversary depth state)).run cache =
      scan PqxdhInitialForwardPost.selected (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth)
        (PqxdhInitialNativeAudit.handler source writer stage (fun request => localLift (pre request))
          (fun reply => localLift (application reply)) (fun secrets => localLift (initializer secrets))
          (fun request => localLift (selector request)) (fun request => localLift (aux request)))
        (capturedBuilder mark origin sender route read index before trace source initial metadata ready owner number bit adversary)
        (builder_covered mark origin sender route read index before trace source initial metadata ready owner number bit adversary)
        (attach state cache) := by
  exact RawCtxSharedPrefixScan.source PqxdhInitialForwardPost.selected (selected depth)
    (fun query state chosen => native_selection depth query (attach state ∅) chosen)
    (compiler source writer stage pre application initializer selector aux)
    (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth)
    (PqxdhInitialNativeAudit.handler source writer stage (fun request => localLift (pre request))
      (fun reply => localLift (application reply)) (fun secrets => localLift (initializer secrets))
      (fun request => localLift (selector request)) (fun request => localLift (aux request)))
    attach (selection_cache depth) (step source writer stage pre application initializer selector aux)
    _ _ state cache

local notation "nativeHandler" => PqxdhInitialNativeAudit.handler source writer stage
  (fun request => localLift (pre request)) (fun reply => localLift (application reply))
  (fun secrets => localLift (initializer secrets)) (fun request => localLift (selector request))
  (fun request => localLift (aux request))

/-- An actual evaluated shared-prefix capture supplies the reached native Builder and wrapper request, at the same callback-local cut and complete audited backend. -/
theorem shared_reaches (state : Local A N C) (cache : CtxRO.QueryCache)
    (reached : Local A N C) (after : CtxRO.QueryCache)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (supported : (Cut.pending (context, some details) reached, after) ∈ support
      ((simulateQ hashImpl (sharedCarried mark origin sender route read index before trace source writer stage
        pre application initializer selector aux initial metadata ready owner number bit adversary depth state)).run cache)) :
    ∃ built backend front history ambient,
      (built, backend) ∈ support ((simulateQ nativeHandler (simulateQ erase
        (PqxdhInitialOriginForwardBuilder.program source mark origin sender route read initial index metadata ready pure before trace))).run (attach state cache)) ∧
      PqxdhRecordConfidentialityTrace.Reaches (postImpl mark sender route read nativeHandler) owner number bit
        (adversary built.1) PqxdhRecordConfidentialityChallenge.initial (built.2, backend)
        ((PqxdhFirstRecordConfidentiality.AdvSpec extra S B).query details.request.query >>= details.request.next)
        details.request.before ((front, history), ambient) ∧
      Cut.pending details.callback (attach reached after) ∈ support
        (scan PqxdhInitialForwardPost.selected (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth) nativeHandler
          (PqxdhInitialOriginForwardPost.program mark sender route read ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history)
          (PqxdhInitialOriginForwardPost.program_covered mark sender route read ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history) ambient) := by
  apply builder_reaches mark sender route read nativeHandler (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth)
    source origin index initial metadata ready before trace owner number bit adversary (attach state cache) (attach reached after) context details
  rw [← shared_source source writer stage pre application initializer selector aux mark origin sender route read index before trace
    initial metadata ready owner number bit adversary depth state cache, support_map]
  exact ⟨(Cut.pending (context, some details) reached, after), supported, rfl⟩

end Shared

end BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.native_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.native_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.native_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.native_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.native_pending_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.native_pending_cases
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.native_pending_map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.native_pending_map
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.post_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.post_program
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.captured_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.captured_reaches
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.builder_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.builder_reaches
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.shared_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.shared_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology.shared_reaches
