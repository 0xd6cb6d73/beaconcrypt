import BeaconcryptCore.Computational.RawCtxLoggedParentResponse

/-!
The actual source scan stops at the earliest matched private cache hit or the requested predecessor depth. A cached predecessor is retained as an explicit collision branch with its original complete continuation; it is never resampled as a uniform parent. Every unselected matched callback is an actual cache miss. The fresh pending branch derives its miss and depth from the same reached cache and selector. Both adjacent source games use the same prefix, and finishing either saved branch recovers the entire original source execution. The global recurrence must charge the collision branch at the earlier input hop.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFirstParentPrefix
open PqxdhJointKdf PqxdhJointKdfGame RawCtxSelectiveChainGame RawCtxPendingSelectiveFamily RawCtxPendingParentCallbacks
open RawCtxSelectiveFamilyLog (LoggedState)
variable {M P I D K A Result : Type} {S B : Nat}

def hit (query : (Spec S B).Domain) (state : LoggedState A) : Bool :=
  match RawCtxSelectedFamilyContext.queryAddress query with
  | none => false
  | some address => matched state.1.2.2 address && (state.1.2.1 address).isSome

def selected (depth : Nat) (query : (Spec S B).Domain) (state : LoggedState A) : Bool :=
  parentCut depth query state.1 || hit query state

noncomputable def scan (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth stage : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :=
  RawCtxStatefulPendingPrefix.scan (selected depth) (RawCtxSelectiveFamilyLog.handler source writer stage)
    (program sender route decode client state) initial

/-- The constructive first-hit/predecessor selector stops only at actual original private KDF callbacks. -/
theorem selected_private (depth : Nat) (query : (Spec S B).Domain) (state : LoggedState A)
    (chosen : selected depth query state = true) : RawCtxPendingFamilyLiveTails.selected query = true := by
  rcases query with ((request | opening) | ((request | sealing) | request)) | request
  all_goals first | rfl | simp [selected, parentCut, hit, RawCtxSelectedFamilyContext.queryAddress,
    RawCtxSelectedFamilyContext.primitiveAddress] at chosen

/-- Every matched callback that the actual scan executes before stopping is a cache miss; the requested predecessor depth is also not skipped. -/
theorem unchosen (depth : Nat) (query : (Spec S B).Domain) (state : LoggedState A)
    (notSelected : selected depth query state = false) :
    parentCut depth query state.1 = false ∧
      ∀ address, RawCtxSelectedFamilyContext.queryAddress query = some address →
        matched state.1.2.2 address = true → state.1.2.1 address = none := by
  have both := Bool.or_eq_false_iff.mp notSelected
  refine ⟨both.1, ?_⟩
  intro address found matching
  have noHit := both.2
  simp only [hit, found, matching, Bool.true_and] at noHit
  cases present : state.1.2.1 address with
  | none => rfl
  | some output => simp [present] at noHit

/-- The pending selection is either an actual matched cached response or the exact requested depth with an actual cache miss. -/
theorem selected_cases (depth : Nat) (query : (Spec S B).Domain) (state : LoggedState A)
    (address : JointKdfAddress) (found : RawCtxSelectedFamilyContext.queryAddress query = some address)
    (chosen : selected depth query state = true) :
    matched state.1.2.2 address = true ∧
      ((∃ output, state.1.2.1 address = some output) ∨
        (state.1.2.1 address = none ∧ state.1.2.2.depth = depth)) := by
  cases present : state.1.2.1 address with
  | none =>
      have facts : matched state.1.2.2 address = true ∧ state.1.2.2.depth = depth := by
        simpa [selected, parentCut, hit, found, present] using chosen
      exact ⟨facts.1, Or.inr ⟨rfl, facts.2⟩⟩
  | some output =>
      have cases : (matched state.1.2.2 address = true ∧ state.1.2.2.depth = depth) ∨
          matched state.1.2.2 address = true := by
        simpa [selected, parentCut, hit, found, present] using chosen
      exact ⟨cases.elim And.left id, Or.inl ⟨output, rfl⟩⟩

private theorem step_same (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (query : (Spec S B).Domain) (state : LoggedState A)
    (valid : state.1.2.2.depth ≤ depth) :
    ((RawCtxSelectiveFamilyLog.handler source writer (depth + 1) query).run state) =
      ((RawCtxSelectiveFamilyLog.handler source writer (depth + 2) query).run state) := by
  have same := RawCtxPendingSelectiveFamily.handler_same source writer (depth + 1) query state.1
    (before_child depth query state.1 valid)
  simpa only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp] using
    congrArg (fun computation => (fun result => (result.1, (result.2, RawCtxSelectiveFamilyLog.inputs query state.2))) <$> computation) same

private theorem step_preserve (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage depth : Nat) (query : (Spec S B).Domain) (state : LoggedState A)
    (valid : state.1.2.2.depth ≤ depth) (notSelected : selected depth query state = false)
    (result : (Spec S B).Range query × LoggedState A)
    (supported : result ∈ support (((RawCtxSelectiveFamilyLog.handler source writer stage) query).run state)) :
    result.2.1.2.2.depth ≤ depth := by
  simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨reply, actual, rfl⟩ := supported
  exact RawCtxPendingParentPrefix.step_preserve source writer stage depth query state.1 valid
    (unchosen depth query state notSelected).1 reply actual

/-- The two original adjacent stages share one complete source prefix, stopping earlier cached matches instead of treating them as uniform predecessors. -/
theorem scan_same (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (valid : initial.1.2.2.depth ≤ depth) :
    scan source writer depth (depth + 1) sender route decode client state initial =
      scan source writer depth (depth + 2) sender route decode client state initial := by
  apply RawCtxStatefulPrefixInvariant.scan_same (selected depth)
    _ _ (fun reached => reached.1.2.2.depth ≤ depth) _ _ (program sender route decode client state) initial valid
  · intro query reached invariant _
    exact step_same source writer depth query reached invariant
  · intro query reached invariant notSelected result supported
    exact step_preserve source writer (depth + 1) depth query reached invariant notSelected result supported

/-- Finishing any saved branch, including a collision, recovers the actual complete source family and all private instrumentation. -/
theorem scan_complete (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth stage : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :
    Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (scan source writer depth stage sender route decode client state initial >>=
        RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer stage)) =
      RawCtxSelectiveFamilyLog.family source writer stage sender route decode client state initial.1.1 initial.1.2 initial.2 := by
  rw [scan, RawCtxStatefulPendingPrefix.scan_finish]
  rfl

/-- The same supported source scan derives its complete original frame, cache provenance and either an earlier recorded-input collision or the fresh predecessor at exactly the requested depth. -/
theorem reached_context (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth stage : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial reached : LoggedState A)
    (valid : initial.1.2.2.depth ≤ depth) (covered : RawCtxSelectiveFamilyLog.Covered initial)
    (query : (Spec S B).Domain)
    (next : (Spec S B).Range query → OracleComp (Spec S B)
      (Result × RawCtxSelectedFamilyContext.NativeLive M P I D K S B))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (scan source writer depth stage sender route decode client state initial)) :
    RawCtxSelectiveFamilyLog.Covered reached ∧ reached.1.2.2.depth ≤ depth ∧
    ∃ context : RawCtxSelectedFamilyContext.Context M P I D K Result S B,
      (⟨query, next⟩ : RawCtxSelectedFamilyContext.Frame M P I D K Result S B) =
        RawCtxSelectedFamilyContext.frame sender route decode context ∧
      RawCtxSelectedFamilyContext.queryAddress query = some (RawCtxSelectedFamilyContext.address context) ∧
      matched reached.1.2.2 (RawCtxSelectedFamilyContext.address context) = true ∧
      ((RawCtxSelectedFamilyContext.address context ∈ reached.2 ∧
          ∃ output, reached.1.2.1 (RawCtxSelectedFamilyContext.address context) = some output) ∨
        (reached.1.2.1 (RawCtxSelectedFamilyContext.address context) = none ∧ reached.1.2.2.depth = depth)) := by
  have actualCovered := RawCtxSelectiveFamilyLog.scan_covered source writer stage (selected depth)
    (program sender route decode client state) initial covered _ supported
  have actualDepth := RawCtxStatefulPrefixInvariant.scan_valid (selected depth)
    (RawCtxSelectiveFamilyLog.handler source writer stage) (fun reached => reached.1.2.2.depth ≤ depth)
    (fun query before invariant notSelected result actual =>
      step_preserve source writer stage depth query before invariant notSelected result actual)
    (program sender route decode client state) initial valid _ supported
  have origin := RawCtxStatefulPendingPrefix.pending_origin (selected depth)
    (RawCtxSelectiveFamilyLog.handler source writer stage) (program sender route decode client state)
    initial reached query next supported
  have tail := RawCtxPendingFamilyLiveTails.program_tail sender route decode client
    (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined state.1, state.2)
    query next origin.2 (selected_private depth query reached origin.1)
  obtain ⟨context, same⟩ := RawCtxSelectedFamilyContext.tail_context sender route decode query next tail
  have sameQuery := congrArg Sigma.fst same
  change query = (RawCtxSelectedFamilyContext.frame sender route decode context).1 at sameQuery
  have sameAddress : RawCtxSelectedFamilyContext.queryAddress query = some (RawCtxSelectedFamilyContext.address context) := by
    rw [sameQuery]
    exact RawCtxSelectedFamilyContext.frame_address sender route decode context
  have cases := selected_cases depth query reached _ sameAddress origin.1
  refine ⟨actualCovered, actualDepth, context, same, sameAddress, cases.1, ?_⟩
  rcases cases.2 with ⟨output, present⟩ | fresh
  · exact Or.inl ⟨actualCovered _ output present, output, present⟩
  · exact Or.inr fresh

/-- The actual saved collision branch reuses its cached response; only the derived fresh predecessor branch draws full76 before its unchanged complete continuation. -/
theorem pending_dispatch (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth stage : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B) (state : LoggedState A)
    (chosen : selected depth (RawCtxSelectedFamilyContext.frame sender route decode context).1 state = true)
    (active : depth < stage) :
    RawCtxLoggedParentResponse.execute source writer stage sender route decode context state =
      match state.1.2.1 (RawCtxSelectedFamilyContext.address context) with
      | some output => RawCtxLoggedParentResponse.resume source writer stage sender route decode context output state
      | none => ($ᵗ PqxdhFullSecretInputKdf.FullOutput) >>= fun output =>
          RawCtxLoggedParentResponse.resume source writer stage sender route decode context output state := by
  have facts := selected_cases depth (RawCtxSelectedFamilyContext.frame sender route decode context).1 state
    (RawCtxSelectedFamilyContext.address context) (RawCtxSelectedFamilyContext.frame_address sender route decode context) chosen
  cases present : state.1.2.1 (RawCtxSelectedFamilyContext.address context) with
  | some output => exact RawCtxLoggedParentResponse.execute_hit source writer stage sender route decode context state output present
  | none =>
      have actualDepth : state.1.2.2.depth = depth := by simpa [present] using facts.2
      exact RawCtxLoggedParentResponse.execute_miss source writer stage sender route decode context state present facts.1
        (by rw [actualDepth]; exact active)

/-- Both actual adjacent source games resume one common first-hit/predecessor prefix; collision continuations and early completion are retained without a new uniform-parent assumption. -/
theorem adjacent_complete (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (valid : initial.1.2.2.depth ≤ depth) :
    let common := scan source writer depth (depth + 1) sender route decode client state initial
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer (depth + 1))) =
      RawCtxSelectiveFamilyLog.family source writer (depth + 1) sender route decode client state initial.1.1 initial.1.2 initial.2) ∧
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer (depth + 2))) =
      RawCtxSelectiveFamilyLog.family source writer (depth + 2) sender route decode client state initial.1.1 initial.1.2 initial.2) := by
  refine ⟨scan_complete source writer depth (depth + 1) sender route decode client state initial, ?_⟩
  rw [scan_same source writer depth sender route decode client state initial valid]
  exact scan_complete source writer depth (depth + 2) sender route decode client state initial

end BeaconcryptCore.Computational.RawCtxFirstParentPrefix

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentPrefix.selected_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentPrefix.selected_private

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentPrefix.unchosen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentPrefix.unchosen

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentPrefix.selected_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentPrefix.selected_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentPrefix.scan_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentPrefix.scan_same

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentPrefix.scan_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentPrefix.scan_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentPrefix.reached_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentPrefix.reached_context

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentPrefix.pending_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentPrefix.pending_dispatch

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentPrefix.adjacent_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentPrefix.adjacent_complete
