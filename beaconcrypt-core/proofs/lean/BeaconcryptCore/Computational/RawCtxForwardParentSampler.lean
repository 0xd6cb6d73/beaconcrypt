import BeaconcryptCore.Computational.RawCtxForwardScan
import BeaconcryptCore.Computational.RawCtxForwardLive
import BeaconcryptCore.Computational.RawCtxForwardCosts
import BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds
import BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets
import BeaconcryptCore.Computational.RawCtxLoggedParentSampler
import BeaconcryptCore.Computational.RawCtxFirstParentPrefix

/-!
The carried source sampler maps only actual completion and an explicitly carried family context into the original parent continuation interface. It has no analysis classifier or unsupported fallback branch. The concrete LIVE source annotation supplies exact erasure, complete descriptor soundness and coverage; the actual matched-parent selector and complete logged source backend supply the prefix execution.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardParentSampler
open RawCtxSelectedFamilyContext RawCtxSelectiveFamilyLog RawCtxPendingSelectiveFamily
variable {M P I D K A Result : Type} {S B : Nat}

abbrev Carried (M P I D K A Result : Type) (S B : Nat) := RawCtxForwardScan.Cut
  (Context M P I D K Result S B) (Result × NativeLive M P I D K S B) (LoggedState A)

noncomputable def compiled
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) :=
  RawCtxForwardLive.program sender route decode client
    (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined state.1, state.2)

def promote : Carried M P I D K A Result S B → RawCtxLoggedParentSampler.Cut M P I D K A Result S B
  | .complete result state => .complete result state
  | .pending context state => .pending context state

/-- The actual native family compiler erases to the same enriched full source program, including its original representation conversion. -/
theorem compiled_erase (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) :
    simulateQ RawCtxForwardAnnotation.erase (compiled sender route decode client state) =
      RawCtxPendingSelectiveFamily.program sender route decode client state :=
  RawCtxForwardLive.program_erase sender route decode client _

noncomputable def carried
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (Spec S B).Domain → LoggedState A → Bool)
    (selection : ∀ query reached, selected query reached = true → RawCtxPendingFamilyLiveTails.selected query = true)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :=
  promote <$> RawCtxForwardScan.scan RawCtxPendingFamilyLiveTails.selected selected selection
    (RawCtxSelectiveFamilyLog.handler source writer stage) (compiled sender route decode client state)
    (RawCtxForwardLive.program_covered sender route decode client _) initial

/-- The promoted source sampler retains the exact original completion or full carried family frame; it never constructs the analysis fallback. -/
theorem pack_promote (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (saved : Carried M P I D K A Result S B) :
    RawCtxLoggedParentSampler.pack sender route decode (promote saved) =
      RawCtxForwardScan.pack (frame sender route decode) saved := by
  cases saved <;> rfl

/-- The actual matched-parent selector can select only a private derivation query, whose source annotation must carry its context. -/
theorem parent_private (depth : Nat) (query : (Spec S B).Domain) (state : LoggedState A)
    (chosen : RawCtxPendingParentCallbacks.parentCut depth query state.1 = true) :
    RawCtxPendingFamilyLiveTails.selected query = true := by
  rcases query with ((request | opening) | ((request | sealing) | publicQuery)) | read
  all_goals first | rfl | cases chosen

/-- Supported carried output retains actual chronological cache provenance and the selected source address and depth, with no fallback branch. -/
theorem supported_valid
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (covered : RawCtxSelectiveFamilyLog.Covered initial) (saved : Carried M P I D K A Result S B)
    (supported : RawCtxForwardScan.pack (frame sender route decode) saved ∈
      support (RawCtxLoggedParentPrefix.scan source writer depth (depth + 1) sender route decode client state initial)) :
    RawCtxLoggedParentSampler.Valid depth (promote saved) := by
  have retained := RawCtxSelectiveFamilyLog.scan_covered source writer (depth + 1)
    (fun query reached => RawCtxPendingParentCallbacks.parentCut depth query reached.1)
    (RawCtxPendingSelectiveFamily.program sender route decode client state) initial covered
    (RawCtxForwardScan.pack (frame sender route decode) saved) supported
  cases saved with
  | complete result reached => exact retained
  | pending context reached =>
    obtain ⟨other, exactFrame, queryAddress, selected, sameDepth⟩ :=
      RawCtxLoggedParentPrefix.reached_context source writer depth (depth + 1) sender route decode client state
        initial reached (frame sender route decode context).1 (frame sender route decode context).2 supported
    have sameAddress : address other = address context := Option.some.inj
      (queryAddress.symm.trans (frame_address sender route decode context))
    exact ⟨retained, sameAddress ▸ selected, sameDepth⟩

/-- The complete actual logged source execution retains the established source uniform bill, with every caller coin, private full76 draw and shared commitment draw included. -/
theorem source_uniform
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :
    ((simulateQ (RawCtxSelectiveFamilyLog.handler source writer stage)
      (RawCtxPendingSelectiveFamily.program sender route decode client state)).run initial).IsTotalQueryBound
      (budget.1 .coin + 76 * (budget.1 .send + 51 * budget.1 .raw) +
        64 * (budget.1 .send + budget.1 .raw + budget.1 .hash)) := by
  have full := RawCtxSelectiveChainBudgets.family_uniform source writer stage S B sender route decode
    client budget bounded state initial.1.1 initial.1.2
  rw [← RawCtxSelectiveFamilyLog.source_projection source writer stage sender route decode client state
    initial.1.1 initial.1.2 initial.2] at full
  simpa only [RawCtxSelectiveFamilyLog.family, IsTotalQueryBound, isQueryBound_map_iff] using full

/-- The actual carried source sampler packs to exactly the original state-dependent logged prefix, with the complete original callback and all pre-cut effects. -/
theorem carried_pack
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (Spec S B).Domain → LoggedState A → Bool)
    (selection : ∀ query reached, selected query reached = true → RawCtxPendingFamilyLiveTails.selected query = true)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :
    RawCtxLoggedParentSampler.pack sender route decode <$>
      carried source writer stage selected selection sender route decode client state initial =
      RawCtxStatefulPendingPrefix.scan selected (RawCtxSelectiveFamilyLog.handler source writer stage)
        (RawCtxPendingSelectiveFamily.program sender route decode client state) initial := by
  simp only [carried, Functor.map_map]
  have packing : (fun saved : Carried M P I D K A Result S B =>
      RawCtxLoggedParentSampler.pack sender route decode (promote saved)) =
        RawCtxForwardScan.pack (frame sender route decode) := funext (pack_promote sender route decode)
  rw [packing]
  have actual := RawCtxForwardScan.scan_pack RawCtxPendingFamilyLiveTails.selected selected selection
    (RawCtxSelectiveFamilyLog.handler source writer stage) (frame sender route decode)
    (compiled sender route decode client state) (RawCtxForwardLive.program_covered sender route decode client _)
    (RawCtxForwardLive.program_sound sender route decode client _) initial
  simpa only [compiled_erase] using actual

/-- The carried sampler cannot return the mathematical classifier's unsupported fallback; its syntax constructs only completion or an actual source context. -/
theorem carried_no_other
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (Spec S B).Domain → LoggedState A → Bool)
    (selection : ∀ query reached, selected query reached = true → RawCtxPendingFamilyLiveTails.selected query = true)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (saved : RawCtxLoggedParentSampler.Prefix M P I D K A Result S B) :
    RawCtxLoggedParentSampler.Cut.other saved ∉
      support (carried source writer stage selected selection sender route decode client state initial) := by
  intro supported
  simp only [carried, support_map, Set.mem_image] at supported
  obtain ⟨cut, _, same⟩ := supported
  cases cut <;> cases same

/-- Every supported carried source context retains the actual selection condition and chronological cache provenance at that same reached state. -/
theorem carried_origin
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (Spec S B).Domain → LoggedState A → Bool)
    (selection : ∀ query reached, selected query reached = true → RawCtxPendingFamilyLiveTails.selected query = true)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial reached : LoggedState A)
    (covered : RawCtxSelectiveFamilyLog.Covered initial) (context : Context M P I D K Result S B)
    (supported : RawCtxLoggedParentSampler.Cut.pending context reached ∈
      support (carried source writer stage selected selection sender route decode client state initial)) :
    selected (frame sender route decode context).1 reached = true ∧ RawCtxSelectiveFamilyLog.Covered reached := by
  have mapped : (RawCtxPendingMixedPrefix.Stopped.pending (frame sender route decode context).1
      (frame sender route decode context).2, reached) ∈ support (RawCtxLoggedParentSampler.pack sender route decode <$>
        carried source writer stage selected selection sender route decode client state initial) := by
    rw [support_map]
    exact ⟨.pending context reached, supported, rfl⟩
  rw [carried_pack] at mapped
  exact ⟨(RawCtxStatefulPendingPrefix.pending_origin selected (RawCtxSelectiveFamilyLog.handler source writer stage)
      (RawCtxPendingSelectiveFamily.program sender route decode client state) initial reached
      (frame sender route decode context).1 (frame sender route decode context).2 mapped).1,
    RawCtxSelectiveFamilyLog.scan_covered source writer stage selected
      (RawCtxPendingSelectiveFamily.program sender route decode client state) initial covered _ mapped⟩

/-- Resuming the executable carried source sampler gives the same complete original logged source execution. -/
theorem carried_finish
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (Spec S B).Domain → LoggedState A → Bool)
    (selection : ∀ query reached, selected query reached = true → RawCtxPendingFamilyLiveTails.selected query = true)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :
    (carried source writer stage selected selection sender route decode client state initial >>=
      RawCtxLoggedParentSampler.run source writer stage sender route decode) =
      (simulateQ (RawCtxSelectiveFamilyLog.handler source writer stage)
        (RawCtxPendingSelectiveFamily.program sender route decode client state)).run initial := by
  have complete := RawCtxStatefulPendingPrefix.scan_finish selected (RawCtxSelectiveFamilyLog.handler source writer stage)
    (RawCtxPendingSelectiveFamily.program sender route decode client state) initial
  rw [← carried_pack source writer stage selected selection sender route decode client state initial] at complete
  simp only [bind_map_left] at complete
  exact complete

/-- The executable carried source sampler pays the actual full source uniform bill, independent of whether it stops, hits or rejects. -/
theorem carried_uniform
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (Spec S B).Domain → LoggedState A → Bool)
    (selection : ∀ query reached, selected query reached = true → RawCtxPendingFamilyLiveTails.selected query = true)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :
    (carried source writer stage selected selection sender route decode client state initial).IsTotalQueryBound
      (budget.1 .coin + 76 * (budget.1 .send + 51 * budget.1 .raw) +
        64 * (budget.1 .send + budget.1 .raw + budget.1 .hash)) := by
  apply IsTotalQueryBound.of_bind_left (ob := RawCtxLoggedParentSampler.run source writer stage sender route decode)
  rw [carried_finish]
  exact source_uniform source writer stage sender route decode client budget bounded state initial

/-- The actual source constructs at most S+51R carried private descriptors, including repeated private calls and cache hits. -/
theorem source_descriptors
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) :
    (compiled sender route decode client state).IsQueryBoundP (fun query => query.1.isSome = true)
      (budget.1 .send + 51 * budget.1 .raw) := by
  apply (RawCtxForwardCosts.descriptor_class RawCtxPendingFamilyLiveTails.selected
    (compiled sender route decode client state) (RawCtxForwardLive.program_covered sender route decode client _) _).mpr
  rw [compiled_erase]
  have same : (fun query : (Spec S B).Domain => RawCtxPendingFamilyLiveTails.selected query = true) =
      RawCtxSelectiveFamilyLogBounds.privateQuery := by
    funext query
    rcases query with ((request | opening) | ((request | sealing) | publicQuery)) | read
    all_goals simp [RawCtxPendingFamilyLiveTails.selected, RawCtxPendingMixedPrefix.ownerSelected,
      RawCtxSelectiveFamilyLogBounds.privateQuery, RawCtxSelectedFamilyContext.queryAddress,
      RawCtxSelectedFamilyContext.primitiveAddress]
  simp only [same]
  exact RawCtxSelectiveFamilyLogBounds.source_private sender route decode client budget bounded state

noncomputable def first
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :=
  carried source writer stage (RawCtxFirstParentPrefix.selected depth) (RawCtxFirstParentPrefix.selected_private depth)
    sender route decode client state initial

/-- The concrete executable first-hit/predecessor sampler is exactly the original first-hit logged source prefix after packing its carried contexts. -/
theorem first_pack
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :
    RawCtxLoggedParentSampler.pack sender route decode <$> first source writer depth stage sender route decode client state initial =
      RawCtxFirstParentPrefix.scan source writer depth stage sender route decode client state initial :=
  carried_pack source writer stage _ _ sender route decode client state initial

/-- Each actually returned predecessor is an explicit recorded-input cache hit or the fresh parent at the requested depth, derived from that same carried source sample. -/
theorem first_origin
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial reached : LoggedState A)
    (covered : RawCtxSelectiveFamilyLog.Covered initial) (context : Context M P I D K Result S B)
    (supported : RawCtxLoggedParentSampler.Cut.pending context reached ∈
      support (first source writer depth stage sender route decode client state initial)) :
    RawCtxSelectiveFamilyLog.Covered reached ∧ RawCtxSelectiveChainGame.matched reached.1.2.2 (address context) = true ∧
      ((address context ∈ reached.2 ∧ ∃ output, reached.1.2.1 (address context) = some output) ∨
        (reached.1.2.1 (address context) = none ∧ reached.1.2.2.depth = depth)) := by
  have actual := carried_origin source writer stage _ _ sender route decode client state initial reached covered context supported
  have cases := RawCtxFirstParentPrefix.selected_cases depth (frame sender route decode context).1 reached
    (address context) (frame_address sender route decode context) actual.1
  refine ⟨actual.2, cases.1, ?_⟩
  rcases cases.2 with ⟨output, present⟩ | fresh
  · exact Or.inl ⟨actual.2 _ output present, output, present⟩
  · exact Or.inr fresh

/-- Both full adjacent source family games use the same executable carried sampler, preserving early completion and original collision continuations without uniform-parent assumptions. -/
theorem first_adjacent
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (valid : initial.1.2.2.depth ≤ depth) :
    let common := first source writer depth (depth + 1) sender route decode client state initial
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= RawCtxLoggedParentSampler.run source writer (depth + 1) sender route decode)) =
      RawCtxSelectiveFamilyLog.family source writer (depth + 1) sender route decode client state initial.1.1 initial.1.2 initial.2 ∧
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= RawCtxLoggedParentSampler.run source writer (depth + 2) sender route decode)) =
      RawCtxSelectiveFamilyLog.family source writer (depth + 2) sender route decode client state initial.1.1 initial.1.2 initial.2 := by
  have actual := RawCtxFirstParentPrefix.adjacent_complete source writer depth sender route decode client state initial valid
  dsimp only at actual ⊢
  rw [← first_pack source writer depth (depth + 1) sender route decode client state initial] at actual
  simp only [bind_map_left] at actual
  exact actual

end BeaconcryptCore.Computational.RawCtxForwardParentSampler

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.compiled_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.compiled_erase
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.pack_promote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.pack_promote
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.parent_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.parent_private
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.supported_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.supported_valid
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.source_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.carried_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.carried_pack
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.carried_no_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.carried_no_other
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.carried_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.carried_origin
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.carried_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.carried_finish
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.carried_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.carried_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.source_descriptors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.source_descriptors
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.first_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.first_pack
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.first_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.first_origin
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardParentSampler.first_adjacent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardParentSampler.first_adjacent
