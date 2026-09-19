import BeaconcryptCore.Computational.RawCtxLoggedParentResponse

/-!
A mathematical reification of the actual source-derived predecessor sampler retains completion and both cached and fresh matched callbacks. The saved context comes from the original full family/live program, with its complete pre-draw shared state, private cache, cursor and chronological inputs. Both adjacent child stages resume this same sampler. No arbitrary native continuation, cache separation or fresh-parent premise replaces an actual source branch. The classifier chooses an existing source-context witness in private analysis; it is not an executable inverse of arbitrary function equality and supplies no finite local runtime claim. A standard-game reduction must instead carry this context forward in its actual source interpreter and discharge the exact annotation erasure separately.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxLoggedParentSampler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectiveChainGame
open RawCtxSelectedFamilyContext RawCtxSelectiveFamilyLog RawCtxPendingSelectiveFamily
variable {M P I D K A Result : Type} {S B : Nat}

abbrev Prefix (M P I D K A Result : Type) (S B : Nat) :=
  RawCtxPendingMixedPrefix.Prefix (Spec S B) (Result × NativeLive M P I D K S B) (LoggedState A)

inductive Cut (M P I D K A Result : Type) (S B : Nat) where
  | complete (result : Result × NativeLive M P I D K S B) (state : LoggedState A)
  | pending (context : Context M P I D K Result S B) (state : LoggedState A)
  | other (saved : Prefix M P I D K A Result S B)

noncomputable def classify (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (saved : Prefix M P I D K A Result S B) : Cut M P I D K A Result S B := by
  classical
  exact match saved.1 with
  | .complete result => .complete result saved.2
  | .pending query next =>
    let proposition := ∃ context : Context M P I D K Result S B,
      (⟨query, next⟩ : Frame M P I D K Result S B) = frame sender route decode context
    @dite (Cut M P I D K A Result S B) proposition (Classical.propDecidable proposition)
      (fun found => .pending (Classical.choose found) saved.2) (fun _ => .other saved)

noncomputable def pack (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) : Cut M P I D K A Result S B → Prefix M P I D K A Result S B
  | .complete result state => (.complete result, state)
  | .pending context state => (.pending (frame sender route decode context).1 (frame sender route decode context).2, state)
  | .other saved => saved

/-- Reifying a complete pending source frame preserves the entire original dependent callback and saved state, even for arbitrary unsupported inputs. -/
theorem pack_classify (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (saved : Prefix M P I D K A Result S B) :
    pack sender route decode (classify sender route decode saved) = saved := by
  rcases saved with ⟨stopped, state⟩
  cases stopped with
  | complete result => rfl
  | pending query next =>
    simp only [classify]
    split
    · rename_i found
      exact congrArg (fun saved : Frame M P I D K Result S B =>
        (RawCtxPendingMixedPrefix.Stopped.pending saved.1 saved.2, state)) (Classical.choose_spec found).symm
    · rfl

noncomputable def sample (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) : ProbComp (Cut M P I D K A Result S B) :=
  classify sender route decode <$> RawCtxLoggedParentPrefix.scan source writer depth (depth + 1)
    sender route decode client state initial

noncomputable def run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cut : Cut M P I D K A Result S B) :=
  RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer stage) (pack sender route decode cut)

/-- The concrete source sampler followed by its complete continuation is exactly the same actual logged source prefix and finish, with no supplied continuation equation. -/
theorem sample_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :
    (sample source writer depth sender route decode client state initial >>= run source writer stage sender route decode) =
      (RawCtxLoggedParentPrefix.scan source writer depth (depth + 1) sender route decode client state initial >>=
        RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer stage)) := by
  simp only [sample, bind_map_left, run, pack_classify]

def Valid (depth : Nat) : Cut M P I D K A Result S B → Prop
  | .complete _ state => Covered state
  | .pending context state => Covered state ∧ matched state.1.2.2 (address context) = true ∧ state.1.2.2.depth = depth
  | .other _ => False

private theorem classify_valid (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) (covered : Covered initial)
    (saved : Prefix M P I D K A Result S B)
    (supported : saved ∈ support (RawCtxLoggedParentPrefix.scan source writer depth (depth + 1)
      sender route decode client state initial)) : Valid depth (classify sender route decode saved) := by
  have retained := RawCtxSelectiveFamilyLog.scan_covered source writer (depth + 1)
    (fun query logged => RawCtxPendingParentCallbacks.parentCut depth query logged.1)
    (program sender route decode client state) initial covered saved supported
  rcases saved with ⟨stopped, reached⟩
  cases stopped with
  | complete value => exact retained
  | pending query next =>
    obtain ⟨context, exactFrame, queryAddress, selected, sameDepth⟩ := RawCtxLoggedParentPrefix.reached_context
      source writer depth (depth + 1) sender route decode client state initial reached query next supported
    have found : ∃ context : Context M P I D K Result S B,
        (⟨query, next⟩ : Frame M P I D K Result S B) = frame sender route decode context := ⟨context, exactFrame⟩
    simp only [classify, dif_pos found, Valid]
    have chosenAddress := (congrArg (fun saved : Frame M P I D K Result S B =>
      RawCtxSelectedFamilyContext.queryAddress saved.1) (Classical.choose_spec found)).trans
        (frame_address sender route decode (Classical.choose found))
    have sameAddress : address context = address (Classical.choose found) := Option.some.inj (queryAddress.symm.trans chosenAddress)
    exact ⟨retained, sameAddress ▸ selected, sameDepth⟩

/-- Every supported actual sampler result is complete or carries the original matched source context and cache-input provenance; the unsupported fallback has zero support. -/
theorem sample_supported (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) (covered : Covered initial)
    (cut : Cut M P I D K A Result S B)
    (supported : cut ∈ support (sample source writer depth sender route decode client state initial)) : Valid depth cut := by
  simp only [sample, support_map, Set.mem_image] at supported
  obtain ⟨saved, reached, rfl⟩ := supported
  exact classify_valid source writer depth sender route decode client state initial covered saved reached

noncomputable def after (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    Cut M P I D K A Result S B → ProbComp ((Result × NativeLive M P I D K S B) × LoggedState A)
  | .complete result state => pure (result, state)
  | .pending context state => match state.1.2.1 (address context) with
    | some output => RawCtxLoggedParentResponse.resume source writer stage sender route decode context output state
    | none => ($ᵗ FullOutput) >>= fun output =>
      RawCtxLoggedParentResponse.resume source writer stage sender route decode context output state
  | .other saved => RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer stage) saved

/-- The actual supported predecessor split preserves its cached branch or original full76 draw and entire continuation under each child stage. -/
theorem after_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cut : Cut M P I D K A Result S B) (valid : Valid depth cut) (later : depth < stage) :
    after source writer stage sender route decode cut = run source writer stage sender route decode cut := by
  cases cut with
  | complete result state => rfl
  | other saved => exact False.elim valid
  | pending context state =>
    change Covered state ∧ matched state.1.2.2 (address context) = true ∧ state.1.2.2.depth = depth at valid
    cases found : state.1.2.1 (address context) with
    | some output =>
      simp only [after, found]
      exact (RawCtxLoggedParentResponse.execute_hit source writer stage sender route decode context state output found).symm
    | none =>
      simp only [after, found]
      have before : state.1.2.2.depth < stage := by omega
      exact (RawCtxLoggedParentResponse.execute_miss source writer stage sender route decode context state found valid.2.1 before).symm

/-- One supported source sampler resumes through its actual cached-or-fresh predecessor split, with the complete original final state and no conditioned branch probability. -/
theorem sample_after (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) (covered : Covered initial)
    (later : depth < stage) :
    (sample source writer depth sender route decode client state initial >>= after source writer stage sender route decode) =
      (RawCtxLoggedParentPrefix.scan source writer depth (depth + 1) sender route decode client state initial >>=
        RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer stage)) := by
  rw [← sample_run source writer depth stage sender route decode client state initial]
  exact bind_congr_of_forall_mem_support _ fun cut supported =>
    after_run source writer depth stage sender route decode cut
      (sample_supported source writer depth sender route decode client state initial covered cut supported) later

/-- From the actual empty private cache and depth-zero cursor, both complete adjacent source family games share one mathematical predecessor sampler and its actual cached-or-full76 response split. -/
theorem adjacent_empty (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (primitive : RawCtxSharedPrimitive.SharedState A)
    (input : PqxdhSecretInputKdf.RootOutput) (past : List JointKdfAddress) :
    let initial : LoggedState A := ((primitive, ((fun _ => none), ⟨input, 0⟩)), past)
    let common := sample source writer depth sender route decode client state initial
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= after source writer (depth + 1) sender route decode)) =
      RawCtxSelectiveFamilyLog.family source writer (depth + 1) sender route decode client state primitive initial.1.2 past ∧
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= after source writer (depth + 2) sender route decode)) =
      RawCtxSelectiveFamilyLog.family source writer (depth + 2) sender route decode client state primitive initial.1.2 past := by
  dsimp only
  have covered := empty_covered primitive (⟨input, 0⟩ : Cursor) past
  have common := RawCtxLoggedParentPrefix.adjacent_complete source writer depth sender route decode client state
    ((primitive, ((fun _ => none), ⟨input, 0⟩)), past) (Nat.zero_le depth)
  constructor
  · rw [sample_after source writer depth (depth + 1) sender route decode client state _ covered (by omega)]
    exact common.1
  · rw [sample_after source writer depth (depth + 2) sender route decode client state _ covered (by omega)]
    exact common.2

/-- A forward source compiler that carries the descriptor uses only its concrete complete erasure equation; this consumer does not call the analysis classifier. -/
theorem carried_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (carried : ProbComp (Cut M P I D K A Result S B))
    (erased : pack sender route decode <$> carried =
      RawCtxLoggedParentPrefix.scan source writer depth (depth + 1) sender route decode client state initial) :
    (carried >>= run source writer stage sender route decode) =
      (RawCtxLoggedParentPrefix.scan source writer depth (depth + 1) sender route decode client state initial >>=
        RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer stage)) := by
  rw [← erased]
  simp only [bind_map_left]
  rfl

end BeaconcryptCore.Computational.RawCtxLoggedParentSampler

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentSampler.pack_classify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentSampler.pack_classify

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentSampler.sample_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentSampler.sample_run

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentSampler.sample_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentSampler.sample_supported

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentSampler.after_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentSampler.after_run

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentSampler.sample_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentSampler.sample_after

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentSampler.adjacent_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentSampler.adjacent_empty

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentSampler.carried_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentSampler.carried_run
