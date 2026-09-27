import BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization

/-!
The original forward first-parent sampler is resolved constructively into an already completed final decision or the actual fresh pending context. Completed and cached-common paths run the original real-stage full continuation and the same supplied final source observation. They do not acquire a fabricated hidden lineage or an artificial false decision. The pending context is retained before its original parent draw. This operational module neither conditions on reaching that draw nor asserts that the supplied final observation is target-free.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxStoppedParentSource
open PqxdhJointKdfGame RawCtxSelectiveFamilyLog RawCtxFirstParentRisk RawCtxAdjacentCacheNormalization
variable {M P I D K A Result : Type} {S B : Nat}

inductive Mode (M P I D K A Result : Type) (S B : Nat) where
  | common (decision : Bool)
  | pending (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B) (state : LoggedState A)

noncomputable def collect (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (observe : Output M P I D K A Result S B → ProbComp Bool)
    (cut : RawCtxLoggedParentSampler.Cut M P I D K A Result S B) : ProbComp (Mode M P I D K A Result S B) :=
  match cut with
  | .pending context state => match state.1.2.1 (RawCtxSelectedFamilyContext.address context) with
    | none => pure (.pending context state)
    | some _ => Mode.common <$> (continued source writer (depth + 1) sender route decode cut >>= observe)
  | _ => Mode.common <$> (continued source writer (depth + 1) sender route decode cut >>= observe)

noncomputable def prepare (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (observe : Output M P I D K A Result S B → ProbComp Bool) : ProbComp (Mode M P I D K A Result S B) :=
  RawCtxForwardParentSampler.first source writer depth (depth + 1) sender route decode client state initial >>=
    collect source writer depth sender route decode observe

noncomputable def resume (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (observe : Output M P I D K A Result S B → ProbComp Bool) :
    Mode M P I D K A Result S B → ProbComp Bool
  | .common decision => pure decision
  | .pending context state => continued source writer stage sender route decode (.pending context state) >>= observe

/-- Collecting complete and cached-common paths before the challenge preserves the entire real-stage source decision exactly. -/
theorem prepare_real (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (before : initial.1.2.2.depth ≤ depth)
    (observe : Output M P I D K A Result S B → ProbComp Bool) :
    (prepare source writer depth sender route decode client state initial observe >>=
      resume source writer (depth + 1) sender route decode observe) =
      family source writer (depth + 1) sender route decode client state initial.1.1 initial.1.2 initial.2 >>= observe := by
  rw [prepare, ← (source_adjacent source writer depth sender route decode client state initial before).1, bind_assoc, bind_assoc]
  apply bind_congr
  intro cut
  cases cut with
  | complete result reached => simp [collect, resume, bind_map_left]
  | other saved => simp [collect, resume, bind_map_left]
  | pending context reached =>
    cases found : reached.1.2.1 (RawCtxSelectedFamilyContext.address context) <;>
      simp [collect, found, resume, bind_map_left]

private theorem complete_stage (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (left right : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (result : Result × RawCtxSelectedFamilyContext.NativeLive M P I D K S B) (state : LoggedState A) :
    continued source writer left sender route decode (.complete result state) =
      continued source writer right sender route decode (.complete result state) := by
  simp only [continued, RawCtxLoggedParentSampler.run, RawCtxLoggedParentSampler.pack,
    RawCtxPendingMixedPrefix.finish]

/-- The same prepared sampler followed by the random-stage pending continuation is exactly the collision-normalized source game, with identical completed and cached-common decisions. -/
theorem prepare_random (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (observe : Output M P I D K A Result S B → ProbComp Bool) :
    (prepare source writer depth sender route decode client state initial observe >>=
      resume source writer (depth + 2) sender route decode observe) =
      normalized source writer depth sender route decode client state initial >>= observe := by
  classical
  rw [prepare, normalized, bind_assoc, bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro cut supported
  cases cut with
  | complete result reached =>
    have uncached : ¬ Cached (.complete result reached) := by simp [Cached]
    simp only [collect, bind_map_left, resume, bind_pure]
    rw [complete_stage source writer (depth + 1) (depth + 2) sender route decode result reached]
    rw [ite_eq_right uncached]
  | pending context reached =>
    cases found : reached.1.2.1 (RawCtxSelectedFamilyContext.address context) <;>
      simp [collect, found, resume, bind_map_left, Cached]
  | other saved =>
    exact False.elim (RawCtxForwardParentSampler.carried_no_other source writer (depth + 1)
      (RawCtxFirstParentPrefix.selected depth) (RawCtxFirstParentPrefix.selected_private depth)
      sender route decode client state initial saved supported)

/-- A pending prepared context is the exact original carried source result with an absent selected cache binding; no replacement context is selected. -/
theorem pending_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial reached : LoggedState A)
    (observe : Output M P I D K A Result S B → ProbComp Bool)
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B)
    (supported : Mode.pending context reached ∈ support
      (prepare source writer depth sender route decode client state initial observe)) :
    RawCtxLoggedParentSampler.Cut.pending context reached ∈ support
      (RawCtxForwardParentSampler.first source writer depth (depth + 1) sender route decode client state initial) ∧
      reached.1.2.1 (RawCtxSelectedFamilyContext.address context) = none := by
  simp only [prepare, mem_support_bind_iff] at supported
  obtain ⟨cut, head, after⟩ := supported
  cases cut with
  | complete result before => simp [collect, support_map] at after
  | other saved => simp [collect, support_map] at after
  | pending original before =>
    cases found : before.1.2.1 (RawCtxSelectedFamilyContext.address original) with
    | some output => simp [collect, found, support_map] at after
    | none =>
      simp only [collect, found, mem_support_pure_iff, Mode.pending.injEq] at after
      obtain ⟨rfl, rfl⟩ := after
      exact ⟨head, found⟩

/-- Every supported pending result is the actual fresh selected predecessor at the requested depth, with its original source Context and covered cache retained. -/
theorem pending_origin (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial reached : LoggedState A)
    (covered : Covered initial) (observe : Output M P I D K A Result S B → ProbComp Bool)
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B)
    (supported : Mode.pending context reached ∈ support
      (prepare source writer depth sender route decode client state initial observe)) :
    Covered reached ∧ RawCtxSelectiveChainGame.matched reached.1.2.2 (RawCtxSelectedFamilyContext.address context) = true ∧
      reached.1.2.1 (RawCtxSelectedFamilyContext.address context) = none ∧ reached.1.2.2.depth = depth := by
  obtain ⟨head, found⟩ := pending_source source writer depth sender route decode client state initial reached observe context supported
  have origin := RawCtxForwardParentSampler.first_origin source writer depth (depth + 1)
    sender route decode client state initial reached covered context head
  refine ⟨origin.1, origin.2.1, found, ?_⟩
  simpa only [found, reduceCtorEq, exists_const, and_false, false_or, true_and] using origin.2.2

/-- A supported pending mode executes the original full76 parent draw before its unchanged entire source continuation under either adjacent stage. -/
theorem pending_draw (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth stage : Nat) (later : depth < stage) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial reached : LoggedState A)
    (covered : Covered initial) (observe : Output M P I D K A Result S B → ProbComp Bool)
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B)
    (supported : Mode.pending context reached ∈ support
      (prepare source writer depth sender route decode client state initial observe)) :
    resume source writer stage sender route decode observe (.pending context reached) =
      (($ᵗ PqxdhFullSecretInputKdf.FullOutput) >>= fun output =>
        (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
          RawCtxLoggedParentResponse.resume source writer stage sender route decode context output reached) >>= observe) := by
  have facts := pending_origin source writer depth sender route decode client state initial reached covered observe context supported
  have actual := RawCtxLoggedParentResponse.execute_miss source writer stage sender route decode context reached
    facts.2.2.1 facts.2.1 (by omega)
  change (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
    RawCtxLoggedParentResponse.execute source writer stage sender route decode context reached) >>= observe = _
  rw [actual, map_bind, bind_assoc]

def toSum : Mode M P I D K A Result S B →
    Sum Bool (RawCtxSelectedFamilyContext.Context M P I D K Result S B × LoggedState A)
  | .common decision => .inl decision
  | .pending context state => .inr (context, state)

noncomputable def sumResume (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (observe : Output M P I D K A Result S B → ProbComp Bool) :
    Sum Bool (RawCtxSelectedFamilyContext.Context M P I D K Result S B × LoggedState A) → ProbComp Bool
  | .inl decision => pure decision
  | .inr saved => resume source writer stage sender route decode observe (.pending saved.1 saved.2)

/-- The source sampler exposes the ordinary common-or-pending sum interface by a literal data map, with no inverse, retry or conditioned sample. -/
theorem sum_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth stage : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (observe : Output M P I D K A Result S B → ProbComp Bool) :
    ((toSum <$> prepare source writer depth sender route decode client state initial observe) >>=
      sumResume source writer stage sender route decode observe) =
      (prepare source writer depth sender route decode client state initial observe >>=
        resume source writer stage sender route decode observe) := by
  rw [bind_map_left]
  apply bind_congr
  intro mode
  cases mode <;> rfl

/-- The executable common/pending sampler uses at most the original complete source uniform bill plus its actual final observer bill. The proof removes a literal program suffix, not an evaluated distribution. -/
theorem prepare_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (before : initial.1.2.2.depth ≤ depth)
    (observe : Output M P I D K A Result S B → ProbComp Bool) (qObserve : Nat)
    (observeBound : ∀ result ∈ support (family source writer (depth + 1) sender route decode client state
      initial.1.1 initial.1.2 initial.2), (observe result).IsTotalQueryBound qObserve) :
    (toSum <$> prepare source writer depth sender route decode client state initial observe).IsTotalQueryBound
      ((budget.1 .coin + 76 * (budget.1 .send + 51 * budget.1 .raw) +
        64 * (budget.1 .send + budget.1 .raw + budget.1 .hash)) + qObserve) := by
  have sourceBound := RawCtxForwardParentSampler.source_uniform source writer (depth + 1)
    sender route decode client budget bounded state initial
  have full : (family source writer (depth + 1) sender route decode client state initial.1.1 initial.1.2 initial.2).IsTotalQueryBound
      (budget.1 .coin + 76 * (budget.1 .send + 51 * budget.1 .raw) +
        64 * (budget.1 .send + budget.1 .raw + budget.1 .hash)) := by
    simpa only [family, IsTotalQueryBound, isQueryBound_map_iff] using sourceBound
  have totalP := isQueryBoundP_bind (full.isQueryBoundP (p := fun _ => True))
    (fun result supported => (observeBound result supported).isQueryBoundP (p := fun _ => True))
  have complete := (isQueryBoundP_true_iff _ _).mp totalP
  rw [← prepare_real source writer depth sender route decode client state initial before observe] at complete
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using complete.of_bind_left

end BeaconcryptCore.Computational.RawCtxStoppedParentSource

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSource.prepare_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSource.prepare_real

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSource.prepare_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSource.prepare_random

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSource.pending_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSource.pending_source

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSource.pending_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSource.pending_origin

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSource.pending_draw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSource.pending_draw

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSource.sum_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSource.sum_run

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSource.prepare_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSource.prepare_uniform
