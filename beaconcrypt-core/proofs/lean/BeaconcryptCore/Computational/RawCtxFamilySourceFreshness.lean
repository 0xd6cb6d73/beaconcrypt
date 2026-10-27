import BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy
import BeaconcryptCore.Computational.RawCtxFamilyReadCompiler
import BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation

/-!
The original finite-family source client is compiled through its actual record/public frontend and exact selected-owner read callback. All state, history, optional replies, shared primitive state and candidate logs remain present. The source program itself derives that a sticky hidden-read flag has an actual disclosed-value witness. On clear-flag executions, every original disclosed value is in the existing available-input candidate ledger. No final freshness or history correspondence is assumed. Public operations remain the supplied common real interface; their candidates are retained and never become freshness exclusions.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilySourceFreshness
open RawCtxProtocolReveals RawCtxSelectedChain RawCtxSelectedLiveRead RawCtxFamilyFreshnessProxy
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxGenericOwnerInterpretation

abbrev PrimitiveSpec := RawCtxSelectedAliasPrimitives.Spec
abbrev Spec := RawCtxSelectedLiveCompiler.Spec
abbrev Roles (M P I D K : Type) (S B : Nat) := RawCtxGenericRoleFamily.Roles Kernel M P I D K S B
abbrev State (M P I D K : Type) (S B : Nat) := RawCtxGenericFamilyLive.State Kernel M P I D K S B
variable {M P I D K A : Type} {S B : Nat}

noncomputable def compiler
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (StateT (State M P I D K S B) (OracleComp Spec)) :=
  fun query state => match query with
  | .inl request => do
      let result ← simulateQ RawCtxSelectedLiveCompiler.primitiveForward
        ((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode request).run state.1)
      pure (result.1, (result.2, tick state.2))
  | .inr request => do
      let reply ← RawCtxFamilyReadCompiler.compiler
        (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1)
      pure (reply, (state.1, note ⟨request, reply⟩ state.2))

/-- The literal compiler is exactly the original generic family/read source frontend, with its same record/public calls individually forwarded and its same selected-owner read. -/
theorem compiler_source
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    compiler (P := P) (I := I) (D := D) (K := K) (S := S) (B := B) calls publicCalls sender route decode =
      RawCtxGenericFamilyLive.impl (interpretedCalls RawCtxSelectedLiveCompiler.primitiveForward calls)
        (fun query => simulateQ RawCtxSelectedLiveCompiler.primitiveForward (publicCalls query))
        RawCtxFamilyReadCompiler.compiler sender route decode := by
  funext query state
  cases query with
  | inl request =>
      exact congrArg (fun work : OracleComp Spec ((RawCtxProtocolRoles.SourceSpec S B).Range request × Roles M P I D K S B) =>
        work >>= fun result => pure (result.1, (result.2, tick state.2)))
        (RawCtxGenericFamilyInterpretation.step_interpretation RawCtxSelectedLiveCompiler.primitiveForward
          calls publicCalls sender route decode request state.1)
  | inr request => rfl

structure Parameters where
  source : FixedHkdfSha512NoSaltSource
  writer : RawCtxMixedShared.Writer
  prior : RawCtxSelectedParentTable.Prior
  entry : RawCtxSelectedParentEntry.Entry
  output : FullOutput
  view : RawCtxSelectedParentLive.View
  target : RootOutput

noncomputable def handler (parameters : Parameters) : QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  RawCtxSelectedParentPrivate.handler parameters.source parameters.writer parameters.prior parameters.entry
    parameters.output (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain parameters.target))
    parameters.view parameters.target

noncomputable def observed (parameters : Parameters) : QueryImpl Spec (StateT (RawCtxSelectedParentLive.State A) ProbComp) :=
  RawCtxSelectedParentPrivate.observed parameters.source parameters.writer parameters.prior parameters.entry
    parameters.output (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain parameters.target))
    parameters.view parameters.target

abbrev FullState (M P I D K A : Type) (S B : Nat) := State M P I D K S B × RawCtxSelectedParentLive.State A

noncomputable def step (parameters : Parameters)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (StateT (FullState M P I D K A S B) ProbComp) :=
  fun query state =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (observed parameters) ((compiler calls publicCalls sender route decode query).run state.1)).run state.2

private theorem state_map {State Result Other : Type} (f : Result → Other)
    (work : StateT State ProbComp Result) (state : State) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state :=
  StateT.run_map f work state

/-- The original selected-owner read preserves all shared state and records its actual native reply, available candidates and exact sticky bit in the same execution. -/
theorem read_step (parameters : Parameters)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : Request S B) (state : FullState M P I D K A S B) :
    let input := (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1.1)
    (step parameters calls publicCalls sender route decode (.inr request)).run state =
      pure (RawCtxGenericFamilyRead.nativeValue (nativeKernel (RawCtxFreshChainCut.concreteChain parameters.target)) input,
        ((state.1.1, note (actualObservation (RawCtxFreshChainCut.concreteChain parameters.target) input) state.1.2),
          ((state.2.1.1, state.2.1.2 ++ candidates (readKind request) input.2), state.2.2 || direct input))) := by
  have traced := RawCtxFamilyReadCompiler.trace_read parameters.source parameters.writer parameters.prior
    parameters.entry parameters.output
    (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain parameters.target))
    parameters.view parameters.target
    (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1.1) state.2
  simp only [StateT.run] at traced
  simp only [step, compiler, StateT.run, bind_pure_comp, simulateQ_map, state_map, observed, traced,
    RawCtxFamilyReadCompiler.native_value, map_pure]
  rfl

/-- Every original non-read role/public operation retains its complete source effects and candidate log, advances the original history and leaves the direct-read bit unchanged. -/
theorem nonread_step (parameters : Parameters)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (RawCtxProtocolRoles.SourceSpec S B).Domain) (state : FullState M P I D K A S B) :
    (step parameters calls publicCalls sender route decode (.inl request)).run state =
      (fun result => (result.1.1, ((result.1.2, tick state.1.2), (result.2, state.2.2)))) <$>
        (simulateQ (RawCtxSelectedQueryTrace.recorded (fun query => handler parameters (.inl query))
          RawCtxSelectedAliasPrimitives.inputs)
          ((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode request).run state.1.1)).run state.2.1 := by
  have retained := RawCtxFamilyReadCompiler.primitive_complete (handler (A := A) parameters)
    ((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode request).run state.1.1)
    state.2.1 state.2.2
  simp only [StateT.run] at retained
  simp only [step, compiler, StateT.run, bind_pure_comp, simulateQ_map, state_map]
  rw [show observed (A := A) parameters = RawCtxFlaggedQueryTrace.trace (handler parameters)
    RawCtxSelectedLiveCompiler.inputs RawCtxSelectedParentReadMask.direct from rfl, ← retained]
  simp only [Functor.map_map, Prod.map_def, id_eq]

private theorem primitive_prefix {Base Result : Type}
    (handler : QueryImpl Spec (StateT Base ProbComp))
    (program : OracleComp PrimitiveSpec Result) (state : Base × List RootOutput)
    (result : Result × (Base × List RootOutput))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedQueryTrace.recorded (fun query => handler (.inl query)) RawCtxSelectedAliasPrimitives.inputs)
      program).run state)) : state.2 ⊆ result.2.2 := by
  have retained := RawCtxFamilyReadCompiler.primitive_complete handler program state false
  have marked : (result.1, (result.2, false)) ∈ support ((simulateQ
      (RawCtxFlaggedQueryTrace.trace handler RawCtxSelectedLiveCompiler.inputs RawCtxSelectedParentReadMask.direct)
      (simulateQ RawCtxSelectedLiveCompiler.primitiveForward program)).run (state, false)) := by
    rw [← retained]
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  exact RawCtxFamilyReadCompiler.retained_candidates handler _ _ _ marked

def Invariant (target : RootOutput) (prior : List RatchetChain) (state : FullState M P I D K A S B) : Prop :=
  Witness (RawCtxFreshChainCut.concreteChain target) state.1.2 state.2.2 ∧
    (state.2.2 = false → knownInputs prior state.1.2 ⊆ state.2.1.2)

set_option backward.isDefEq.respectTransparency false in
/-- Every supported original family step derives its actual disclosure witness and retains all available disclosed bytes in the existing candidate ledger on clear-bit paths. -/
theorem step_invariant (parameters : Parameters)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (prior : List RatchetChain) (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (state : FullState M P I D K A S B) (before : Invariant parameters.target prior state)
    (result : (RawCtxProtocolReveals.SourceSpec S B).Range query × FullState M P I D K A S B)
    (supported : result ∈ support ((step parameters calls publicCalls sender route decode query).run state)) :
    Invariant parameters.target prior result.2 := by
  cases query with
  | inr request =>
      rw [read_step] at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      constructor
      · exact witness_note _ _ _ _ before.1
      · intro clear
        have conditions : state.2.2 = false ∧ direct
            (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1.1) = false := by
          simpa using clear
        have same := congrArg (Sigma.mk request) (value_before
          (RawCtxFreshChainCut.concreteChain parameters.target)
          (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1.1) conditions.2)
        change actualObservation (RawCtxFreshChainCut.concreteChain parameters.target) (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1.1) =
          labelObservation (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1.1) at same
        change knownInputs prior (note (actualObservation (RawCtxFreshChainCut.concreteChain parameters.target)
          (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1.1)) state.1.2) ⊆ _
        simp only [knownInputs, known_note, List.map_append, same, label_inputs]
        intro value present
        rcases List.mem_append.mp present with old | current
        · exact List.mem_append_left _ (before.2 conditions.1 old)
        · exact List.mem_append_right _ current
  | inl request =>
      rw [nonread_step, support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      constructor
      · exact before.1
      · intro clear
        exact List.Subset.trans (before.2 clear) (primitive_prefix (handler parameters) _ _ _ reached)

/-- The complete original adaptive source schedule derives the witness and candidate inclusion at every supported final state. -/
theorem schedule_invariant {Result : Type} (parameters : Parameters)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (prior : List RatchetChain) (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : FullState M P I D K A S B) (before : Invariant parameters.target prior state)
    (result : Result × FullState M P I D K A S B)
    (supported : result ∈ support ((simulateQ (step parameters calls publicCalls sender route decode) client).run state)) :
    Invariant parameters.target prior result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact before
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      change result ∈ support (((step parameters calls publicCalls sender route decode query).run state) >>= fun reply =>
        (simulateQ (step parameters calls publicCalls sender route decode) (next reply.1)).run reply.2) at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      exact ih reply.1 reply.2 (step_invariant parameters calls publicCalls sender route decode prior query state before reply head)
        result tail

/-- The supported source execution is exactly the same original compiled primitive client used by the retained-parent games, with only tuple association changed. -/
theorem source_project {Result : Type} (parameters : Parameters)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : FullState M P I D K A S B) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (observed parameters) ((simulateQ (compiler calls publicCalls sender route decode) client).run state.1)).run state.2 =
      (simulateQ (step parameters calls publicCalls sender route decode) client).run state := by
  have same : ((observed (A := A) parameters).mapStateTBase
      (compiler (P := P) (I := I) (D := D) (K := K) (S := S) (B := B) calls publicCalls sender route decode)).flattenStateT =
      step parameters calls publicCalls sender route decode := rfl
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, same, Functor.map_map]
  change id <$> ((simulateQ (step parameters calls publicCalls sender route decode) client).run state) = _
  simp only [Functor.map_id, id_eq]

/-- Starting with a clear bit and the exact prior/history candidate list derives the source invariant without a freshness assumption. -/
theorem initial_invariant (target : RootOutput) (prior : List RatchetChain) (state : State M P I D K S B)
    (primitive : RawCtxSharedPrimitive.SharedState A) :
    Invariant target prior (state, ((primitive, knownInputs prior state.2), false)) := by
  constructor
  · intro impossible
    cases impossible
  · exact fun _ => List.Subset.refl _

/-- In every supported original execution, actual finite-value freshness equals the unavailable-input-free proxy outside the same total candidate event. -/
theorem source_fresh_proxy {Result : Type} (parameters : Parameters)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked prior : List RatchetChain) (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : FullState M P I D K A S B) (before : Invariant parameters.target prior state)
    (result : Result × FullState M P I D K A S B)
    (supported : result ∈ support ((simulateQ (step parameters calls publicCalls sender route decode) client).run state))
    (safe : parameters.target ∉ result.2.2.1.2) :
    RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain parameters.target :: blocked) prior result.2.1.2 ↔
      Proxy blocked prior result.2.1.2 result.2.2.2 := by
  have after := schedule_invariant parameters calls publicCalls sender route decode prior client state before result supported
  exact fresh_proxy parameters.target blocked prior result.2.1.2 result.2.2.2 after.1
    (fun clear present => safe (after.2 clear present))

private theorem event_distance {Result : Type} (work : ProbComp Result) (actual proxy bad : Result → Prop)
    (included : ∀ result ∈ support work, actual result → proxy result)
    (agreed : ∀ result ∈ support work, proxy result → ¬ bad result → actual result) :
    |(Pr{let x ← work}[actual x]).toReal - (Pr{let x ← work}[proxy x]).toReal| ≤ (Pr{let x ← work}[bad x]).toReal := by
  have smaller : Pr{let x ← work}[actual x] ≤ Pr{let x ← work}[proxy x] := prEvent_mono_of_support _ _ _ included
  have covered : Pr{let x ← work}[proxy x] ≤ Pr{let result ← work}[actual result ∨ bad result] := by
    apply prEvent_mono_of_support
    intro result supported enabled
    by_cases hit : bad result
    · exact Or.inr hit
    · exact Or.inl (agreed result supported enabled hit)
  have larger : Pr{let x ← work}[proxy x] ≤ Pr{let x ← work}[actual x] + Pr{let x ← work}[bad x] :=
    covered.trans (prEvent_or_le work actual bad)
  have smallerReal := ENNReal.toReal_mono (prEvent_ne_top _) smaller
  have largerReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), (prEvent_ne_top _)⟩) larger
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at largerReal
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr smallerReal)]
  linarith

/-- Replacing actual byte freshness by the executable known-value proxy costs at most the original complete candidate-hit probability; forbidden direct reveals incur no additional probability term. -/
theorem source_event_bound (parameters : Parameters)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked prior : List RatchetChain) (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (state : FullState M P I D K A S B) (before : Invariant parameters.target prior state) :
    let work := (simulateQ (step parameters calls publicCalls sender route decode) client).run state
    |(Pr{let result ← work}[result.1 = true ∧ RawCtxLiveLineage.Fresh
        (RawCtxFreshChainCut.concreteChain parameters.target :: blocked) prior result.2.1.2]).toReal -
      (Pr{let result ← work}[result.1 = true ∧ Proxy blocked prior result.2.1.2 result.2.2.2]).toReal| ≤
      (Pr{let result ← work}[parameters.target ∈ result.2.2.1.2]).toReal := by
  apply event_distance
  · intro result supported enabled
    have after := schedule_invariant parameters calls publicCalls sender route decode prior client state before result supported
    exact ⟨enabled.1, fresh_clear _ blocked prior _ _ after.1 enabled.2,
      fun value present => enabled.2 value (List.mem_cons_of_mem _ present)⟩
  · intro result supported enabled safe
    exact ⟨enabled.1, (source_fresh_proxy parameters calls publicCalls sender route decode blocked prior client state
      before result supported safe).mpr enabled.2⟩

/-- The same probability bridge applies directly to the original old-interface compiled client used by the computational hop, preserving its full private state and candidate list. -/
theorem compiled_event_bound (parameters : Parameters)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked prior : List RatchetChain) (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (state : FullState M P I D K A S B) (before : Invariant parameters.target prior state) :
    let work := (simulateQ (observed parameters)
      ((simulateQ (compiler calls publicCalls sender route decode) client).run state.1)).run state.2
    |(Pr{let result ← work}[result.1.1 = true ∧ RawCtxLiveLineage.Fresh
        (RawCtxFreshChainCut.concreteChain parameters.target :: blocked) prior result.1.2.2]).toReal -
      (Pr{let result ← work}[result.1.1 = true ∧ Proxy blocked prior result.1.2.2 result.2.2]).toReal| ≤
      (Pr{let result ← work}[parameters.target ∈ result.2.1.2]).toReal := by
  have bounded := source_event_bound parameters calls publicCalls sender route decode blocked prior client state before
  rw [← source_project parameters calls publicCalls sender route decode client state] at bounded
  simpa only [prEvent_map, Function.comp_def] using bounded

end BeaconcryptCore.Computational.RawCtxFamilySourceFreshness

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.compiler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.compiler_source
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.read_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.read_step
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.nonread_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.nonread_step
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.step_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.step_invariant
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.schedule_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.schedule_invariant
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.source_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.source_project
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.initial_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.initial_invariant
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.source_fresh_proxy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.source_fresh_proxy
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.source_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.source_event_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.compiled_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilySourceFreshness.compiled_event_bound
