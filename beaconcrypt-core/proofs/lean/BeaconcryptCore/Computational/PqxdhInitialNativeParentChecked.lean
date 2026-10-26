import BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent
import BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness

/-!
The actual partial-routing observer's complete finite checker can be evaluated while preserving every original result and ambient effect. Candidate and disclosure instrumentation are erased only from an observation that does not inspect them; the checked freshness comparison itself retains and charges that instrumentation separately.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialParentStoppedHop PqxdhInitialParentObserverCompiler PqxdhInitialBeaconAmbient
variable {ι Context M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Candidate and disclosure instrumentation cannot change any original reply or state field. -/
theorem trace_project {δ T V : Type} {spec : OracleSpec δ}
    (impl : QueryImpl spec (StateT T ProbComp)) (inputs : spec.Domain → List RootOutput)
    (direct : spec.Domain → Bool) (client : OracleComp spec V) (state : (T × List RootOutput) × Bool) :
    (fun result => (result.1, result.2.1.1)) <$>
      (simulateQ (RawCtxFlaggedQueryTrace.trace impl inputs direct) client).run state =
      (simulateQ impl client).run state.1.1 := by
  refine map_run_simulateQ_eq_of_query_map_eq (RawCtxFlaggedQueryTrace.trace impl inputs direct) impl
    (fun current => current.1.1) ?_ client state
  intro query before
  simp only [RawCtxFlaggedQueryTrace.trace, StateT.run, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, Prod.eta]
  exact LawfulFunctor.id_map _

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (continuation : Continuation Context extra M P I D K X Response Shared A N C Result Origin S B)
    (context : Context × RawCtxSelectedParentEntry.Entry) (target : RootOutput) (output : FullOutput)

/-- Each appended checker query uses only the original private ratchet callback and returns the exact partial-routing step. -/
theorem checker_step (reader : RawCtxSelectedLiveTrace.Reader) (input : RawCtxSelectedChain.Slot) :
    simulateQ (PqxdhInitialParentPrivateObserver.handler source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1) reader target) (checkerCompiler input) =
      pure (RawCtxFiniteLineageCheck.routedStep (continuation.prior context.1) context.2 target output input) := by
  apply (simulateQ_spec_query _ _).trans
  rw [PqxdhInitialParentPrivateObserver.old_source]
  cases input <;> simp only [RawCtxSelectedParentPrivate.known_send, RawCtxSelectedParentPrivate.hidden_send,
    RawCtxFiniteLineageCheck.routedStep]
  all_goals rfl

/-- The actual partial observer evaluates its appended finite checker without changing any ambient field. -/
theorem checker_source (reader : RawCtxSelectedLiveTrace.Reader) (depth : Option Nat) :
    simulateQ (PqxdhInitialParentPrivateObserver.handler source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1) reader target) (checker depth) =
      pure (checkerTrace (continuation.prior context.1) context.2 target output depth) := by
  cases depth with
  | none => rfl
  | some depth =>
      rw [checker, ← QueryImpl.simulateQ_compose]
      have step : PqxdhInitialParentPrivateObserver.handler source writer (continuation.prior context.1) context.2 output
          (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
          (continuation.selector context.1) (continuation.aux context.1) reader target ∘ₛ checkerCompiler =
          (fun input => pure (RawCtxFiniteLineageCheck.routedStep (continuation.prior context.1) context.2 target output input)) :=
        funext (checker_step source writer continuation context target output reader)
      rw [step]
      exact RawCtxFiniteLineageCheck.evaluate RawCtxFiniteLineageCheck.labelKey
        (RawCtxFiniteLineageCheck.routedStep (continuation.prior context.1) context.2 target output) depth .hidden

/-- The complete native freshness run retains the original stopped result and actual finite checker list after erasing only private candidate/flag instrumentation. -/
theorem native_projection (disclosed : List RatchetChain) (state : PqxdhInitialParentObserver.State A N C)
    (candidates : List RootOutput) :
    (fun result => (result.1, result.2.1.1)) <$>
      PqxdhInitialPrivateCheckedFreshness.nativeRun source writer mark sender route decode continuation context target output
        disclosed state candidates =
    (fun result => ((result.1, checkerTrace (continuation.prior context.1) context.2 target output
      (continuation.depth context.1)), result.2)) <$>
      (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer (continuation.prior context.1) context.2 output
        (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
        (continuation.selector context.1) (continuation.aux context.1)
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
        (baseProgram mark sender route decode continuation context)).run state := by
  rw [PqxdhInitialPrivateCheckedFreshness.nativeRun, PqxdhInitialParentPrivateObserver.observed, trace_project]
  simp only [program, simulateQ_bind, simulateQ_map, checker_source, map_pure, bind_pure_comp,
    StateT.run_map, PqxdhInitialStoppedDisclosure.initial]

/-- An observation of only the complete original result and checker list retains exactly the same distribution after removing the query instrumentation. -/
theorem observation (disclosed : List RatchetChain) (state : PqxdhInitialParentObserver.State A N C)
    (candidates : List RootOutput) (observe : SourceFinal M P I D K Result Origin S B → List RawCtxSelectedChain.Slot → Bool) :
    (fun result => observe result.1.1 result.1.2) <$>
      PqxdhInitialPrivateCheckedFreshness.nativeRun source writer mark sender route decode continuation context target output
        disclosed state candidates =
    (fun result => observe result.1 (checkerTrace (continuation.prior context.1) context.2 target output
      (continuation.depth context.1))) <$>
      (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer (continuation.prior context.1) context.2 output
        (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
        (continuation.selector context.1) (continuation.aux context.1)
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
        (baseProgram mark sender route decode continuation context)).run state := by
  have actual := congrArg
    (fun work : ProbComp (Final M P I D K Result Origin S B × PqxdhInitialParentObserver.State A N C) =>
      (fun result => observe result.1.1 result.1.2) <$> work)
    (native_projection source writer mark sender route decode continuation context target output disclosed state candidates)
  simpa only [Functor.map_map] using actual

/-- The concrete native publication/freshness decision on the full partial observer equals the same decision on its complete stopped source result and exact checker trace. -/
theorem decision_source (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (continuation : Continuation Context extra M P I D K X Response Shared A N C Bool Bool S B)
    (context : Context × RawCtxSelectedParentEntry.Entry) (target : RootOutput) (output : FullOutput)
    (disclosed : List RatchetChain) (state : PqxdhInitialParentObserver.State A N C) (candidates : List RootOutput)
    (remaining : Nat) (depth : continuation.depth context.1 = some remaining)
    (earlier ancestors : List RatchetChain) (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) :
    (PqxdhInitialPrivateCheckedFreshness.actualDecision target (earlier ++ ancestors) disclosed
      (fun result => PqxdhInitialPublishedEvent.Gate selected number result.1.1)) <$>
      PqxdhInitialPrivateCheckedFreshness.nativeRun source writer mark sender route decode continuation context target output
        disclosed state candidates =
    (fun result => PqxdhInitialNativeParentEvent.nativeDecision (continuation.prior context.1) context.2 target output
      remaining earlier ancestors disclosed selected number
      (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront (RawCtxSelectedParentCalls.nativeKernel target)) id) result.1)) <$>
      (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer (continuation.prior context.1) context.2 output
        (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
        (continuation.selector context.1) (continuation.aux context.1)
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
        (baseProgram mark sender route decode continuation context)).run state := by
  have actual := observation source writer mark sender route decode continuation context target output disclosed state candidates
    (fun result slots => @decide (PqxdhInitialPublishedEvent.Gate selected number result ∧
      RawCtxLiveLineage.Fresh (slots.map (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain target)) ++
        (earlier ++ ancestors)) disclosed result.2.1.roles.2) (Classical.propDecidable _))
  rw [depth] at actual
  exact actual

end BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.trace_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.trace_project

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.checker_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.checker_step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.checker_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.checker_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.native_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.native_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.observation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.decision_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked.decision_source
