import BeaconcryptCore.Computational.PqxdhPreparedPendingReplay
import BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths

/-! The source retained interpreter and existing installation-occurrence interpreter differ only by tuple association. The actual initializer and all other callbacks are kept. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRetainedOccurrenceInterpreter
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialNativeRetained PqxdhInitialBeaconAmbient PqxdhInitialReceiptConstruction
variable {ι I D K X Response A N Result : Type} {extra : OracleSpec ι} {S B : Nat}

def reassociate (state : RetainedState A N RootOracle.QueryCache) : InitialState A N :=
  ((state.1, state.2.1), state.2.2)

noncomputable def ambient (work : Ambient A N RootOracle.QueryCache Result) :
    StateT (InitialState A N) ProbComp Result := fun state =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> (work state.1).run state.2

private def promote {Value : Type} (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp Value) :
    StateT (InitialState A N) ProbComp Value := fun state =>
  (fun result => (result.1, ((result.2, state.1.2), state.2))) <$> work.run state.1.1

private theorem promote_pure {Value : Type} (value : Value) :
    promote (pure value : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp Value) =
      (pure value : StateT (InitialState A N) ProbComp Value) := rfl

private theorem promote_bind {Value Next : Type}
    (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp Value)
    (next : Value → StateT (RawCtxSharedPrimitive.SharedState A) ProbComp Next) :
    promote (work >>= next) = promote work >>= fun value => promote (N := N) (next value) := by
  funext state
  change (fun result => (result.1, ((result.2, state.1.2), state.2))) <$>
      (work state.1.1 >>= fun first => next first.1 first.2) =
    (((fun result => (result.1, ((result.2, state.1.2), state.2))) <$> work state.1.1) >>= fun first =>
      (fun result => (result.1, ((result.2, first.2.1.2), first.2.2))) <$> next first.1 first.2.1.1)
  simp only [map_bind, bind_map_left]

private theorem simulate_promote {δ Value : Type} {spec : OracleSpec δ}
    (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (client : OracleComp spec Value) :
    simulateQ (fun query => promote (N := N) (impl query)) client = promote (simulateQ impl client) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact (promote_pure value).symm
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, promote_bind, ih]

private theorem compose_promote {δ κ : Type} {spec : OracleSpec δ} {other : OracleSpec κ}
    (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (adapter : QueryImpl other (OracleComp spec)) :
    (fun query => promote (N := N) (impl query)) ∘ₛ adapter =
      (fun query => promote ((impl ∘ₛ adapter) query)) :=
  funext fun query => simulate_promote impl (adapter query)

private theorem original_promote
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    RawCtxPendingNativeCalls.original (fun query => promote (N := N) (native query))
      (fun query => promote (publicCalls query)) =
      fun query => promote (RawCtxPendingNativeCalls.original native publicCalls query) := by
  funext query
  rcases query with (query | pending) | ((query | pending) | request) <;>
    simp only [RawCtxPendingNativeCalls.original, RawCtxPendingNativeCalls.receive,
      RawCtxPendingNativeCalls.send, compose_promote]

private theorem pending_promote
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    RawCtxPendingNativeCalls.pending (fun query => promote (N := N) (native query))
      (fun query => promote (publicCalls query)) =
      fun query => promote (RawCtxPendingNativeCalls.pending native publicCalls query) := by
  simp only [RawCtxPendingNativeCalls.pending, original_promote, compose_promote]

private theorem live_promote
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    RawCtxPendingFamilyLiveQueries.handler
      (RawCtxPendingNativeCalls.pending (fun query => promote (N := N) (native query))
        (fun query => promote (publicCalls query)))
      (RawCtxGenericFamilyRead.nativeReader (serverCount := S) (beaconCount := B) ConcreteRatchetKernel.mk) =
    fun query => promote (RawCtxPendingFamilyLiveQueries.handler
      (RawCtxPendingNativeCalls.pending native publicCalls)
      (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) query) := by
  funext query
  cases query with
  | inl query => exact congrArg (fun impl => impl query) (pending_promote native publicCalls)
  | inr query => exact (promote_pure _).symm

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (selected : Message) (previousRoot : RootOutput)
  (response64 : PqxdhInitialRootLabelService.Response)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache))
  (application : Response → Ambient A N RootOracle.QueryCache (Option Pqxdh.Bytes))
  (selector : QueryImpl extra (Ambient A N RootOracle.QueryCache))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N RootOracle.QueryCache))

/-- One actual source callback preserves its complete reply and all non-analysis state when passed to the existing occurrence-path interpreter. -/
theorem source_step
    (query : (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared S B).Domain)
    (state : RetainedState A N RootOracle.QueryCache) :
    Prod.map id reassociate <$> (retained source writer prior
      (PqxdhInitialNativeAudit.external pre application
        (PqxdhInitialNativeInitializer.initial source selected previousRoot response64) selector aux) query).run state =
      (PqxdhInitialOccurrencePaths.handler source writer prior selected previousRoot response64
        (fun query => ambient (pre query))
        (fun reply => ambient (application reply))
        (fun query => ambient (selector query))
        (fun query => ambient (aux query)) query).run (reassociate state) := by
  cases query with
  | inl query =>
      have actual : PqxdhInitialOccurrencePaths.handler (S := S) (B := B)
          source writer prior selected previousRoot response64
          (fun query => ambient (pre query)) (fun reply => ambient (application reply))
          (fun query => ambient (selector query)) (fun query => ambient (aux query)) (.inl query) =
          promote (RawCtxPendingRetainedExecution.retained source writer prior query) :=
        congrArg (fun impl => impl query) (live_promote
          (RawCtxFunctionalFamily.native source writer prior)
          (RawCtxFunctionalFamily.backend source writer prior ∘ₛ RawCtxServerServices.publicLift))
      rw [actual]
      simp only [retained, promote, StateT.run, Functor.map_map, reassociate, Prod.map_def, id_eq]
  | inr query =>
      rcases query with query | reply | secrets | query | query <;>
        simp only [retained, PqxdhInitialNativeAudit.external,
          PqxdhInitialOccurrencePaths.handler, PqxdhInitialPendingPost.handler,
          PqxdhInitialReceiptConstruction.initial, ambient, StateT.run,
          Functor.map_map, reassociate, Prod.map_def, id_eq, Prod.eta]
      all_goals try rfl
      change (fun result => (result.1.1, result.1.2, result.2)) <$>
        (((Prod.snd <$> PqxdhInitialNativeInitializer.initial source selected previousRoot response64 secrets).run
          (state.1, state.2.1)).run state.2.2) = _
      rw [StateT.run_map, StateT.run_map]
      simp only [Functor.map_map, StateT.run]

/-- The complete source program and all outside continuation effects use the same retained interpreter as the existing installation-path proof. Only state tuple association changes. -/
theorem source_program
    (client : OracleComp (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared S B) Result)
    (state : RetainedState A N RootOracle.QueryCache) :
    Prod.map id reassociate <$> (simulateQ (retained source writer prior
      (PqxdhInitialNativeAudit.external pre application
        (PqxdhInitialNativeInitializer.initial source selected previousRoot response64) selector aux)) client).run state =
      (simulateQ (PqxdhInitialOccurrencePaths.handler source writer prior selected previousRoot response64
        (fun query => ambient (pre query)) (fun reply => ambient (application reply))
        (fun query => ambient (selector query)) (fun query => ambient (aux query))) client).run
          (reassociate state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ reassociate
    (source_step source writer prior selected previousRoot response64 pre application selector aux) client state

end BeaconcryptCore.Computational.PqxdhRetainedOccurrenceInterpreter

/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedOccurrenceInterpreter.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedOccurrenceInterpreter.source_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedOccurrenceInterpreter.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedOccurrenceInterpreter.source_program
