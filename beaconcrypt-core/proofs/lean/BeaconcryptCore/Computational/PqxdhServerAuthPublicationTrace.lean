import BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt

/-! Exact optional builder replies are retained as private observations. Successful inner frame writing and successful outer response writing remain separate; observing either callback does not repeat it or alter its state. This module adds no publication-security assumption. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace
open PqxdhServerAuthBuildProgram (Spec Log)
open PqxdhServerAuthExperiment (Codec Checks)
open PqxdhJointKdfGame

/-- An outer `none` records component refusal; `some none` retains native optional rejection, including a reached writer failure. The original arguments and complete actual optional result are retained. -/
inductive Event where
  | seal (pending : PqxdhServerAuthCtxSend.Pending)
      (reply : Option (Option RawCtxSourceSend.Encrypted))
  | write (fields : PqxdhServerRegistrationPublication.ResponseFields)
      (reply : Option (Option Pqxdh.Bytes))

abbrev Trace := List Event
abbrev State := Log × Trace
abbrev Compiler := OptionT (PqxdhServerAuthCtxNative.Local State)

/-- Record only the reached send and outer writer callbacks. Allocation, erasure and identity checks still execute, with their original replies and effects. -/
def observation (query : Spec.Domain) : Option (Spec.Range query) → Option Event :=
  match query with
  | .inl pending => fun reply => some (.seal pending reply)
  | .inr (.write fields) => fun reply => some (.write fields reply)
  | .inr _ => fun _ => none

/-- Chronological append preserves repeated identical observations as distinct source occurrences. -/
def record (query : Spec.Domain) (reply : Option (Spec.Range query)) (trace : Trace) : Trace :=
  trace ++ (observation query reply).toList

/-- Erase only the new observations, retaining the original complete reply and successful-seal log. -/
def project {Result : Type} (result : Option Result × State) : Option Result × Log :=
  (result.1, result.2.1)

/-- Observe an optional stateful query after its actual execution, preserving refusal and the complete original state. The callback chooses only the new private annotation. -/
def observe {ι : Type} {spec : OracleSpec ι} {S E : Type}
    {m : Type → Type} [Monad m]
    (handler : QueryImpl spec (OptionT (StateT S m)))
    (event : (query : spec.Domain) → Option (spec.Range query) → Option E) :
    QueryImpl spec (OptionT (StateT (S × List E) m)) :=
  fun query => OptionT.mk fun state =>
    (fun result => (result.1, (result.2, state.2 ++ (event query result.1).toList))) <$>
      (handler query).run.run state.1

/-- Erasing the private receipt list preserves the complete optional adaptive continuation and the original state, including a final refusal. -/
theorem observe_program {ι Result S E : Type} {spec : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl spec (OptionT (StateT S m)))
    (event : (query : spec.Domain) → Option (spec.Range query) → Option E)
    (client : OracleComp spec Result) (state : S × List E) :
    Prod.map id Prod.fst <$> ((simulateQ (observe handler event) client).run.run state) =
      (simulateQ handler client).run.run state.1 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, map_pure, Prod.map, id_eq]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind,
        Option.elimM, StateT.run_bind]
      simp only [observe, OptionT.run_mk, StateT.run, map_bind, bind_map_left]
      refine bind_congr fun ⟨reply, after⟩ => ?_
      cases reply with
      | none =>
          change Prod.map id Prod.fst <$>
            (pure (none, (after, state.2 ++ (event query none).toList)) :
              m (Option Result × (S × List E))) = pure (none, after)
          simp only [map_pure, Prod.map, id_eq]
      | some value => exact ih value (after, state.2 ++ (event query (some value)).toList)

variable {Reader WireResponse : Type}

/-- The literal executable compiler is run once before its optional reply is observed. No selected-key parameter or component cache is given to the observation code. -/
noncomputable def compiler (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) : QueryImpl Spec Compiler :=
  observe (PqxdhServerAuthBuildProgram.compiler source codec checks) observation

/-- Observe the actual complete concrete builder, including all native optional and diagnostic outcomes. -/
noncomputable def compiled (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    {Metadata PeerMetadata Consumed : Type} (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :=
  simulateQ (compiler source codec checks)
    (PqxdhServerAuthBuildProgram.program source rest pending data metadata state)

/-- Every observed query erases to the identical original query program and full original local result. -/
theorem query_erase (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (query : Spec.Domain) (state : State) :
    project <$> (compiler source codec checks query).run.run state =
      (PqxdhServerAuthBuildProgram.compiler source codec checks query).run.run state.1 := by
  simp only [compiler, observe, OptionT.run_mk, StateT.run, Functor.map_map]
  change id <$> _ = _
  exact id_map _

/-- The observed sealing callback executes the unchanged dynamic sealer once, retains its actual nested optional reply, and records success only where the source itself appends its seal context. -/
theorem seal_run (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (pending : PqxdhServerAuthCtxSend.Pending) (before : State) :
    (compiler source codec checks (.inl pending)).run.run before =
      (fun result => (result, ((match result with
        | some (some _) => before.1 ++ [pending.context]
        | _ => before.1), before.2 ++ [.seal pending result]))) <$>
        RawCtxSelectedSealConsumer.sealing source.crypto codec.frameWrite
          (PqxdhServerAuthCtxSend.sealing pending) := by
  change (fun result => (result.1, (result.2, before.2 ++ [.seal pending result.1]))) <$>
    (PqxdhServerAuthBuildProgram.sealer source codec.frameWrite pending).run.run before.1 = _
  rw [PqxdhServerAuthBuildProgram.sealer_run, Functor.map_map]
  rfl

/-- The actual outer writer's complete optional reply is recorded separately from the sealer; the callback cannot change the earlier successful-seal log. -/
theorem write_run (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (fields : PqxdhServerRegistrationPublication.ResponseFields) (before : State) :
    (compiler source codec checks (.inr (.write fields))).run.run before =
      pure (some (codec.write2 fields), (before.1,
        before.2 ++ [.write fields (some (codec.write2 fields))])) := by
  simp [compiler, observe, PqxdhServerAuthBuildProgram.compiler,
    PqxdhServerAuthBuildProgram.impl, PqxdhServerAuthCtxNative.aux, observation, StateT.run]
  rfl

/-- The whole observed builder erases to the unchanged executable source compiler, including its complete optional native result and original seal log. No selected-key, success or freshness premise is needed. -/
theorem compiled_erase (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    {Metadata PeerMetadata Consumed : Type} (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (before : State) :
    project <$> (compiled source codec checks rest pending data metadata state).run.run before =
      (PqxdhServerAuthBuildProgram.compiled source codec checks rest pending data metadata state).run.run before.1 :=
  observe_program (PqxdhServerAuthBuildProgram.compiler source codec checks) observation _ before

/-- Adding private callback observations preserves every source component query certificate exactly; it adds neither queries nor an unbilled callback. -/
theorem compiled_bound_iff (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    {Metadata PeerMetadata Consumed : Type} (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (before : State)
    (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    ((compiled source codec checks rest pending data metadata state).run.run before).IsQueryBoundP predicate bound ↔
      ((PqxdhServerAuthBuildProgram.compiled source codec checks rest pending data metadata state).run.run before.1).IsQueryBoundP predicate bound := by
  rw [← compiled_erase source codec checks rest pending data metadata state before, isQueryBoundP_map_iff]

/-- The caller supplies an occurrence coordinate; this annotation does not infer it from keys, frames or byte equality. A completed trailer is emitted before the original API reply is returned, including an optional component refusal. -/
inductive Annotation where
  | beginBuild (coordinate : Nat)
  | completedBuild (coordinate : Nat) (events : Trace)

abbrev AnnotatedSpec := AdaptiveCtxDynamicKnownKeys.Spec + (Annotation →ₒ Unit)

def liftDynamic : QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (OracleComp AnnotatedSpec) :=
  fun query => AnnotatedSpec.query (.inl query)

/-- Private annotations return only Unit. Erasure forwards every dynamic component query unchanged. -/
def erase : QueryImpl AnnotatedSpec (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)
  | .inl query => AdaptiveCtxDynamicKnownKeys.Spec.query query
  | .inr _ => pure ()

/-- Lifting the original component program to the annotated interface and erasing annotations preserves every adaptive reply and continuation. -/
theorem erase_lift {Result : Type} (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    simulateQ erase (simulateQ liftDynamic work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : erase ∘ₛ liftDynamic = QueryImpl.id' AdaptiveCtxDynamicKnownKeys.Spec := by
    funext query
    simp only [QueryImpl.apply_compose, liftDynamic, simulateQ_spec_query, erase, QueryImpl.id']
    rfl
  rw [same, simulateQ_id']

/-- Private begin/end annotations bracket the actual builder execution. The completed trailer is emitted even when the native result or component result is absent; the caller receives the unchanged optional result and source seal log. -/
noncomputable def annotated (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual)
    (coordinate : Nat) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    {Metadata PeerMetadata Consumed : Type} (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (before : Log) :
    OracleComp AnnotatedSpec (Option (RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)) × Log) := do
  let _ ← AnnotatedSpec.query (.inr (.beginBuild coordinate))
  let outcome ← simulateQ liftDynamic
    ((compiled source codec checks rest pending data metadata state).run.run (before, []))
  let _ ← AnnotatedSpec.query (.inr (.completedBuild coordinate outcome.2.2))
  pure (project outcome)

/-- Erasing both private annotations recovers the literal complete builder, not just its marginal return distribution. All component queries, optional results and original seal-log changes are retained. -/
theorem annotated_erase (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual)
    (coordinate : Nat) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    {Metadata PeerMetadata Consumed : Type} (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (before : Log) :
    simulateQ erase (annotated source codec checks rest coordinate pending data metadata state before) =
      (PqxdhServerAuthBuildProgram.compiled source codec checks rest pending data metadata state).run.run before := by
  simp only [annotated, simulateQ_bind, simulateQ_spec_query, erase, pure_bind,
    erase_lift, simulateQ_map, map_pure, bind_pure_comp]
  exact compiled_erase source codec checks rest pending data metadata state (before, [])

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.observe_program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.observe_program

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.query_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.seal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.seal_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.write_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.write_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.compiled_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.compiled_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.compiled_bound_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.compiled_bound_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.erase_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.erase_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.annotated_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace.annotated_erase
