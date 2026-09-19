import BeaconcryptCore.Computational.PqxdhInitialNativeRetained
import BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw
import BeaconcryptCore.Computational.PqxdhInitialNativeBudgets

/-!
The full original pending interface supports the same single remaining private child draw while retaining every external preparation, initializer, application, selector and publication effect. A literal compiler exposes only the existing private KDF endpoint to the generic single-draw theorem. The final projection removes completed private table/cursor/log instrumentation and retains the complete result and Shared/N/root-cache state. The early full76 comparison draw is separately billed.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhInitialNativeLog PqxdhInitialBeaconAmbient
open RawCtxSelectiveChainGame RawCtxSelectedParentTable PqxdhInitialNativeRetained
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Other (extra : OracleSpec ι) (I D K X Response Shared : Type) :=
  RawCtxServerServices.BackendSpec + External extra RatchetChain I D K X Response Shared

abbrev Flat (extra : OracleSpec ι) (I D K X Response Shared : Type) := Other extra I D K X Response Shared + JointKdfRO

noncomputable def other (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C)) :
    QueryImpl (Other extra I D K X Response Shared) (StateT (RetainedState A N C) ProbComp)
  | .inl query => fun state =>
      (fun result => (result.1, (result.2, state.2))) <$> (RawCtxProtocolBackend.backend source writer query).run state.1
  | .inr query => fun state =>
      (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
        ((external query (state.1, state.2.1)).run state.2.2)

def liveForward : QueryImpl RawCtxSelectiveKdfFamily.FamilySpec (OracleComp (Flat extra I D K X Response Shared))
  | .inl query => (Flat extra I D K X Response Shared).query (.inl (.inl query))
  | .inr query => (Flat extra I D K X Response Shared).query (.inr query)

noncomputable def compiler : QueryImpl (Spec extra RatchetChain I D K X Response Shared S B)
    (OracleComp (Flat extra I D K X Response Shared))
  | .inl query => simulateQ liveForward (RawCtxPendingRetainedExecution.compiler query)
  | .inr query => (Flat extra I D K X Response Shared).query (.inl (.inr query))

def pack (state : Bare A N C) : RetainedState A N C × Store := ((state.1.1, state.2), state.1.2)

private theorem live_selective (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp RawCtxSelectiveKdfFamily.FamilySpec Result)
    (state : RawCtxPendingSelectiveFamily.State A) (privateState : N × C) :
    (simulateQ (RawCtxSelectiveChainGame.handler source stage (other source writer external))
      (simulateQ liveForward client)).run ((state.1, privateState), state.2) =
    (fun result => (result.1, ((result.2.1, privateState), result.2.2))) <$>
      (simulateQ (RawCtxSelectiveChainGame.handler source stage (RawCtxProtocolBackend.backend source writer)) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
    cases query with
    | inl query =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, liveForward,
        RawCtxSelectiveChainGame.handler, other]
      simp only [StateT.run, bind_map_left, map_bind, bind_assoc, pure_bind]
      exact bind_congr fun reply => ih reply.1 (reply.2, state.2)
    | inr query =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, liveForward,
        RawCtxSelectiveChainGame.handler]
      simp only [StateT.run, map_bind, bind_assoc, pure_bind]
      exact bind_congr fun reply => ih reply.1 (state.1, reply.2)


/-- Flattening the full actual callback preserves every state field and original reply while exposing only the existing private KDF endpoint. -/
theorem bare_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : Bare A N C) :
    (simulateQ (RawCtxSelectiveChainGame.handler source stage (other source writer external)) (compiler query)).run (pack state) =
      (fun result => (result.1, pack result.2)) <$> (bare source writer stage external query).run state := by
  cases query with
  | inl query =>
    have lifted := live_selective source writer stage external (RawCtxPendingRetainedExecution.compiler query) state.1 state.2
    have actual := congrFun (RawCtxPendingBackendInterpretation.family_compose
      (RawCtxSelectiveChainGame.handler source stage (RawCtxProtocolBackend.backend (Auxiliary := A) source writer))
      RawCtxSelectiveKdfFamily.compiler) query
    change simulateQ _ (RawCtxPendingRetainedExecution.compiler query) =
      RawCtxPendingSelectiveFamily.handler source writer stage query at actual
    rw [actual] at lifted
    simpa only [compiler, pack, bare, StateT.run, bind_pure_comp, Functor.map_map] using lifted
  | inr query =>
    simp only [compiler, simulateQ_spec_query, RawCtxSelectiveChainGame.handler, other, pack, bare,
      liftExternal, StateT.run, bind_pure_comp, Functor.map_map]
    rfl


/-- The literal full source program flattens with its entire private table, cursor and all ambient fields still present. -/
theorem bare_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result) (state : Bare A N C) :
    (simulateQ (RawCtxSelectiveChainGame.handler source stage (other source writer external))
      (simulateQ compiler client)).run (pack state) =
    (fun result => (result.1, pack result.2)) <$> (simulateQ (bare source writer stage external) client).run state := by
  rw [← QueryImpl.simulateQ_compose]
  exact (program_project (bare source writer stage external)
    (fun _ : Unit => RawCtxSelectiveChainGame.handler source stage (other source writer external) ∘ₛ compiler)
    (fun _ => ()) pack (fun query state => (bare_step source writer stage external query state).symm)
    (fun _ _ _ _ => rfl) client state).symm


private theorem live_retained (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp RawCtxSelectiveKdfFamily.FamilySpec Result)
    (state : RawCtxSharedPrimitive.SharedState A) (privateState : N × C) :
    (simulateQ (RawCtxRetainedTable.viewImpl prior (other source writer external))
      (simulateQ liveForward client)).run (state, privateState) =
    (fun result => (result.1, (result.2, privateState))) <$>
      (simulateQ (RawCtxRetainedTable.viewImpl prior (RawCtxProtocolBackend.backend source writer)) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
    cases query with
    | inl query =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, liveForward,
        RawCtxRetainedTable.viewImpl, other]
      simp only [StateT.run, bind_map_left, map_bind]
      exact bind_congr fun reply => ih reply.1 reply.2
    | inr query =>
      simp only [simulateQ_bind, simulateQ_spec_query, liveForward, RawCtxRetainedTable.viewImpl, pure_bind]
      exact ih (prior query) state


/-- The same complete compiler under a retained private lookup is exactly the original full retained interpreter, including its external effects. -/
theorem retained_compiler (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C)) :
    RawCtxRetainedTable.viewImpl prior (other source writer external) ∘ₛ (compiler (S := S) (B := B)) =
      retained source writer prior external := by
  funext query state
  cases query with
  | inl query =>
    have lifted := live_retained source writer prior external (RawCtxPendingRetainedExecution.compiler query) state.1 state.2
    have actual := congrFun (RawCtxPendingBackendInterpretation.family_compose
      (RawCtxRetainedTable.viewImpl prior (RawCtxProtocolBackend.backend (Auxiliary := A) source writer))
      RawCtxSelectiveKdfFamily.compiler) query
    change simulateQ _ (RawCtxPendingRetainedExecution.compiler query) =
      RawCtxPendingRetainedExecution.retained source writer prior query at actual
    rw [actual] at lifted
    exact lifted
  | inr query =>
    simp only [QueryImpl.apply_compose, compiler, simulateQ_spec_query, RawCtxRetainedTable.viewImpl, other, retained]


/-- A single remaining child draw may be sampled before the complete original full-interface continuation while preserving its full result and ambient state. -/
theorem bare_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result) (state : Bare A N C)
    (missing : state.1.2.1 (cursorAddress state.1.2.2) = none) :
    𝒟[(fun result => (result.1, (result.2.1.1, result.2.2))) <$>
      (simulateQ (bare source writer (state.1.2.2.depth + 1) external) client).run state] =
    𝒟[($ᵗ FullOutput) >>= fun output =>
      (simulateQ (retained source writer (view (productionStream source.crypto)
        (state.1.2.1.cacheQuery (cursorAddress state.1.2.2) output)) external) client).run (state.1.1, state.2)] := by
  have actual := RawCtxSelectiveSingleDraw.single_uniform source (other source writer external)
    (simulateQ compiler client) (state.1.1, state.2) state.1.2.1 state.1.2.2 missing
  simp only [Prod.eta] at actual
  have flattened := bare_program source writer (state.1.2.2.depth + 1) external client state
  dsimp only [pack] at flattened
  rw [flattened] at actual
  simpa only [Functor.map_map, pack, ← QueryImpl.simulateQ_compose, retained_compiler] using actual


/-- The full original logged source has the same single-child distribution after projecting only completed private table, cursor and log; all original results, Shared/N and root-cache effects remain. -/
theorem logged_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : PqxdhInitialNativeLog.State A N C)
    (missing : state.1.1.2.1 (cursorAddress state.1.1.2.2) = none) :
    𝒟[(fun result => (result.1, PqxdhInitialNativeRetained.project result.2)) <$>
      (simulateQ (PqxdhInitialNativeLog.handler source writer (state.1.1.2.2.depth + 1) external) client).run state] =
    𝒟[($ᵗ FullOutput) >>= fun output =>
      (simulateQ (retained source writer (view (productionStream source.crypto)
        (state.1.1.2.1.cacheQuery (cursorAddress state.1.1.2.2) output)) external) client).run (PqxdhInitialNativeRetained.project state)] := by
  have erased := congrArg (fun work : ProbComp (Result × Bare A N C) =>
    (fun result => (result.1, (result.2.1.1, result.2.2))) <$> work)
    (program_projection source writer (state.1.1.2.2.depth + 1) external client state)
  have complete : (fun result => (result.1, PqxdhInitialNativeRetained.project result.2)) <$>
      (simulateQ (PqxdhInitialNativeLog.handler source writer (state.1.1.2.2.depth + 1) external) client).run state =
      (fun result => (result.1, (result.2.1.1, result.2.2))) <$>
        (simulateQ (bare source writer (state.1.1.2.2.depth + 1) external) client).run (erase state) := by
    simpa only [Functor.map_map, PqxdhInitialNativeRetained.project, erase, Prod.map_def, id_eq] using erased
  exact (congrArg evalDist complete).trans (bare_uniform source writer external client (erase state) missing)


set_option maxRecDepth 2048 in
/-- The early comparison execution pays its own full76 draw and the original all-reply callback ledger; no cost is transported through the evaluated single-draw equality. -/
theorem early_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (budget : PqxdhInitialNativeBudgets.ExternalBudget)
    (callbacks : PqxdhInitialNativeBudgets.LocalBounds external budget)
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (queries : Nat) (sourceBound : client.IsTotalQueryBound queries) (state : PqxdhInitialNativeLog.State A N C) :
    (($ᵗ FullOutput) >>= fun output =>
      (simulateQ (retained source writer (view (productionStream source.crypto)
        (state.1.1.2.1.cacheQuery (cursorAddress state.1.1.2.2) output)) external) client).run
          (PqxdhInitialNativeRetained.project state)).IsTotalQueryBound
      (76 + queries * PqxdhInitialNativeBudgets.callbackCap budget) := by
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
  intro output
  let recorded : PqxdhInitialNativeLog.State A N C :=
    (((state.1.1.1, (state.1.1.2.1.cacheQuery (cursorAddress state.1.1.2.2) output, state.1.1.2.2)), state.1.2), state.2)
  have bounded := PqxdhInitialNativeBudgets.program_uniform source writer 0 external budget callbacks client queries sourceBound recorded
  have projected := (isQueryBound_map_iff _
    (fun result : Result × PqxdhInitialNativeLog.State A N C => (result.1, PqxdhInitialNativeRetained.project result.2)) _ _ _).mpr bounded
  rw [retained_run source writer 0 external client recorded (Nat.zero_le _)] at projected
  exact projected

end BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw


/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.bare_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.bare_step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.bare_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.bare_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.retained_compiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.retained_compiler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.bare_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.bare_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.logged_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.logged_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.early_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw.early_uniform
