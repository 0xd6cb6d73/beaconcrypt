import BeaconcryptCore.Computational.PqxdhInitialParentObserver

/-!
The later-parent comparison routes both known private step inputs and actual initializer roots through one supplied full76 response. Initializer routing occurs after the unchanged root lookup, at the explicit typed audit callback, so it can preserve the shared64-byte prefix without secretly learning a root before the lookup. The ordinary observer has no selected-input argument. The mathematical routed interpreter and its full-state distance are charged to the original final candidate event; no alias probability is assumed small here.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialBeaconAmbient PqxdhInitialParentObserverCompiler PqxdhInitialParentObserver
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

noncomputable def patched (output : FullOutput) (reply : InitialReply) : Option (PqxdhInitialPendingPost.KernelOf RatchetChain) :=
  reply.2.map (fun _ => (PqxdhInitialSelectedBeacon.normalize (initialPrefix output)).refined)

section Interpreter
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
  (output : FullOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

noncomputable def alternate (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput) :
    QueryImpl (Spec extra I D K X Response Shared) (StateT (State A N C) ProbComp)
  | .inl query => flatten (PqxdhInitialBeaconAmbient.lift
      (RawCtxSelectedParentPrivate.alternate source writer prior entry output reader
        (RawCtxSelectedParentPrivateRealization.realView source) query))
  | .inr (.inr reply) => pure (if target = reply.1 then patched output reply else reply.2)
  | query => PqxdhInitialParentObserver.handler source writer prior entry output pre application initial selector aux reader query

noncomputable def handler (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput) :=
  RawCtxSelectedAliasCoupling.routed
    (PqxdhInitialParentObserver.handler source writer prior entry output pre application initial selector aux reader)
    (alternate source writer prior entry output pre application initial selector aux reader target) inputs target

noncomputable def observed (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput) :=
  RawCtxFlaggedQueryTrace.trace
    (handler source writer prior entry output pre application initial selector aux reader target) inputs direct

/-- The actual audited input controls initializer prefix routing; failed initialization remains failed and the complete ambient state is unchanged. -/
theorem audit_route (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput) (reply : InitialReply) :
    handler source writer prior entry output pre application initial selector aux reader target (.inr (.inr reply)) =
      pure (if target = reply.1 then patched output reply else reply.2) := by
  by_cases same : target = reply.1
  · subst target
    simp [handler, RawCtxSelectedAliasCoupling.routed, inputs, candidates, alternate]
  · by_cases hit : target ∈ candidates reply
    all_goals simp [handler, RawCtxSelectedAliasCoupling.routed, inputs, hit, alternate, same,
      PqxdhInitialParentObserver.handler, PqxdhInitialParentObserverCompiler.handler, flatten_pure]

/-- Every old private step, public evaluation and optional read is exactly the established private-only alias interpreter inside the complete ambient state. -/
theorem old_source (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (query : RawCtxSelectedLiveCompiler.Spec.Domain) :
    handler source writer prior entry output pre application initial selector aux reader target (.inl query) =
      flatten (PqxdhInitialBeaconAmbient.lift
        (RawCtxSelectedParentPrivate.handler source writer prior entry output reader
          (RawCtxSelectedParentPrivateRealization.realView source) target query)) := by
  by_cases hit : target ∈ RawCtxSelectedLiveCompiler.inputs query
  all_goals simp [handler, RawCtxSelectedAliasCoupling.routed, inputs, hit, alternate,
    RawCtxSelectedParentPrivate.handler, PqxdhInitialParentObserver.handler,
    PqxdhInitialParentObserverCompiler.handler, PqxdhInitialParentObserver.old]

/-- The original initializer lookup and full cache effects finish before any alias routing; no target value is supplied to that original service. -/
theorem initial_lookup (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets Shared) :
    handler source writer prior entry output pre application initial selector aux reader target
      (.inr (.inl (.inr (.inr (.inl secrets))))) = flatten (initial secrets) := by
  simp [handler, RawCtxSelectedAliasCoupling.routed, inputs, PqxdhInitialParentObserver.handler,
    PqxdhInitialParentObserverCompiler.handler]

noncomputable def routedInitial (target : RootOutput) (secrets : PqxdhBeaconPhase2Shared.Secrets Shared) :
    Ambient A N C (Option (PqxdhInitialPendingPost.KernelOf RatchetChain)) := do
  let reply ← initial secrets
  pure (if target = reply.1 then patched output reply else reply.2)

/-- The compiled initializer is exactly original lookup followed by the shared-prefix replacement on a recorded root hit, before the source uses its known kernel. -/
theorem initial_source (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets Shared) :
    simulateQ (handler source writer prior entry output pre application initial selector aux reader target)
      (PqxdhInitialParentObserverCompiler.compiler (S := S) (B := B) (.inr (.inr (.inr (.inl secrets))))) =
      Option.map RawCtxSelectedFamilyContext.knownKernel <$>
        flatten (routedInitial output initial target secrets) := by
  have first : simulateQ (handler source writer prior entry output pre application initial selector aux reader target)
      (externalForward (.inr (.inr (.inl secrets)))) = flatten (initial secrets) := by
    exact (simulateQ_spec_query _ _).trans (initial_lookup source writer prior entry output pre application initial selector aux reader target secrets)
  have next : ∀ reply, simulateQ (handler source writer prior entry output pre application initial selector aux reader target)
      (audit reply) = pure (if target = reply.1 then patched output reply else reply.2) := by
    intro reply
    exact (simulateQ_spec_query _ _).trans (audit_route source writer prior entry output pre application initial selector aux reader target reply)
  change simulateQ _ ((externalForward (.inr (.inr (.inl secrets))) : OracleComp (Spec extra I D K X Response Shared) InitialReply) >>=
    fun reply => audit reply >>= fun kernel => pure (Option.map RawCtxSelectedFamilyContext.knownKernel kernel)) = _
  simp only [simulateQ_bind, first, next, simulateQ_pure, pure_bind,
    routedInitial, flatten_bind, flatten_pure, map_bind, map_pure]
  rfl

/-- Routing across the entire original post interface is charged once to its original complete candidate event, retaining prior candidates and the direct-read flag. -/
theorem distance (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (client : OracleComp (Spec extra I D K X Response Shared) Result)
    (state : (State A N C × List RootOutput) × Bool) :
    tvDist ((simulateQ (PqxdhInitialParentObserver.observed source writer prior entry output pre application initial selector aux reader) client).run state)
      ((simulateQ (observed source writer prior entry output pre application initial selector aux reader target) client).run state) ≤
      Pr[fun result => target ∈ result.2.1.2 |
        (simulateQ (PqxdhInitialParentObserver.observed source writer prior entry output pre application initial selector aux reader) client).run state].toReal :=
  RawCtxFlaggedQueryTrace.distance
    (PqxdhInitialParentObserver.handler source writer prior entry output pre application initial selector aux reader)
    (alternate source writer prior entry output pre application initial selector aux reader target)
    inputs direct target client state

/-- Every public HKDF projection remains the actual fixed public computation, including a successful guess of a patched private input. -/
theorem public_real (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (query : JointKdfViewQuery) :
    handler source writer prior entry output pre application initial selector aux reader target
      (.inl (.inl (.inr (.inr (.inr (.inr query)))))) =
      pure (query.project (PqxdhJointKdf.productionStream source.crypto query.address)) := by
  rw [old_source, RawCtxSelectedParentPrivate.public_real]
  rfl

noncomputable def routedOld (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput) :
    QueryImpl RawCtxSelectedLiveCompiler.Spec (Ambient A N C) :=
  fun query => PqxdhInitialBeaconAmbient.lift (RawCtxSelectedParentPrivate.handler source writer prior entry output reader
    (RawCtxSelectedParentPrivateRealization.realView source) target query)

noncomputable def sourceHandler (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput) :
    QueryImpl (PqxdhInitialPendingPost.Spec extra RawCtxSelectedChain.Slot I D K X Response Shared S B) (Ambient A N C) :=
  PqxdhInitialPendingPost.handler
    (routedOld source writer prior entry output reader target ∘ₛ RawCtxFamilyPendingCompiler.primitive)
    (routedOld source writer prior entry output reader target ∘ₛ RawCtxFamilyReadCompiler.compiler)
    pre application (fun secrets => Option.map RawCtxSelectedFamilyContext.knownKernel <$>
      routedInitial output initial target secrets) selector aux

private theorem flatten_map {α β : Type} (f : α → β) (work : Ambient A N C α) :
    flatten (f <$> work) = f <$> flatten work := by
  simp only [← bind_pure_comp, flatten_bind, flatten_pure]

private theorem compiler_source (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (query : (PqxdhInitialPendingPost.Spec extra RawCtxSelectedChain.Slot I D K X Response Shared S B).Domain) :
    simulateQ (handler source writer prior entry output pre application initial selector aux reader target)
      (PqxdhInitialParentObserverCompiler.compiler query) =
      flatten (sourceHandler source writer prior entry output pre application initial selector aux reader target query) := by
  have oldEquation : handler source writer prior entry output pre application initial selector aux reader target ∘ₛ oldForward =
      (fun query => flatten (routedOld source writer prior entry output reader target query)) := by
    funext oldQuery
    exact (simulateQ_spec_query _ _).trans (old_source source writer prior entry output pre application initial selector aux reader target oldQuery)
  rcases query with query | (query | (reply | (secrets | (query | query))))
  · simp only [PqxdhInitialParentObserverCompiler.compiler, ← QueryImpl.simulateQ_compose, oldEquation, flatten_program]
    cases query <;> rfl
  · simp [PqxdhInitialParentObserverCompiler.compiler, externalForward,
      handler, RawCtxSelectedAliasCoupling.routed, inputs, PqxdhInitialParentObserver.handler,
      PqxdhInitialParentObserverCompiler.handler, sourceHandler, PqxdhInitialPendingPost.handler]
  · simp [PqxdhInitialParentObserverCompiler.compiler, externalForward,
      handler, RawCtxSelectedAliasCoupling.routed, inputs, PqxdhInitialParentObserver.handler,
      PqxdhInitialParentObserverCompiler.handler, sourceHandler, PqxdhInitialPendingPost.handler]
  · rw [initial_source, ← flatten_map]
    rfl
  · simp [PqxdhInitialParentObserverCompiler.compiler, externalForward,
      handler, RawCtxSelectedAliasCoupling.routed, inputs, PqxdhInitialParentObserver.handler,
      PqxdhInitialParentObserverCompiler.handler, sourceHandler, PqxdhInitialPendingPost.handler]
  · simp [PqxdhInitialParentObserverCompiler.compiler, externalForward,
      handler, RawCtxSelectedAliasCoupling.routed, inputs, PqxdhInitialParentObserver.handler,
      PqxdhInitialParentObserverCompiler.handler, sourceHandler, PqxdhInitialPendingPost.handler]

/-- The complete actual pending program runs the same private step routing and root-audited initializer prefix routing, with all original external effects and cache state retained. -/
theorem compiled_source (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (client : OracleComp (PqxdhInitialPendingPost.Spec extra RawCtxSelectedChain.Slot I D K X Response Shared S B) Result) :
    simulateQ (handler source writer prior entry output pre application initial selector aux reader target)
      (simulateQ PqxdhInitialParentObserverCompiler.compiler client) =
      flatten (simulateQ (sourceHandler source writer prior entry output pre application initial selector aux reader target) client) := by
  have step : handler source writer prior entry output pre application initial selector aux reader target ∘ₛ
      PqxdhInitialParentObserverCompiler.compiler (S := S) (B := B) =
      (fun query => flatten (sourceHandler source writer prior entry output pre application initial selector aux reader target query)) :=
    funext (compiler_source (S := S) (B := B) source writer prior entry output pre application initial selector aux reader target)
  rw [← QueryImpl.simulateQ_compose, step, flatten_program]

/-- The fully routed source callback still agrees with its target-free reader outside the same actual hidden-chain disclosure flag. -/
theorem query_safe (target : RootOutput) (query : (Spec extra I D K X Response Shared).Domain)
    (safe : direct query = false) :
    handler source writer prior entry output pre application initial selector aux
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target query =
      handler source writer prior entry output pre application initial selector aux
        RawCtxSelectedLiveRead.labelRead target query := by
  cases query with
  | inl query =>
      simp only [old_source]
      rcases query with ((pending | opening) | ((pending | sealing) | (coin | (hash | view)))) | read
      all_goals try rfl
      simp only [RawCtxSelectedParentPrivate.read_same]
      exact congrArg (fun value => flatten (PqxdhInitialBeaconAmbient.lift (pure value)))
        (RawCtxSelectedLiveRead.before_exposure read.1 (RawCtxFreshChainCut.concreteChain target) read.2 safe)
  | inr query =>
      rcases query with (query | (reply | (secrets | (query | query)))) | reply
      all_goals rfl

/-- The complete routed native event equals its masked counterpart on the unconditioned clear-bit event; initializer root routing and all candidate entries remain the same. -/
theorem event_good (target : RootOutput) (client : OracleComp (Spec extra I D K X Response Shared) Result)
    (state : (State A N C × List RootOutput) × Bool)
    (event : Result × ((State A N C × List RootOutput) × Bool) → Prop) :
    Pr[fun result => event result ∧ result.2.2 = false |
      (simulateQ (observed source writer prior entry output pre application initial selector aux
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target) client).run state] =
      Pr[fun result => event result ∧ result.2.2 = false |
        (simulateQ (observed source writer prior entry output pre application initial selector aux
          RawCtxSelectedLiveRead.labelRead target) client).run state] :=
  RawCtxFlaggedQueryAgreement.event_good _ _ inputs direct
    (query_safe source writer prior entry output pre application initial selector aux target) client state event

end Interpreter
end BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.audit_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.audit_route
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.old_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.old_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.initial_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.initial_lookup
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.initial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.initial_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.distance
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.public_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.public_real
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.compiled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.compiled_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.query_safe
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases.event_good
