import BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases
import BeaconcryptCore.Computational.PqxdhInitialDisclosureState

/-!
The actual later-parent source routes aliases only in private step calls. Original initializer lookups and their optional returned kernels remain unchanged, while their audited inputs and returned chains remain in the candidate ledger. The ordinary observer has no target input; the mathematical routing interpreter is compared to it through the same masked candidate event and exact original disclosure flag.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialBeaconAmbient PqxdhInitialParentObserverCompiler PqxdhInitialParentObserver
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}
section Interpreter
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
  (output : FullOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

noncomputable def alternate (reader : RawCtxSelectedLiveTrace.Reader) :
    QueryImpl (Spec extra I D K X Response Shared) (StateT (State A N C) ProbComp)
  | .inl query => flatten (PqxdhInitialBeaconAmbient.lift
      (RawCtxSelectedParentPrivate.alternate source writer prior entry output reader
        (RawCtxSelectedParentPrivateRealization.realView source) query))
  | query => PqxdhInitialParentObserver.handler source writer prior entry output pre application initial selector aux reader query

noncomputable def handler (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput) :=
  RawCtxSelectedAliasCoupling.routed
    (PqxdhInitialParentObserver.handler source writer prior entry output pre application initial selector aux reader)
    (alternate source writer prior entry output pre application initial selector aux reader) inputs target

noncomputable def observed (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput) :=
  RawCtxFlaggedQueryTrace.trace
    (handler source writer prior entry output pre application initial selector aux reader target) inputs direct

/-- Private steps retain exact byte-alias routing; public HKDF and every original read/open/seal effect remain unchanged. -/
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

/-- Every external and initializer-audit callback is the original ordinary callback on every branch, including root aliases. -/
theorem external_same (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (query : ((External extra I D K X Response Shared) + (InitialReply →ₒ Option (PqxdhInitialPendingPost.KernelOf RatchetChain))).Domain) :
    handler source writer prior entry output pre application initial selector aux reader target (.inr query) =
      PqxdhInitialParentObserver.handler source writer prior entry output pre application initial selector aux reader (.inr query) := by
  simp [handler, RawCtxSelectedAliasCoupling.routed, alternate]

/-- The initializer audit returns the original optional kernel even when its root equals the selected input. -/
theorem audit_reply (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput) (reply : InitialReply) :
    handler source writer prior entry output pre application initial selector aux reader target (.inr (.inr reply)) = pure reply.2 := by
  rw [external_same]
  rfl

/-- The complete partial routing comparison is charged to the same ordinary final candidate event, preserving the original direct-disclosure flag and prior candidate prefix. -/
theorem distance (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (client : OracleComp (Spec extra I D K X Response Shared) Result)
    (state : (State A N C × List RootOutput) × Bool) :
    tvDist ((simulateQ (PqxdhInitialParentObserver.observed source writer prior entry output pre application initial selector aux reader) client).run state)
      ((simulateQ (observed source writer prior entry output pre application initial selector aux reader target) client).run state) ≤
      Pr[fun result => target ∈ result.2.1.2 |
        (simulateQ (PqxdhInitialParentObserver.observed source writer prior entry output pre application initial selector aux reader) client).run state].toReal :=
  RawCtxFlaggedQueryTrace.distance_vcvioLegacy
    (PqxdhInitialParentObserver.handler source writer prior entry output pre application initial selector aux reader)
    (alternate source writer prior entry output pre application initial selector aux reader)
    inputs direct target client state

/-- Native and masked readers agree for every callback that does not disclose the unavailable chain; initializer replies stay identical. -/
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
      rw [external_same, external_same]
      rcases query with (query | (reply | (secrets | (query | query)))) | reply
      all_goals rfl

/-- The complete native source event equals its masked counterpart on the unconditioned clear-bit event, without bounding candidate guesses after a permitted disclosure. -/
theorem event_good (target : RootOutput) (client : OracleComp (Spec extra I D K X Response Shared) Result)
    (state : (State A N C × List RootOutput) × Bool)
    (event : Result × ((State A N C × List RootOutput) × Bool) → Prop) :
    Pr[fun result => event result ∧ result.2.2 = false |
      (simulateQ (observed source writer prior entry output pre application initial selector aux
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target) client).run state] =
      Pr[fun result => event result ∧ result.2.2 = false |
        (simulateQ (observed source writer prior entry output pre application initial selector aux
          RawCtxSelectedLiveRead.labelRead target) client).run state] :=
  RawCtxFlaggedQueryAgreement.event_good_vcvioLegacy _ _ inputs direct
    (query_safe source writer prior entry output pre application initial selector aux target) client state event

/-- Away from the explicit parent-input collision, partial routing is exactly the patched private interpreter with every original initializer and external reply unchanged. -/
theorem handler_patch (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ entry.address) :
    handler source writer prior entry output pre application initial selector aux reader target =
      PqxdhInitialParentObserver.handler source writer (RawCtxSelectedParentPrivatePatch.privatePatch prior target output)
        entry output pre application initial selector aux reader := by
  funext query
  cases query with
  | inl query =>
      rw [old_source]
      unfold PqxdhInitialParentObserver.handler PqxdhInitialParentObserverCompiler.handler PqxdhInitialParentObserver.old
      rw [RawCtxSelectedParentPrivateRealization.handler_patch source writer prior entry target output reader
        (RawCtxSelectedParentPrivateRealization.realView source) separate]
  | inr query =>
      rw [external_same]
      rcases query with (query | (reply | (secrets | (query | query)))) | reply
      all_goals simp only [PqxdhInitialParentObserver.handler, PqxdhInitialParentObserverCompiler.handler]

/-- The complete source program is the exact patched private label interpreter with its original initializer, all optional native reads and all ambient state retained. -/
theorem compiled_source (target : RootOutput)
    (client : OracleComp (PqxdhInitialPendingPost.Spec extra RawCtxSelectedChain.Slot I D K X Response Shared S B) Result)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ entry.address) :
    simulateQ (handler source writer prior entry output pre application initial selector aux
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
      (simulateQ PqxdhInitialParentObserverCompiler.compiler client) =
      flatten (simulateQ (PqxdhInitialParentPost.labelHandler source writer
        (RawCtxSelectedParentPrivatePatch.privatePatch prior target output) entry target
        pre application (fun secrets => Prod.snd <$> initial secrets) selector aux
        (RawCtxKdfRequestTable.fullResponse output)) client) := by
  rw [handler_patch source writer prior entry output pre application initial selector aux _ target separate]
  exact PqxdhInitialParentObserver.compiled_source source writer _ entry output pre application initial selector aux target client

open PqxdhInitialDisclosureState (Base isRead Keep Rules trace_keep)
open RawCtxFamilyFreshnessProxy RawCtxSelectedChain

private theorem state_pure {T V : Type} (value : V) (state : T) :
    (pure value : StateT T ProbComp V) state = pure (value, state) := rfl

/-- Every original non-read callback compiles to a program with zero direct-disclosure queries. -/
theorem compiler_quiet (query : (Base extra I D K X Response Shared S B).Domain)
    (quiet : ¬ isRead query) :
    (PqxdhInitialParentObserverCompiler.compiler query).IsQueryBoundP
      (fun query => PqxdhInitialParentObserver.direct (extra := extra) query = true) 0 := by
  rcases query with (query | input) | (query | (reply | (secrets | (query | query))))
  · rcases query with (pending | opening) | ((pending | sealing) | (coin | (hash | view)))
    all_goals simp only [PqxdhInitialParentObserverCompiler.compiler, RawCtxFamilyPendingCompiler.live,
      RawCtxPendingFamilyLiveQueries.handler, RawCtxFamilyPendingCompiler.primitive,
      QueryImpl.compose, RawCtxPendingOwnerQueries.erase, simulateQ_spec_query,
      PqxdhInitialParentObserverCompiler.oldForward, RawCtxSelectedLiveCompiler.primitiveForward]
    all_goals exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialParentObserver.direct, RawCtxSelectedParentReadMask.direct])
  · exact False.elim (quiet trivial)
  · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialParentObserver.direct])
  · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialParentObserver.direct])
  · simp only [PqxdhInitialParentObserverCompiler.compiler, PqxdhInitialParentObserverCompiler.externalForward,
      PqxdhInitialParentObserverCompiler.audit, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [PqxdhInitialParentObserver.direct]), fun _ => ⟨Or.inl (by simp [PqxdhInitialParentObserver.direct]), fun _ => True.intro⟩⟩
  · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialParentObserver.direct])
  · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialParentObserver.direct])


variable (target : RootOutput)

noncomputable def actual : QueryImpl (Base extra I D K X Response Shared S B)
    (StateT (PqxdhInitialDisclosureState.State (PqxdhInitialParentObserver.State A N C)) ProbComp) :=
  PqxdhInitialParentPrivateObserver.observed source writer prior entry output pre application initial selector aux
    (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target ∘ₛ
      PqxdhInitialParentObserverCompiler.compiler

/-- Every non-read source callback in the actual complete audited interpreter retains the disclosure bit and all earlier candidates, including the unchanged initializer and its candidate audit. -/
theorem actual_quiet (query : (Base extra I D K X Response Shared S B).Domain)
    (quiet : ¬ isRead query) (state : PqxdhInitialDisclosureState.State (PqxdhInitialParentObserver.State A N C))
    (result : (Base extra I D K X Response Shared S B).Range query × PqxdhInitialDisclosureState.State (PqxdhInitialParentObserver.State A N C))
    (supported : result ∈ support ((actual source writer prior entry output pre application initial selector aux target query).run state)) :
    Keep state result.2 :=
  trace_keep _ _ _ _ (compiler_quiet query quiet) state result supported


private theorem actual_old_read (input : RawCtxSelectedLiveCompiler.ReadInput) :
    PqxdhInitialParentPrivateObserver.handler source writer prior entry output pre application initial selector aux
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target (.inl (.inr input)) =
      pure (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target) input.1 input.2) := by
  rw [PqxdhInitialParentPrivateObserver.old_source, RawCtxSelectedParentPrivate.read_same]
  rfl

/-- The full audited interpreter returns the original optional native family read, recording its available candidates and exact direct-disclosure bit without altering ambient state. -/
theorem actual_read (input : RawCtxFamilyFreshnessProxy.Input S B)
    (state : PqxdhInitialDisclosureState.State (PqxdhInitialParentObserver.State A N C)) :
    ((actual source writer prior entry output pre application initial selector aux target) (.inl (.inr input))).run state =
      pure (RawCtxGenericFamilyRead.nativeValue (nativeKernel (RawCtxFreshChainCut.concreteChain target)) input,
        ((state.1.1, state.1.2 ++ RawCtxSelectedLiveRead.candidates (readKind input.1) input.2), state.2 || direct input)) := by
  rcases input with ⟨request, kernel⟩
  cases request <;> cases kernel
  all_goals simp only [actual, QueryImpl.compose, PqxdhInitialParentObserverCompiler.compiler,
    RawCtxFamilyPendingCompiler.live, RawCtxPendingFamilyLiveQueries.handler, RawCtxFamilyReadCompiler.compiler,
    simulateQ_pure, simulateQ_spec_query, PqxdhInitialParentObserverCompiler.oldForward,
    PqxdhInitialParentPrivateObserver.observed, RawCtxFlaggedQueryTrace.trace,
    actual_old_read source writer prior entry output pre application initial selector aux target,
    StateT.run, state_pure, pure_bind]
  all_goals simp [RawCtxGenericFamilyRead.nativeValue, nativeKernel, RawCtxSelectedLiveTrace.nativeReader,
    RawCtxSelectedLiveRead.nativeRead, RawCtxSelectedLiveRead.candidates, readKind, RawCtxFamilyFreshnessProxy.direct,
    RawCtxSelectedLiveRead.exposed, RawCtxSelectedLiveRead.labelRead, RawCtxSelectedLiveRead.replyInputs,
    PqxdhInitialParentObserver.inputs, PqxdhInitialParentObserver.direct,
    RawCtxSelectedLiveCompiler.inputs, RawCtxSelectedParentReadMask.direct,
    RawCtxChainInterpretation.mapChains, interpret]

/-- The actual full partial-routing interpreter discharges every callback law needed by the original post history proof. -/
theorem actual_rules : Rules target (actual (S := S) (B := B) source writer prior entry output pre application initial selector aux target) :=
  ⟨actual_quiet source writer prior entry output pre application initial selector aux target,
    actual_read source writer prior entry output pre application initial selector aux target⟩


end Interpreter
end BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.old_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.old_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.external_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.external_same

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.audit_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.audit_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.distance

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.query_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.event_good

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.handler_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.handler_patch

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.compiled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.compiled_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.compiler_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.compiler_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.actual_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.actual_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.actual_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.actual_read

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.actual_rules' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver.actual_rules
