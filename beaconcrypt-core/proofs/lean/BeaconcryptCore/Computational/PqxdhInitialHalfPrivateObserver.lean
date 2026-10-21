import BeaconcryptCore.Computational.PqxdhInitialHalfObserver
import BeaconcryptCore.Computational.PqxdhInitialDisclosureState

/-!
The first-half source uses exact byte-alias routing only for private ratchet steps. Matching initializer requests keep their original hidden-half kernels; all external callbacks and their audited optional replies stay unchanged, including initializer-root aliases. The same actual candidate ledger bounds the ordinary masked comparison, and the literal original read/history interpreter discharges its disclosure invariant.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialBeaconAmbient PqxdhInitialHalfObserverCompiler PqxdhInitialHalfObserver
open PqxdhInitialParentObserver (State flatten)
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
  | query => PqxdhInitialHalfObserver.handler source writer prior entry output pre application initial selector aux reader query

noncomputable def handler (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput) :=
  RawCtxSelectedAliasCoupling.routed
    (PqxdhInitialHalfObserver.handler source writer prior entry output pre application initial selector aux reader)
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
    RawCtxSelectedParentPrivate.handler, PqxdhInitialHalfObserver.handler,
    PqxdhInitialHalfObserverCompiler.handler, PqxdhInitialHalfObserver.old]

/-- Every external and initializer-audit callback is the original ordinary callback on every branch, including root aliases. -/
theorem external_same (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (query : ((External extra I D K X Response Shared) + (InitialReply →ₒ Option (PqxdhInitialPendingPost.KernelOf RawCtxSelectedChain.Slot))).Domain) :
    handler source writer prior entry output pre application initial selector aux reader target (.inr query) =
      PqxdhInitialHalfObserver.handler source writer prior entry output pre application initial selector aux reader (.inr query) := by
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
    tvDist ((simulateQ (PqxdhInitialHalfObserver.observed source writer prior entry output pre application initial selector aux reader) client).run state)
      ((simulateQ (observed source writer prior entry output pre application initial selector aux reader target) client).run state) ≤
      Pr[fun result => target ∈ result.2.1.2 |
        (simulateQ (PqxdhInitialHalfObserver.observed source writer prior entry output pre application initial selector aux reader) client).run state].toReal :=
  RawCtxFlaggedQueryTrace.distance_vcvioLegacy
    (PqxdhInitialHalfObserver.handler source writer prior entry output pre application initial selector aux reader)
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
      PqxdhInitialHalfObserver.handler source writer (RawCtxSelectedParentPrivatePatch.privatePatch prior target output)
        entry output pre application initial selector aux reader := by
  funext query
  cases query with
  | inl query =>
      rw [old_source]
      unfold PqxdhInitialHalfObserver.handler PqxdhInitialHalfObserverCompiler.handler PqxdhInitialHalfObserver.old
      rw [RawCtxSelectedParentPrivateRealization.handler_patch source writer prior entry target output reader
        (RawCtxSelectedParentPrivateRealization.realView source) separate]
  | inr query =>
      rw [external_same]
      rcases query with (query | (reply | (secrets | (query | query)))) | reply
      all_goals simp only [PqxdhInitialHalfObserver.handler, PqxdhInitialHalfObserverCompiler.handler]

/-- The complete source program is the exact patched private label interpreter with its original initializer, all optional native reads and all ambient state retained. -/
theorem compiled_source (target : RootOutput)
    (client : OracleComp (PqxdhInitialPendingPost.Spec extra RawCtxSelectedChain.Slot I D K X Response Shared S B) Result)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ entry.address) :
    simulateQ (handler source writer prior entry output pre application initial selector aux
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
      (simulateQ PqxdhInitialHalfObserverCompiler.compiler client) =
      flatten (simulateQ (PqxdhInitialPendingPost.handler
        (PqxdhInitialParentPost.labelPrimitive source writer
          (RawCtxSelectedParentPrivatePatch.privatePatch prior target output) entry (RawCtxKdfRequestTable.fullResponse output))
        (PqxdhInitialParentPost.labelReader target) pre application
        (fun secrets => Prod.snd <$> initial secrets) selector aux) client) := by
  rw [handler_patch source writer prior entry output pre application initial selector aux _ target separate]
  exact PqxdhInitialHalfObserver.compiled_source source writer _ entry output pre application initial selector aux target client

open PqxdhInitialDisclosureState (Base isRead Keep Rules trace_keep)
open RawCtxFamilyFreshnessProxy RawCtxSelectedChain

private theorem state_pure {T V : Type} (value : V) (state : T) :
    (pure value : StateT T ProbComp V) state = pure (value, state) := rfl

/-- Every original non-read callback compiles to a program with zero direct-disclosure queries. -/
theorem compiler_quiet (query : (Base extra I D K X Response Shared S B).Domain)
    (quiet : ¬ isRead query) :
    (PqxdhInitialHalfObserverCompiler.compiler query).IsQueryBoundP
      (fun query => PqxdhInitialHalfObserver.direct (extra := extra) query = true) 0 := by
  rcases query with (query | input) | (query | (reply | (secrets | (query | query))))
  · rcases query with (pending | opening) | ((pending | sealing) | (coin | (hash | view)))
    all_goals simp only [PqxdhInitialHalfObserverCompiler.compiler, RawCtxFamilyPendingCompiler.live,
      RawCtxPendingFamilyLiveQueries.handler, RawCtxFamilyPendingCompiler.primitive,
      QueryImpl.compose, RawCtxPendingOwnerQueries.erase, simulateQ_spec_query,
      PqxdhInitialHalfObserverCompiler.oldForward, RawCtxSelectedLiveCompiler.primitiveForward]
    all_goals exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialHalfObserver.direct, RawCtxSelectedParentReadMask.direct])
  · exact False.elim (quiet trivial)
  · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialHalfObserver.direct])
  · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialHalfObserver.direct])
  · simp only [PqxdhInitialHalfObserverCompiler.compiler, PqxdhInitialHalfObserverCompiler.externalForward,
      PqxdhInitialHalfObserverCompiler.audit, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [PqxdhInitialHalfObserver.direct]), fun _ =>
      (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialHalfObserver.direct])⟩
  · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialHalfObserver.direct])
  · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialHalfObserver.direct])


variable (target : RootOutput)

noncomputable def actual : QueryImpl (Base extra I D K X Response Shared S B)
    (StateT (PqxdhInitialDisclosureState.State (PqxdhInitialParentObserver.State A N C)) ProbComp) :=
  PqxdhInitialHalfPrivateObserver.observed source writer prior entry output pre application initial selector aux
    (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target ∘ₛ
      PqxdhInitialHalfObserverCompiler.compiler

/-- Every non-read source callback in the actual complete audited interpreter retains the disclosure bit and all earlier candidates, including the unchanged initializer and its candidate audit. -/
theorem actual_quiet (query : (Base extra I D K X Response Shared S B).Domain)
    (quiet : ¬ isRead query) (state : PqxdhInitialDisclosureState.State (PqxdhInitialParentObserver.State A N C))
    (result : (Base extra I D K X Response Shared S B).Range query × PqxdhInitialDisclosureState.State (PqxdhInitialParentObserver.State A N C))
    (supported : result ∈ support ((actual source writer prior entry output pre application initial selector aux target query).run state)) :
    Keep state result.2 :=
  trace_keep _ _ _ _ (compiler_quiet query quiet) state result supported


private theorem actual_old_read (input : RawCtxSelectedLiveCompiler.ReadInput) :
    PqxdhInitialHalfPrivateObserver.handler source writer prior entry output pre application initial selector aux
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target (.inl (.inr input)) =
      pure (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target) input.1 input.2) := by
  rw [PqxdhInitialHalfPrivateObserver.old_source, RawCtxSelectedParentPrivate.read_same]
  rfl

/-- The full audited interpreter returns the original optional native family read, recording its available candidates and exact direct-disclosure bit without altering ambient state. -/
theorem actual_read (input : RawCtxFamilyFreshnessProxy.Input S B)
    (state : PqxdhInitialDisclosureState.State (PqxdhInitialParentObserver.State A N C)) :
    ((actual source writer prior entry output pre application initial selector aux target) (.inl (.inr input))).run state =
      pure (RawCtxGenericFamilyRead.nativeValue (nativeKernel (RawCtxFreshChainCut.concreteChain target)) input,
        ((state.1.1, state.1.2 ++ RawCtxSelectedLiveRead.candidates (readKind input.1) input.2), state.2 || direct input)) := by
  rcases input with ⟨request, kernel⟩
  cases request <;> cases kernel
  all_goals simp only [actual, QueryImpl.compose, PqxdhInitialHalfObserverCompiler.compiler,
    RawCtxFamilyPendingCompiler.live, RawCtxPendingFamilyLiveQueries.handler, RawCtxFamilyReadCompiler.compiler,
    simulateQ_pure, simulateQ_spec_query, PqxdhInitialHalfObserverCompiler.oldForward,
    PqxdhInitialHalfPrivateObserver.observed, RawCtxFlaggedQueryTrace.trace,
    actual_old_read source writer prior entry output pre application initial selector aux target,
    StateT.run, state_pure, pure_bind]
  all_goals simp [RawCtxGenericFamilyRead.nativeValue, nativeKernel, RawCtxSelectedLiveTrace.nativeReader,
    RawCtxSelectedLiveRead.nativeRead, RawCtxSelectedLiveRead.candidates, readKind, RawCtxFamilyFreshnessProxy.direct,
    RawCtxSelectedLiveRead.exposed, RawCtxSelectedLiveRead.labelRead, RawCtxSelectedLiveRead.replyInputs,
    PqxdhInitialHalfObserver.inputs, PqxdhInitialHalfObserver.direct,
    RawCtxSelectedLiveCompiler.inputs, RawCtxSelectedParentReadMask.direct,
    RawCtxChainInterpretation.mapChains, interpret]

/-- The actual full partial-routing interpreter discharges every callback law needed by the original post history proof. -/
theorem actual_rules : Rules target (actual (S := S) (B := B) source writer prior entry output pre application initial selector aux target) :=
  ⟨actual_quiet source writer prior entry output pre application initial selector aux target,
    actual_read source writer prior entry output pre application initial selector aux target⟩


end Interpreter
end BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.old_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.old_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.external_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.external_same

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.audit_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.audit_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.distance

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.query_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.event_good

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.handler_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.handler_patch

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.compiled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.compiled_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.compiler_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.compiler_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.actual_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.actual_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.actual_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.actual_read

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.actual_rules' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver.actual_rules
