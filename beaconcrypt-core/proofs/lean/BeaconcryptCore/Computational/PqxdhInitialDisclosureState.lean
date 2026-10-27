import BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop
import BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy

/-!
The full pending source distinguishes actual family disclosures from its other callbacks. A zero-read syntactic certificate preserves the complete candidate prefix and sticky disclosure bit under an explicit interpreter. The concrete later-parent audit interpreter discharges the per-query laws; no final freshness equation is assumed.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialDisclosureState
open PqxdhSecretInputKdf PqxdhInitialPendingPost RawCtxSelectedChain RawCtxFamilyFreshnessProxy
variable {ι M P I D K X Response Shared Result Origin Z : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev State (Z : Type) := (Z × List RootOutput) × Bool

private theorem state_pure {T V : Type} (value : V) (state : T) :
    (pure value : StateT T ProbComp V) state = pure (value, state) := rfl

private theorem state_map {α β : Type} (f : α → β) (work : StateT (State Z) ProbComp α) (state : State Z) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state := StateT.run_map f work state

abbrev Base (extra : OracleSpec ι) (I D K X Response Shared : Type) (S B : Nat) :=
  PqxdhInitialPendingPost.Spec extra Slot I D K X Response Shared S B

def isRead : (Base extra I D K X Response Shared S B).Domain → Prop
  | .inl (.inr _) => True
  | _ => False
instance : DecidablePred (isRead (extra := extra) (I := I) (D := D) (K := K) (X := X)
    (Response := Response) (Shared := Shared) (S := S) (B := B)) := fun query => by
  rcases query with (query | query) | query <;> simp only [isRead] <;> infer_instance

def Keep (before after : State Z) : Prop := after.2 = before.2 ∧ before.1.2 ⊆ after.1.2

def Invariant (target : RootOutput) (prior : List RatchetChain)
    (history : RawCtxProtocolReveals.History S B) (state : State Z) : Prop :=
  Witness (RawCtxFreshChainCut.concreteChain target) history state.2 ∧
    (state.2 = false → knownInputs prior history ⊆ state.1.2)

structure Rules (target : RootOutput)
    (impl : QueryImpl (Base extra I D K X Response Shared S B) (StateT (State Z) ProbComp)) : Prop where
  quiet : ∀ query, ¬ isRead query → ∀ state result, result ∈ support ((impl query).run state) → Keep state result.2
  read : ∀ (input : RawCtxFamilyFreshnessProxy.Input S B) (state : State Z),
    (impl (.inl (.inr input))).run state = pure
      (RawCtxGenericFamilyRead.nativeValue (nativeKernel (RawCtxFreshChainCut.concreteChain target)) input,
        ((state.1.1, state.1.2 ++ RawCtxSelectedLiveRead.candidates (readKind input.1) input.2), state.2 || direct input))

/-- A complete zero-read source program retains every earlier candidate and exactly its prior disclosure bit. -/
theorem quiet_program (target : RootOutput)
    (impl : QueryImpl (Base extra I D K X Response Shared S B) (StateT (State Z) ProbComp))
    (rules : Rules target impl) (client : OracleComp (Base extra I D K X Response Shared S B) Result)
    (quiet : client.IsQueryBoundP (isRead (extra := extra)) 0) (state : State Z) (result : Result × State Z)
    (supported : result ∈ support ((simulateQ impl client).run state)) : Keep state result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨rfl, List.Subset.refl _⟩
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have unselected : ¬ isRead query := quiet.1.resolve_right (Nat.not_lt_zero _)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, reached, rest⟩ := supported
    have first := rules.quiet query unselected state reply reached
    have later := ih reply.1 (by simpa only [unselected, ite_false] using quiet.2 reply.1) reply.2 result rest
    exact ⟨later.1.trans first.1, List.Subset.trans first.2 later.2⟩

/-- A preserved candidate prefix and flag retain the exact same original-history disclosure invariant. -/
theorem invariant_keep (target : RootOutput) (prior : List RatchetChain)
    (history : RawCtxProtocolReveals.History S B) (before after : State Z)
    (valid : Invariant target prior history before) (kept : Keep before after) : Invariant target prior history after :=
  ⟨fun hit => valid.1 (kept.1 ▸ hit), fun clear => List.Subset.trans (valid.2 (kept.1 ▸ clear)) kept.2⟩

/-- Original optional family reads append their actual native reply and supply a witness for each newly raised direct-read flag. -/
theorem read_invariant (target : RootOutput) (prior : List RatchetChain)
    (input : RawCtxFamilyFreshnessProxy.Input S B) (history : RawCtxProtocolReveals.History S B) (state : State Z)
    (valid : Invariant target prior history state) :
    Invariant target prior (RawCtxProtocolReveals.note (actualObservation (RawCtxFreshChainCut.concreteChain target) input) history)
      ((state.1.1, state.1.2 ++ RawCtxSelectedLiveRead.candidates (readKind input.1) input.2), state.2 || direct input) := by
  constructor
  · exact witness_note _ _ _ _ valid.1
  · intro clear
    have conditions : state.2 = false ∧ direct input = false := by simpa using clear
    have same := congrArg (Sigma.mk input.1) (value_before (RawCtxFreshChainCut.concreteChain target) input conditions.2)
    change actualObservation (RawCtxFreshChainCut.concreteChain target) input = labelObservation input at same
    simp only [knownInputs, known_note, List.map_append, same, label_inputs]
    intro value present
    rcases List.mem_append.mp present with old | current
    · exact List.mem_append_left _ (valid.2 conditions.1 old)
    · exact List.mem_append_right _ current

private theorem zero_simulate {κ : Type} {spec : OracleSpec κ}
    (forward : QueryImpl spec (OracleComp (Base extra I D K X Response Shared S B)))
    (zero : ∀ query, (forward query).IsQueryBoundP (isRead (extra := extra)) 0) (client : OracleComp spec Result) :
    (simulateQ forward client).IsQueryBoundP (isRead (extra := extra)) 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact isQueryBoundP_bind (n := 0) (m := 0) (zero query) (fun reply _ => ih reply)

/-- Every complete owner primitive continuation excludes family-read callbacks under the literal pending injection. -/
theorem primitive_quiet (client : OracleComp (RawCtxPendingOwnerQueries.Spec Slot) Result) :
    (simulateQ (primitiveForward (extra := extra) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := Shared) (S := S) (B := B)) client).IsQueryBoundP (isRead (extra := extra)) 0 := by
  apply zero_simulate
  intro query
  exact (isQueryBoundP_query_iff _ _ _).mpr (by simp only [isRead, IsEmpty.forall_iff])


private theorem external_quiet (query : (PqxdhInitialPendingPost.External extra Slot I D K X Response Shared).Domain) :
    OracleComp.IsQueryBoundP ((Base extra I D K X Response Shared S B).query (.inr query) : OracleComp (Base extra I D K X Response Shared S B) _)
      (isRead (extra := extra)) 0 :=
  (isQueryBoundP_query_iff _ _ _).mpr (by simp only [isRead, IsEmpty.forall_iff])

private theorem after_quiet (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) (kernel : KernelOf Slot) :
    (PqxdhInitialGenericBeacon.afterInitial
      (calls (extra := extra) (I := I) (D := D) (K := K) (X := X) (Shared := Shared) (S := S) (B := B))
      applicationForward decode pending kernel).IsQueryBoundP (isRead (extra := extra)) 0 := by
  unfold PqxdhInitialGenericBeacon.afterInitial
  apply isQueryBoundP_bind (n := 0) (m := 0) (external_quiet _)
  intro reply _
  cases reply with
  | none => trivial
  | some raw =>
    simp only [bind_pure_comp, isQueryBoundP_map_iff]
    apply RawCtxGenericFamilyBudgets.owner_raw calls (isRead (extra := extra)) 0 _ decode raw _
    intro entry target context
    exact primitive_quiet (RawCtxPendingOwnerQueries.calls.receive entry target context)

private theorem tail_quiet (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) :
    (PqxdhInitialGenericBeacon.tail
      (calls (Chain := Slot) (extra := extra) (I := I) (D := D) (K := K) (X := X) (Shared := Shared) (S := S) (B := B))
      applicationForward initialForward decode pending).IsQueryBoundP (isRead (extra := extra)) 0 := by
  unfold PqxdhInitialGenericBeacon.tail
  apply isQueryBoundP_bind (n := 0) (m := 0) (external_quiet _)
  intro reply _
  cases reply with
  | none => trivial
  | some kernel => exact after_quiet decode pending kernel

/-- Every original attempted initialization and complete first receive excludes adversary family-read operations, even across failing external callbacks. -/
theorem finish_quiet (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxGenericRoleStorage.BeaconState (KernelOf Slot) I D K) :
    (PqxdhInitialFinishOrigin.owner mark preForward
      (calls (extra := extra) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B))
      applicationForward initialForward decode raw state).IsQueryBoundP (isRead (extra := extra)) 0 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [PqxdhInitialFinishOrigin.owner, active]
    apply isQueryBoundP_bind (n := 0) (m := 0)
    · exact zero_simulate preForward (fun query => external_quiet _) _
    · intro pending _
      cases pending with
      | none => trivial
      | some pending =>
        simp only [bind_pure_comp, isQueryBoundP_map_iff]
        exact tail_quiet decode pending
  | _ => simp only [PqxdhInitialFinishOrigin.owner, active]; trivial


/-- The actual original family operation updates its original history and derives the disclosure invariant from the interpreter's literal read and non-read laws. -/
theorem live_invariant (target : RootOutput)
    (impl : QueryImpl (Base extra I D K X Response Shared S B) (StateT (State Z) ProbComp))
    (rules : Rules target impl) (prior : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : RawCtxPendingFamilyLiveQueries.State Slot M P I D K S B) (state : State Z)
    (valid : Invariant target prior before.2 state)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query ×
      RawCtxPendingFamilyLiveQueries.State Slot M P I D K S B) × State Z)
    (supported : result ∈ support ((simulateQ impl (simulateQ liveForward
      ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run before))).run state)) :
    Invariant target prior result.1.2.2 result.2 := by
  cases query with
  | inl request =>
    simp only [RawCtxPendingFamilyLiveQueries.compiler, StateT.run, bind_pure_comp,
      simulateQ_map, state_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    have actual : completed ∈ support ((simulateQ impl (simulateQ primitiveForward
        ((RawCtxGenericFamilyFrontend.impl RawCtxPendingOwnerQueries.calls RawCtxPendingOwnerQueries.publicForward
          sender route decode request).run before.1))).run state) := by
      rw [← QueryImpl.simulateQ_compose liveForward RawCtxPendingFamilyLiveQueries.primitiveForward] at reached
      have forward : liveForward ∘ₛ RawCtxPendingFamilyLiveQueries.primitiveForward =
          (primitiveForward : QueryImpl (RawCtxPendingOwnerQueries.Spec Slot) (OracleComp (Base extra I D K X Response Shared S B))) := by
        funext query
        exact simulateQ_spec_query _ _
      simpa only [forward, StateT.run] using reached
    exact invariant_keep target prior before.2 state completed.2 valid
      (quiet_program target impl rules _ (primitive_quiet _) state completed actual)
  | inr request =>
    simp only [RawCtxPendingFamilyLiveQueries.compiler, StateT.run, bind_pure_comp,
      simulateQ_map, simulateQ_spec_query, liveForward, state_map] at supported
    have actualRead := rules.read (request, RawCtxGenericRoleFamily.selectedKernel
      (RawCtxGenericFamilyRead.requestOwner request) before.1) state
    simp only [StateT.run] at actualRead
    rw [actualRead, map_pure, mem_support_pure_iff] at supported
    subst result
    exact read_invariant target prior _ before.2 state valid

/-- The complete original live continuation preserves its actual disclosure history under the same local source callback laws. -/
theorem live_schedule_invariant (target : RootOutput)
    (impl : QueryImpl (Base extra I D K X Response Shared S B) (StateT (State Z) ProbComp))
    (rules : Rules target impl) (prior : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (before : RawCtxPendingFamilyLiveQueries.State Slot M P I D K S B) (state : State Z)
    (valid : Invariant target prior before.2 state)
    (result : (Result × RawCtxPendingFamilyLiveQueries.State Slot M P I D K S B) × State Z)
    (supported : result ∈ support ((simulateQ impl (simulateQ liveForward
      ((simulateQ (RawCtxPendingFamilyLiveQueries.compiler sender route decode) client).run before))).run state)) :
    Invariant target prior result.1.2.2 result.2 := by
  induction client using OracleComp.inductionOn generalizing before state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact valid
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨completed, reached, rest⟩ := supported
    exact ih completed.1.1 completed.1.2 completed.2
      (live_invariant target impl rules prior sender route decode query before state valid completed reached) rest

/-- The full original post operation retains the same source history, candidate log and disclosure witness through every selector and finish branch. -/
theorem post_invariant (target : RootOutput)
    (impl : QueryImpl (Base extra I D K X Response Shared S B) (StateT (State Z) ProbComp))
    (rules : Rules target impl) (prior : List RatchetChain)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : Front Slot M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B) (state : State Z)
    (valid : Invariant target prior before.1.roles.2 state)
    (result : ((PqxdhInitialGenericPost.Spec extra S B).Range query ×
      (Front Slot M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) × State Z)
    (supported : result ∈ support ((simulateQ impl
      ((PqxdhInitialOriginPost.compiler mark sender route decode query).run before)).run state)) :
    Invariant target prior result.1.2.1.roles.2 result.2 := by
  rcases query with (query | query) | ⟨index, raw⟩
  · simp only [PqxdhInitialOriginPost.compiler, StateT.run, bind_pure_comp, simulateQ_map, state_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    exact live_invariant target impl rules prior sender route decode query before.1.roles state valid completed reached
  · simp only [PqxdhInitialOriginPost.compiler, StateT.run, bind_pure_comp, simulateQ_map, state_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    exact invariant_keep target prior before.1.roles.2 state completed.2 valid
      (quiet_program target impl rules (selectorForward query)
        (external_quiet (.inr (.inr (.inr (.inl query))))) state completed reached)
  · simp only [PqxdhInitialOriginPost.compiler, StateT.run, bind_pure_comp, simulateQ_map, state_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    exact invariant_keep target prior before.1.roles.2 state completed.2 valid
      (quiet_program target impl rules _ (finish_quiet mark decode raw _) state completed reached)

/-- Every complete original adaptive post client derives its actual final disclosure invariant from its own initial history and the same interpreter. -/
theorem schedule_invariant (target : RootOutput)
    (impl : QueryImpl (Base extra I D K X Response Shared S B) (StateT (State Z) ProbComp))
    (rules : Rules target impl) (prior : List RatchetChain)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front Slot M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B) (state : State Z)
    (valid : Invariant target prior before.1.roles.2 state)
    (result : (Result × (Front Slot M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) × State Z)
    (supported : result ∈ support ((simulateQ impl
      ((simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) client).run before)).run state)) :
    Invariant target prior result.1.2.1.roles.2 result.2 := by
  induction client using OracleComp.inductionOn generalizing before state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact valid
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨completed, reached, rest⟩ := supported
    exact ih completed.1.1 completed.1.2 completed.2
      (post_invariant target impl rules prior mark sender route decode query before state valid completed reached) rest


/-- Any literal program with no flagged queries retains its original candidate prefix and exact sticky bit under full query tracing. -/
theorem trace_keep {κ V : Type} {spec : OracleSpec κ}
    (handler : QueryImpl spec (StateT Z ProbComp)) (inputs : spec.Domain → List RootOutput)
    (flagged : spec.Domain → Bool) (client : OracleComp spec V)
    (quiet : client.IsQueryBoundP (fun query => flagged query = true) 0)
    (state : State Z) (result : V × State Z)
    (supported : result ∈ support ((simulateQ (RawCtxFlaggedQueryTrace.trace handler inputs flagged) client).run state)) :
    Keep state result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨rfl, List.Subset.refl _⟩
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have absent : flagged query ≠ true := quiet.1.resolve_right (Nat.not_lt_zero _)
    have flagEq : flagged query = false := Bool.eq_false_iff.mpr absent
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, reached, rest⟩ := supported
    simp only [RawCtxFlaggedQueryTrace.trace, StateT.run, bind_pure_comp, support_map] at reached
    obtain ⟨actual, _, rfl⟩ := reached
    have later := ih actual.1 (by simpa only [flagEq, Bool.false_eq_true, ite_false] using quiet.2 actual.1) _ result rest
    exact ⟨by simpa only [flagEq, Bool.or_false] using later.1,
      List.Subset.trans (List.subset_append_left _ _) later.2⟩

private theorem compiler_quiet (query : (Base extra I D K X Response Shared S B).Domain)
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

section Actual
open PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhInitialBeaconAmbient PqxdhInitialParentObserverCompiler
variable {A N C : Type}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (output : FullOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
  (selector : QueryImpl extra (Ambient A N C)) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (target : RootOutput)

noncomputable def actual : QueryImpl (Base extra I D K X Response Shared S B)
    (StateT (State (PqxdhInitialParentObserver.State A N C)) ProbComp) :=
  PqxdhInitialParentObserverAliases.observed source writer prior entry output pre application initial selector aux
    (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target ∘ₛ
      PqxdhInitialParentObserverCompiler.compiler

/-- Every non-read source callback in the actual complete audited interpreter retains the disclosure bit and all earlier candidates, including initializer root routing. -/
theorem actual_quiet (query : (Base extra I D K X Response Shared S B).Domain)
    (quiet : ¬ isRead query) (state : State (PqxdhInitialParentObserver.State A N C))
    (result : (Base extra I D K X Response Shared S B).Range query × State (PqxdhInitialParentObserver.State A N C))
    (supported : result ∈ support ((actual source writer prior entry output pre application initial selector aux target query).run state)) :
    Keep state result.2 :=
  trace_keep _ _ _ _ (compiler_quiet query quiet) state result supported


private theorem actual_old_read (input : RawCtxSelectedLiveCompiler.ReadInput) :
    PqxdhInitialParentObserverAliases.handler source writer prior entry output pre application initial selector aux
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target (.inl (.inr input)) =
      pure (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target) input.1 input.2) := by
  rw [PqxdhInitialParentObserverAliases.old_source, RawCtxSelectedParentPrivate.read_same]
  rfl

/-- The full audited interpreter returns the original optional native family read, recording its available candidates and exact direct-disclosure bit without altering ambient state. -/
theorem actual_read (input : RawCtxFamilyFreshnessProxy.Input S B)
    (state : State (PqxdhInitialParentObserver.State A N C)) :
    ((actual source writer prior entry output pre application initial selector aux target) (.inl (.inr input))).run state =
      pure (RawCtxGenericFamilyRead.nativeValue (nativeKernel (RawCtxFreshChainCut.concreteChain target)) input,
        ((state.1.1, state.1.2 ++ RawCtxSelectedLiveRead.candidates (readKind input.1) input.2), state.2 || direct input)) := by
  rcases input with ⟨request, kernel⟩
  cases request <;> cases kernel
  all_goals simp only [actual, QueryImpl.compose, PqxdhInitialParentObserverCompiler.compiler,
    RawCtxFamilyPendingCompiler.live, RawCtxPendingFamilyLiveQueries.handler, RawCtxFamilyReadCompiler.compiler,
    simulateQ_pure, simulateQ_spec_query, PqxdhInitialParentObserverCompiler.oldForward,
    PqxdhInitialParentObserverAliases.observed, RawCtxFlaggedQueryTrace.trace,
    actual_old_read source writer prior entry output pre application initial selector aux target,
    StateT.run, state_pure, pure_bind]
  all_goals simp [RawCtxGenericFamilyRead.nativeValue, nativeKernel, RawCtxSelectedLiveTrace.nativeReader,
    RawCtxSelectedLiveRead.nativeRead, RawCtxSelectedLiveRead.candidates, readKind, direct,
    RawCtxSelectedLiveRead.exposed, RawCtxSelectedLiveRead.labelRead, RawCtxSelectedLiveRead.replyInputs,
    PqxdhInitialParentObserver.inputs, PqxdhInitialParentObserver.direct,
    RawCtxSelectedLiveCompiler.inputs, RawCtxSelectedParentReadMask.direct,
    RawCtxChainInterpretation.mapChains, interpret]

/-- The actual full routed private interpreter discharges every callback law needed by the original post history proof. -/
theorem actual_rules : Rules target (actual (S := S) (B := B) source writer prior entry output pre application initial selector aux target) :=
  ⟨actual_quiet source writer prior entry output pre application initial selector aux target,
    actual_read source writer prior entry output pre application initial selector aux target⟩

end Actual

end BeaconcryptCore.Computational.PqxdhInitialDisclosureState

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.quiet_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.quiet_program
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.invariant_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.invariant_keep
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.read_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.read_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.primitive_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.primitive_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.finish_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.finish_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.live_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.live_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.live_schedule_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.live_schedule_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.post_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.post_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.schedule_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.schedule_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.actual_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.actual_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.actual_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.actual_read
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.actual_rules' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.actual_rules

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDisclosureState.trace_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDisclosureState.trace_keep
