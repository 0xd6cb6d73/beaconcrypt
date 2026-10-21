import BeaconcryptCore.Computational.PqxdhSelectedPostCompiler
import BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs

/-!
The selected-nonce stop of the complete outer post interpreter (adaptive records and reveals, private selectors and attempted Beacon finishes) is charged to a source event of the same run. A chronological history records the original send trailer of every record request; selectors and attempted finishes record nothing because they make no selected seal (a finish makes only its single raw opening, a selector only forwards known-key hash work). The main theorem `input_bound` shows, with coefficient one and for every post client and every prepared state with an empty selected-nonce ledger, that the probability of the sticky stop flag used by `PqxdhSelectedPostCompiler.source_distance` is at most the probability that two ordered sealing positions of that history use the exact selected sending chain `concreteChain target`. The corollary `source_input_distance` restates `source_distance` with this source event.

This is the generic-post version of `RawCtxSelectedNonceSourceEvent.nonce_event_bound` and `RawCtxSelectedSourceSendInputs.nonce_input_bound`. The companion theorems `source_input_bound` and `source_history_distance` charge the same event in `sourceObserved`, the original stopped-source post extended by the same history, which has no CTX component and no selected-nonce ledger; `source_erased_program` shows that erasing its history gives the original source post run. None of these theorems bounds the probability of the repeated selected input itself. For the first-record run that probability is not a pure statistical term pointwise in the prepared front and the post adversary, for two reasons. First, two Beacons of the front in the initial-sent phase that hold the same Diffie-Hellman key handles and accept the same raw response (for example two identical slots) can both be finished on the selected message, because the finish mark depends only on the four Diffie-Hellman values and on the ciphertext (decapsulation routing compares only the ciphertext), and both first sends then use the target chain. Second, a reveal of the selected sending chain before its first send (or of the Server peer receiving chain before it receives) returns the target chain as a known value without setting the hidden-disclosure flag, after which a second chain can reach it through a preimage search on public HKDF, for which no statistical bound exists. The first case needs a preparation-phase event or hypothesis on the front, the second needs a charged event restricted to stops while the target chain is still undisclosed (the source decision is false afterwards), and the remaining chain-collision count needs a target-free observer; all three are left to the consuming experiment.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedDriverAudit
open PqxdhSelectedPostCompiler (Optional Full)
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The chronological source event history of the post, labelled by protocol owner. -/
abbrev History (S B : Nat) := List (Event (RawCtxProtocolReveals.Owner S B))

/-- The complete augmented post state together with its source event history. -/
abbrev Observed (M P I D K A N C : Type) (S B : Nat) := History S B × Full M P I D K A N C S B

/-- The original send trailer of a record request; selectors and attempted finishes record no event. -/
noncomputable def events (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
    (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (state : Full M P I D K A N C S B) : History S B :=
  match query with
  | .inl (.inl request) => RawCtxSelectedLiveAuditLedger.events prior parent target nonce next sender request state.1.1.roles
  | _ => []

/-- The same send trailer read from an original stopped-source post state, which has no CTX component. -/
noncomputable def sourceEvents (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
    (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (state : PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B) : History S B :=
  match query with
  | .inl (.inl request) => RawCtxSelectedLiveAuditLedger.events prior parent target nonce next sender request state.1.roles
  | _ => []

section Quiet
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

/-- The source-local callbacks make no selected sealing request, regardless of their original uniform and hash cost. -/
theorem external_nonseal (query : (PqxdhSelectedCallbackCompiler.External extra I D K X Response Shared).Domain)
    (state : Local A N C) :
    ((PqxdhSelectedCallbackCompiler.lower pre application initial selector aux (.inl query)).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  change (simulateQ RawCtxSourceSharedRom.forward
    ((PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query).run state)).IsQueryBoundP _ 0
  simp only [RawCtxSourceSharedRom.forward, QueryImpl.simulateQ_compose]
  apply RawCtxSelectedSealConsumer.lifted_bound
  change (simulateQ AdaptiveCtxSharedTarget.forward
    ((PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query).run state)).IsQueryBoundP
      AdaptiveCtxQueryBounds.SourceSeal 0
  apply AdaptiveCtxSharedTarget.forward_bound
  simp only [AdaptiveCtxSharedTarget.forward_seal_class]
  exact isQueryBoundP_false _ 0

/-- A complete attempted Beacon finish makes no selected sealing request: its only component work is the raw first-record opening and forwarded callback work. -/
theorem finish_nonseal (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (before : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) (state : Local A N C) :
    ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent target nonce next read)
      (PqxdhSelectedInitialOwnerCompiler.owner raw before)).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  apply (isQueryBoundP_false (PqxdhSelectedInitialOwnerCompiler.owner (extra := extra) (X := X) (Response := Response)
    (Shared := Shared) raw before) 0).simulateQ_run_of_step
  · intro _ impossible
    exact False.elim impossible
  · intro query _ state
    cases query with
    | inl query => exact external_nonseal pre application initial selector aux query state
    | inr request =>
      simp only [PqxdhSelectedInitialOwnerCompiler.lower, StateT.run, isQueryBoundP_map_iff,
        PqxdhSelectedBeaconCompiler.finishApplication]
      cases application : request.application with
      | none => simp only [PqxdhSelectedBeaconCompiler.afterApplication, isQueryBoundP_pure]
      | some raw =>
        simp only [PqxdhSelectedBeaconCompiler.afterApplication, isQueryBoundP_map_iff]
        exact RawCtxSelectedSendAuditLedger.raw_quiet prior parent target nonce next read raw
          (PqxdhInitialGenericBeacon.localOwner request.candidate request.kernel)

/-- Evaluating any source-local program with no selected sealing request keeps the selected nonce ledger of the CTX component. -/
theorem evaluate_quiet {Local Value : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) Value)
    (bounded : ∀ state, (work.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0)
    (before : Local × AdaptiveCtxDynamicKnownKeys.SourceState) (result : Value × (Local × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((PqxdhSelectedStateInterpreter.evaluate
      (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key) work).run before)) :
    result.2.2.selected.1.usedNonces = before.2.selected.1.usedNonces := by
  simp only [PqxdhSelectedStateInterpreter.evaluate, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  exact RawCtxSelectedSendLedger.program_nonseal (RawCtxUniversalDecoder.decoder read) source.crypto key _
    (bounded before.1) before.2 reply reached

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)

/-- Every new selected nonce of one augmented post callback belongs to that callback's recorded send trailer; selectors and attempted finishes keep the ledger. -/
theorem step_used (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (before : Full M P I D K A N C S B)
    (result : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × Full M P I D K A N C S B)
    (supported : result ∈ support ((PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer
      prior parent key target nonce next sender route read query).run before)) :
    RawCtxSelectedRoleAuditLedger.UsedBy (events prior parent target nonce next sender query before) before.2 result.2.2 := by
  rcases query with (request | request) | ⟨index, raw⟩
  · simp only [PqxdhSelectedPostCompiler.augmented, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact RawCtxSelectedLiveAuditLedger.step_used source writer prior parent key target nonce next sender route read request
      (before.1.1.roles, (before.1.2, before.2)) reply reached
  · have unchanged := evaluate_quiet source key read _
      (fun state => by
        simp only [PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff]
        exact external_nonseal pre application initial selector aux _ state.2) before result supported
    intro value used
    exact Or.inl (unchanged ▸ used)
  · have unchanged := evaluate_quiet source key read _
      (fun state => by
        simp only [PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff]
        exact finish_nonseal pre application initial selector aux prior parent target nonce next read raw _ state.2)
      before result supported
    intro value used
    exact Or.inl (unchanged ▸ used)

/-- The augmented post interpreter extended by the chronological source event history. -/
noncomputable def observed :
    QueryImpl (Optional (PqxdhInitialGenericPost.Spec extra S B)) (StateT (Observed M P I D K A N C S B) ProbComp) :=
  fun query before => (fun result => (result.1, (before.1 ++ events prior parent target nonce next sender query before.2, result.2))) <$>
    (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next
      sender route read query).run before.2

/-- Erasing the history from one observed callback gives the augmented callback with its complete reply and state. -/
theorem erased_step (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (before : Observed M P I D K A N C S B) :
    Prod.map id Prod.snd <$> (observed pre application initial selector aux source writer prior parent key target nonce next
      sender route read query).run before =
      (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next
        sender route read query).run before.2 := by
  simp only [observed, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  exact id_map _

/-- Erasing the history from a complete adaptive observed post run gives the augmented post run. -/
theorem erased_program (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : Observed M P I D K A N C S B) :
    Prod.map id Prod.snd <$> (simulateQ (observed pre application initial selector aux source writer prior parent key target nonce next
      sender route read) client).run before =
      (simulateQ (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next
        sender route read) client).run before.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (erased_step pre application initial selector aux source writer prior parent key target nonce next sender route read) client before

/-- The observed post run projects to the original stopped-source post interpreter, with its complete optional result and source state. -/
theorem observed_source (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (before : Full M P I D K A N C S B) :
    (fun result => (result.1, PqxdhSelectedPostCompiler.project result.2.2)) <$>
      (simulateQ (observed pre application initial selector aux source writer prior parent key target nonce next sender route read)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run ([], before) =
      (simulateQ (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next
        sender route read) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (PqxdhSelectedPostCompiler.project before) := by
  have erased := congrArg (fun run => Prod.map id PqxdhSelectedPostCompiler.project <$> run)
    (erased_program pre application initial selector aux source writer prior parent key target nonce next sender route read
      (RawCtxSelectedFamilyNonceCoupling.optionalClient work) ([], before))
  simp only [Functor.map_map, Prod.map_def, id_eq] at erased
  rw [erased]
  exact PqxdhSelectedPostCompiler.augmented_program pre application initial selector aux source writer prior parent key target nonce next
    sender route read work before

/-- The original stopped-source post interpreter extended by the same chronological send-trailer history. It carries no CTX component and no selected-nonce ledger. -/
noncomputable def sourceObserved :
    QueryImpl (Optional (PqxdhInitialGenericPost.Spec extra S B))
      (StateT (History S B × PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B) ProbComp) :=
  fun query before => (fun result => (result.1, (before.1 ++ sourceEvents prior parent target nonce next sender query before.2, result.2))) <$>
    (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next
      sender route read query).run before.2

/-- Erasing the history from the history-extended source post gives the original stopped-source post run with its complete result and state. -/
theorem source_erased_program (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : History S B × PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B) :
    Prod.map id Prod.snd <$> (simulateQ (sourceObserved pre application initial selector aux source writer prior parent key target
      nonce next sender route read) client).run before =
      (simulateQ (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target
        nonce next sender route read) client).run before.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd (fun query state => by
    simp only [sourceObserved, StateT.run, Functor.map_map, Prod.map_def, id_eq]
    exact id_map _) client before

/-- Keep the history and project the augmented state to the original source-post state. -/
def projectObserved (state : Observed M P I D K A N C S B) :
    History S B × PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B :=
  (state.1, PqxdhSelectedPostCompiler.project state.2)

/-- One observed callback projects to the history-extended original source callback, with the same reply, history and source state. -/
theorem source_observed_step (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : Observed M P I D K A N C S B) :
    Prod.map id projectObserved <$> (observed pre application initial selector aux source writer prior parent key target nonce next
      sender route read query).run before =
      (sourceObserved pre application initial selector aux source writer prior parent key target nonce next
        sender route read query).run (projectObserved before) := by
  have trailer : events prior parent target nonce next sender query before.2 =
      sourceEvents prior parent target nonce next sender query (PqxdhSelectedPostCompiler.project before.2) := by
    rcases query with (request | request) | request <;> rfl
  have step := PqxdhSelectedPostCompiler.augmented_step pre application initial selector aux source writer prior parent key target
    nonce next sender route read query before.2
  simp only [StateT.run] at step
  simp only [observed, sourceObserved, projectObserved, StateT.run, trailer, Functor.map_map, Prod.map_def, id_eq]
  rw [← step, Functor.map_map]
  rfl

/-- Every complete adaptive observed run projects to the history-extended original source-post run, with the same result, history and source state. -/
theorem source_observed_program (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : Observed M P I D K A N C S B) :
    Prod.map id projectObserved <$> (simulateQ (observed pre application initial selector aux source writer prior parent key target
      nonce next sender route read) client).run before =
      (simulateQ (sourceObserved pre application initial selector aux source writer prior parent key target nonce next
        sender route read) client).run (projectObserved before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ projectObserved
    (source_observed_step pre application initial selector aux source writer prior parent key target nonce next sender route read)
    client before

/-- The stop predicate read from the observed state. -/
noncomputable def observedStops (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (state : Observed M P I D K A N C S B) : Prop :=
  PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender query state.2

/-- Nonce provenance, routed send trailers and the stop-to-repetition implication, for an observed state with its sticky stop flag. -/
def Consistent (state : Observed M P I D K A N C S B × Bool) : Prop :=
  RawCtxSelectedSendTrace.Tracked state.1.2.2 (RawCtxSourceEventRecorder.seals state.1.1) ∧
    RawCtxSelectedFamilySendEvents.RoutedHistory prior parent target nonce next state.1.1 ∧
    (state.2 = true → RawCtxSelectedNonceSourceEvent.Repeated state.1.1)

/-- One marked observed callback preserves nonce provenance and routing, and a stop leaves two recorded seals with the same selected nonce. -/
theorem marked_step_consistent (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : Observed M P I D K A N C S B × Bool)
    (result : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × (Observed M P I D K A N C S B × Bool))
    (supported : result ∈ support ((RawCtxSelectedFamilyNonceCoupling.marked
      (observed pre application initial selector aux source writer prior parent key target nonce next sender route read)
      (observedStops (extra := extra) prior parent target nonce next sender) query).run before))
    (previous : Consistent prior parent target nonce next before) :
    Consistent prior parent target nonce next result.2 := by
  classical
  simp only [RawCtxSelectedFamilyNonceCoupling.marked, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  simp only [observed, StateT.run, support_map, Set.mem_image] at reached
  obtain ⟨step, stepped, rfl⟩ := reached
  refine ⟨?_, ?_, ?_⟩
  · exact RawCtxSelectedRoleAuditLedger.tracked _ before.1.1 before.1.2.2 step.2.2
      (step_used pre application initial selector aux source writer prior parent key target nonce next sender route read
        query before.1.2 step stepped) previous.1
  · intro occurrence found
    rcases List.mem_append.mp found with old | current
    · exact previous.2.1 occurrence old
    · rcases query with (request | request) | request
      · exact RawCtxSelectedSourceSendInputs.callback_routed prior parent target nonce next sender request
          before.1.2.1.1.roles occurrence current
      · exact False.elim (List.not_mem_nil current)
      · exact False.elim (List.not_mem_nil current)
  · intro flagged
    rcases Bool.or_eq_true_iff.mp flagged with old | stopped
    · exact RawCtxSelectedNonceSourceEvent.repeated_append _ _ (previous.2.2 old)
    · have stops := of_decide_eq_true stopped
      rcases query with (request | request) | request
      · obtain ⟨value, earlier, current, oldFound, currentFound, oldNonce, currentNonce⟩ :=
          RawCtxSelectedLiveAuditLedger.stopped_pair prior parent target nonce next sender request
            (before.1.1, (before.1.2.1.1.roles, (before.1.2.1.2, before.1.2.2))) previous.1 stops
        exact RawCtxSelectedNonceSourceEvent.repeated_pair _ _ value earlier current oldFound currentFound oldNonce currentNonce
      · exact False.elim stops
      · exact False.elim stops

/-- Every complete adaptive marked observed run preserves the consistency invariant. -/
theorem marked_program_consistent (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : Observed M P I D K A N C S B × Bool) (result : Result × (Observed M P I D K A N C S B × Bool))
    (supported : result ∈ support ((simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
      (observed pre application initial selector aux source writer prior parent key target nonce next sender route read)
      (observedStops (extra := extra) prior parent target nonce next sender)) client).run before))
    (previous : Consistent prior parent target nonce next before) :
    Consistent prior parent target nonce next result.2 := by
  induction client using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact previous
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, reached, tail⟩ := supported
      exact ih reply.1 reply.2 result tail
        (marked_step_consistent pre application initial selector aux source writer prior parent key target nonce next sender route read
          query before reply reached previous)

/-- Drop the history from a marked observed state. -/
def forgetHistory (state : Observed M P I D K A N C S B × Bool) : Full M P I D K A N C S B × Bool := (state.1.2, state.2)

/-- Erasing the history from one marked observed callback gives the marked augmented callback used by `source_distance`. -/
theorem marked_step_erased (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : Observed M P I D K A N C S B × Bool) :
    Prod.map id forgetHistory <$> (RawCtxSelectedFamilyNonceCoupling.marked
      (observed pre application initial selector aux source writer prior parent key target nonce next sender route read)
      (observedStops (extra := extra) prior parent target nonce next sender) query).run before =
      (RawCtxSelectedFamilyNonceCoupling.marked
        (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next
          sender route read)
        (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender) query).run (forgetHistory before) := by
  simp only [RawCtxSelectedFamilyNonceCoupling.marked, observed, observedStops, forgetHistory, StateT.run,
    bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  rfl

/-- Erasing the history from a complete marked observed run gives the marked augmented run. -/
theorem marked_program_erased (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : Observed M P I D K A N C S B × Bool) :
    Prod.map id forgetHistory <$> (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
      (observed pre application initial selector aux source writer prior parent key target nonce next sender route read)
      (observedStops (extra := extra) prior parent target nonce next sender)) client).run before =
      (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
        (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next
          sender route read)
        (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender)) client).run (forgetHistory before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ forgetHistory
    (marked_step_erased pre application initial selector aux source writer prior parent key target nonce next sender route read) client before

end Quiet

/-- A repeated selected nonce in a routed history gives two ordered sealing positions at the exact selected sending chain. -/
theorem routed_input (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (history : History S B) (routed : RawCtxSelectedFamilySendEvents.RoutedHistory prior parent target nonce next history)
    (repeated : RawCtxSelectedNonceSourceEvent.Repeated history) :
    RawCtxSelectedSourceSendInputs.RepeatedInput target history := by
  obtain ⟨i, j, order, value, earlier, current⟩ := RawCtxSelectedSourceSendInputs.repeated_positions history repeated
  have chain : ∀ position : Fin (RawCtxSourceEventRecorder.seals history).length,
      RawCtxSelectedSendTrace.nonce ((RawCtxSourceEventRecorder.seals history).get position).pending = some value →
      ((RawCtxSourceEventRecorder.seals history).get position).entry.send_chain = RawCtxFreshChainCut.concreteChain target := by
    intro position selected
    have found := routed _ ((RawCtxSourceEventRecorder.mem_seals _ _).mp (List.get_mem _ position))
    cases parent with
    | none => exact RawCtxSelectedSendTrace.routed_chain prior target next nonce value _ found selected
    | some predecessor =>
      exact (RawCtxSelectedSendTrace.later_routed_chain prior predecessor target next nonce value _ found selected).2
  exact ⟨i, j, order, chain i earlier, chain j current⟩

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

section Bound
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)

/-- The selected-nonce stop probability of the complete outer post interpreter is at most, with coefficient one, the probability that the same run's chronological history contains two ordered sealing positions at the exact selected sending chain. No nonce freshness, uniqueness or independence premise is used; the prepared state only needs an empty selected-nonce ledger. -/
theorem input_bound (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : Full M P I D K A N C S B) (empty : before.2.selected.1.usedNonces = []) :
    𝒟[(fun result => result.2.2) <$> (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
      (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next
        sender route read)
      (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender)) client).run (before, false)] {true} ≤
      𝒟[(fun result => decide (RawCtxSelectedSourceSendInputs.RepeatedInput target result.2.1)) <$>
        (simulateQ (observed pre application initial selector aux source writer prior parent key target nonce next sender route read)
          client).run ([], before)] {true} := by
  have flags := congrArg (fun work => (fun result => result.2.2) <$> work)
    (marked_program_erased pre application initial selector aux source writer prior parent key target nonce next sender route read
      client (([], before), false))
  simp only [Functor.map_map, Prod.map_def, id_eq, forgetHistory] at flags
  rw [← flags]
  have histories := congrArg (fun work => (fun result => decide (RawCtxSelectedSourceSendInputs.RepeatedInput target result.2.1)) <$> work)
    (RawCtxSelectedFamilyNonceCoupling.marked_client
      (observed pre application initial selector aux source writer prior parent key target nonce next sender route read)
      (observedStops (extra := extra) prior parent target nonce next sender) client (([], before), false))
  simp only [Functor.map_map, Prod.map_def, id_eq] at histories
  rw [← histories]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  simp only [decide_eq_true_eq]
  apply prEvent_mono_of_support
  intro result supported flagged
  have consistent := marked_program_consistent pre application initial selector aux source writer prior parent key target nonce next
    sender route read client (([], before), false) result supported
    ⟨RawCtxSelectedSendTrace.tracked_empty before.2 empty, fun _ impossible => False.elim (List.not_mem_nil impossible),
      fun impossible => False.elim (Bool.false_ne_true impossible)⟩
  exact routed_input prior parent target nonce next result.2.1.1 consistent.2.1 (consistent.2.2 flagged)

/-- The complete post source and the evaluated executable CTX post differ by at most the probability of a repeated selected sending input in the same observed run, with coefficient one and complete terminal output and state comparison. -/
theorem source_input_distance (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Full M P I D K A N C S B) (empty : before.2.selected.1.usedNonces = []) :
    tvDist
      ((simulateQ (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next
        sender route read) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (PqxdhSelectedPostCompiler.project before))
      (Prod.map id PqxdhSelectedPostCompiler.project <$> (PqxdhSelectedStateInterpreter.evaluate
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (simulateQ (PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer prior parent target nonce next
          sender route read) work).run).run before) ≤
      (𝒟[(fun result => decide (RawCtxSelectedSourceSendInputs.RepeatedInput target result.2.1)) <$>
        (simulateQ (observed pre application initial selector aux source writer prior parent key target nonce next sender route read)
          (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run ([], before)] {true}).toReal := by
  apply (PqxdhSelectedPostCompiler.source_distance pre application initial selector aux source writer prior parent key target nonce next
    sender route read work before).trans
  apply ENNReal.toReal_mono
  · rw [← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  · exact input_bound pre application initial selector aux source writer prior parent key target nonce next sender route read
      (RawCtxSelectedFamilyNonceCoupling.optionalClient work) before empty

/-- The stop probability is at most the probability of two ordered sealing positions at the exact selected sending chain in the history-extended original source post, which has no CTX component or selected-nonce ledger. -/
theorem source_input_bound (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : Full M P I D K A N C S B) (empty : before.2.selected.1.usedNonces = []) :
    𝒟[(fun result => result.2.2) <$> (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
      (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next
        sender route read)
      (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender)) client).run (before, false)] {true} ≤
      𝒟[(fun result => decide (RawCtxSelectedSourceSendInputs.RepeatedInput target result.2.1)) <$>
        (simulateQ (sourceObserved pre application initial selector aux source writer prior parent key target nonce next sender route read)
          client).run ([], PqxdhSelectedPostCompiler.project before)] {true} := by
  have projected := congrArg (fun work => (fun result => decide (RawCtxSelectedSourceSendInputs.RepeatedInput target result.2.1)) <$> work)
    (source_observed_program pre application initial selector aux source writer prior parent key target nonce next sender route read
      client ([], before))
  simp only [Functor.map_map, Prod.map_def, id_eq, projectObserved] at projected
  rw [← projected]
  exact input_bound pre application initial selector aux source writer prior parent key target nonce next sender route read
    client before empty

/-- The complete post source and the evaluated executable CTX post differ by at most the probability of a repeated selected sending input in the history-extended original source post from the projected state, with coefficient one and complete terminal output and state comparison. -/
theorem source_history_distance (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Full M P I D K A N C S B) (empty : before.2.selected.1.usedNonces = []) :
    tvDist
      ((simulateQ (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next
        sender route read) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (PqxdhSelectedPostCompiler.project before))
      (Prod.map id PqxdhSelectedPostCompiler.project <$> (PqxdhSelectedStateInterpreter.evaluate
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (simulateQ (PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer prior parent target nonce next
          sender route read) work).run).run before) ≤
      (𝒟[(fun result => decide (RawCtxSelectedSourceSendInputs.RepeatedInput target result.2.1)) <$>
        (simulateQ (sourceObserved pre application initial selector aux source writer prior parent key target nonce next sender route read)
          (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run ([], PqxdhSelectedPostCompiler.project before)] {true}).toReal := by
  apply (PqxdhSelectedPostCompiler.source_distance pre application initial selector aux source writer prior parent key target nonce next
    sender route read work before).trans
  apply ENNReal.toReal_mono
  · rw [← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  · exact source_input_bound pre application initial selector aux source writer prior parent key target nonce next sender route read
      (RawCtxSelectedFamilyNonceCoupling.optionalClient work) before empty

end Bound

end BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.external_nonseal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.external_nonseal
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.finish_nonseal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.finish_nonseal
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.evaluate_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.evaluate_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.step_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.step_used
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.erased_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.erased_step
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.erased_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.erased_program
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.observed_source
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.marked_step_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.marked_step_consistent
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.marked_program_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.marked_program_consistent
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.marked_step_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.marked_step_erased
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.marked_program_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.marked_program_erased
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.routed_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.routed_input
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.input_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.input_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_input_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_input_distance
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_observed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_observed_step
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_observed_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_observed_program
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_input_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_input_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_history_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_history_distance
/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_erased_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop.source_erased_program
