import BeaconcryptCore.Computational.RawCtxSourceEventRecorder
import BeaconcryptCore.Computational.RawCtxFamilyStateInvariant

/-!
The original family callbacks interpret the concrete send-event recorder in their actual shared source service. This supplies source routing evidence for the same privately labelled owner and complete state used by the native family audit.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open RawCtxSelectedFamilyAudit RawCtxSelectedDriverAudit
open RawCtxProtocolReveals (Owner)
variable {A M P I D K Result : Type} {S B : Nat}

noncomputable def interpreter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    QueryImpl (RawCtxSelectedFamilyAudit.Spec S B)
      (StateT (List (Event (Owner S B)) × RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  RawCtxSourceEventRecorder.record (sourceServices source writer prior parent key target nonce next)

/-- The actual family send-service injection preserves the original source interpreter and complete private audit. -/
theorem send_lift (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    interpreter (A := A) (S := S) (B := B) source writer prior parent key target nonce next ∘ₛ RawCtxSelectedFamilyAudit.sendLift =
      RawCtxSourceEventRecorder.record (sendServices source writer prior parent key target nonce next) := by
  funext query
  cases query <;>
    simp only [QueryImpl.compose, RawCtxSelectedFamilyAudit.sendLift, simulateQ_spec_query,
      interpreter]
  all_goals rfl

/-- The original family send callback has the same retained source events as the concrete scalar send, with its full optional ciphertext and shared state. -/
theorem send_observed (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner S B) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (history : List (Event (Owner S B))) (state : RawCtxSharedPrimitive.SharedState A) :
    (fun result => (some result.1, result.2)) <$>
      (simulateQ (interpreter source writer prior parent key target nonce next)
        ((ownedCalls parent target nonce next owner).send entry context)).run (history, state) =
      RawCtxSelectedSendEvents.executed source writer prior parent key target nonce next owner entry context history state := by
  simp only [ownedCalls, ← QueryImpl.simulateQ_compose, send_lift]
  exact (RawCtxSourceEventRecorder.program (sendServices source writer prior parent key target nonce next)
    (RawCtxSelectedDriverAudit.send owner entry parent target nonce next context) history state).symm

/-- The concrete family's original source send appends exactly the scalar source trailer, including an unsuccessful writer and all retained shared state. -/
theorem send_history (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner S B) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (history afterHistory : List (Event (Owner S B))) (state after : RawCtxSharedPrimitive.SharedState A)
    (reply : RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted)
    (supported : (reply, (afterHistory, after)) ∈ support
      ((simulateQ (interpreter source writer prior parent key target nonce next)
        ((ownedCalls parent target nonce next owner).send entry context)).run (history, state))) :
    afterHistory = history ++ RawCtxSelectedSendEvents.events prior parent target nonce next owner entry context := by
  apply RawCtxSelectedSendEvents.history_exact source writer prior parent key target nonce next owner entry context
    history afterHistory state after (some reply)
  rw [← send_observed, support_map]
  exact ⟨(reply, (afterHistory, after)), supported, rfl⟩

def RoutedHistory (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (history : List (Event (Owner S B))) : Prop :=
  ∀ occurrence, Event.sealing occurrence ∈ history →
    RawCtxSelectedSendTrace.Routed (RawCtxSelectedSendEvents.route prior parent target nonce next) occurrence

/-- The actual source send preserves routing provenance for every recorded seal, with no distinct-event, honest-owner or unique-chain premise. -/
theorem send_preserves (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner S B) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (history afterHistory : List (Event (Owner S B))) (state after : RawCtxSharedPrimitive.SharedState A)
    (reply : RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted)
    (supported : (reply, (afterHistory, after)) ∈ support
      ((simulateQ (interpreter source writer prior parent key target nonce next)
        ((ownedCalls parent target nonce next owner).send entry context)).run (history, state)))
    (valid : RoutedHistory prior parent target nonce next history) :
    RoutedHistory prior parent target nonce next afterHistory := by
  intro occurrence found
  rw [send_history source writer prior parent key target nonce next owner entry context history afterHistory state after reply supported] at found
  rcases List.mem_append.mp found with old | current
  · exact valid occurrence old
  · exact (RawCtxSelectedSendEvents.sealing_routed prior parent target nonce next owner entry context occurrence current).2.2

/-- Every original receive-driver callback emits no private sealing event, including every derivation and arbitrary opening reply. -/
theorem receive_query_quiet (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner S B) (entry : RawCtxSelectedMessageReveals.Kernel)
    (query : (RawCtxInterpretedReceive.ReceiveSpec RawCtxSelectedMessageKey.Slot
      RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).Domain) :
    IsQueryBoundP (simulateQ RawCtxSelectedFamilyAudit.receiveLift
      (RawCtxSelectedDriverAudit.receiveCompiler owner entry parent target nonce next query))
        (RawCtxSourceEventRecorder.IsSeal (base := Services)) 0 := by
  cases query with
  | inl request =>
      simp only [RawCtxSelectedDriverAudit.receiveCompiler, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, RawCtxSelectedFamilyAudit.receiveLift, ← QueryImpl.simulateQ_compose]
      apply isQueryBoundP_bind (n := 0) (m := 0)
      · exact (isQueryBoundP_false (derive parent target nonce next request) 0).simulateQ_of_step
          (fun _ impossible => False.elim impossible)
          (fun address _ => by
            simp only [QueryImpl.compose, simulateQ_spec_query, RawCtxSelectedFamilyAudit.receiveLift]
            exact (isQueryBoundP_query_iff (spec := RawCtxSelectedFamilyAudit.Spec S B)
              (p := RawCtxSourceEventRecorder.IsSeal (base := Services)) _ 0).mpr (by simp [RawCtxSourceEventRecorder.IsSeal]))
      · intro reply _
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp [RawCtxSourceEventRecorder.IsSeal]), fun _ => by trivial⟩
  | inr pending =>
      simp only [RawCtxSelectedDriverAudit.receiveCompiler, simulateQ_spec_query, RawCtxSelectedFamilyAudit.receiveLift]
      exact (isQueryBoundP_query_iff (spec := RawCtxSelectedFamilyAudit.Spec S B)
        (p := RawCtxSourceEventRecorder.IsSeal (base := Services)) _ 0).mpr (by simp [RawCtxSourceEventRecorder.IsSeal])

/-- The complete cached or future receive emits no sealing event along any callback reply path. -/
theorem receive_quiet (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner S B) (entry : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    ((ownedCalls parent target nonce next owner).receive entry sequence context).IsQueryBoundP
      (RawCtxSourceEventRecorder.IsSeal (base := Services)) 0 := by
  simp only [ownedCalls, RawCtxSelectedDriverAudit.receive, ← QueryImpl.simulateQ_compose]
  exact (isQueryBoundP_false (RawCtxInterpretedReceive.receive entry sequence context) 0).simulateQ_of_step
    (fun _ impossible => False.elim impossible)
    (fun query _ => receive_query_quiet parent target nonce next owner entry query)

/-- An actual receive preserves all previously recorded seal occurrences and their source routing evidence. -/
theorem receive_preserves (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner S B) (entry : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (history afterHistory : List (Event (Owner S B))) (state after : RawCtxSharedPrimitive.SharedState A)
    (reply : RawCtxSelectedMessageReveals.Kernel × core.option.Option RawCtxWholeOwner.Decrypted)
    (supported : (reply, (afterHistory, after)) ∈ support
      ((simulateQ (interpreter source writer prior parent key target nonce next)
        ((ownedCalls parent target nonce next owner).receive entry sequence context)).run (history, state)))
    (valid : RoutedHistory prior parent target nonce next history) :
    RoutedHistory prior parent target nonce next afterHistory := by
  have same := RawCtxSourceEventRecorder.nonseal_program
    (sourceServices source writer prior parent key target nonce next)
    ((ownedCalls parent target nonce next owner).receive entry sequence context)
    (receive_quiet parent target nonce next owner entry sequence context)
    history state (reply, (afterHistory, after)) supported
  intro occurrence found
  apply valid occurrence
  apply (RawCtxSourceEventRecorder.mem_seals history occurrence).mp
  rw [← same]
  exact (RawCtxSourceEventRecorder.mem_seals afterHistory occurrence).mpr found

/-- Public services keep the entire private seal list while preserving their own actual replies and shared-state effects. -/
theorem public_preserves (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (query : RawCtxServerServices.PublicSpec.Domain)
    (history afterHistory : List (Event (Owner S B))) (state after : RawCtxSharedPrimitive.SharedState A)
    (reply : RawCtxServerServices.PublicSpec.Range query)
    (supported : (reply, (afterHistory, after)) ∈ support
      ((simulateQ (interpreter source writer prior parent key target nonce next)
        (publicService query)).run (history, state))) :
    afterHistory = history := by
  simp only [publicService, simulateQ_spec_query, interpreter, RawCtxSourceEventRecorder.record,
    StateT.run, support_map] at supported
  obtain ⟨result, _, same⟩ := supported
  exact (congrArg (fun value => value.2.1) same).symm

private theorem rules (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    RawCtxFamilyStateInvariant.Rules
      (RawCtxGenericOwnerInterpretation.interpretedCalls
        (interpreter (A := A) source writer prior parent key target nonce next)
        (calls (S := S) (B := B) parent target nonce next))
      (fun before after => RoutedHistory prior parent target nonce next before.1 →
        RoutedHistory prior parent target nonce next after.1) (fun _ _ => True) := by
  constructor
  · intro state valid
    exact valid
  · intro before middle after first later valid
    exact later (first valid)
  · intros
    trivial
  · intro entry sequence context state result supported
    simp only [RawCtxGenericOwnerInterpretation.interpretedCalls, calls, RawCtxOwnerLabels.calls,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact ⟨receive_preserves source writer prior parent key target nonce next entry.1 entry.2
      sequence context state.1 reply.2.1 state.2 reply.2.2 reply.1 reached, fun _ => True.intro⟩
  · intro entry context state result supported
    simp only [RawCtxGenericOwnerInterpretation.interpretedCalls, calls, RawCtxOwnerLabels.calls,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact ⟨send_preserves source writer prior parent key target nonce next entry.1 entry.2
      context state.1 reply.2.1 state.2 reply.2.2 reply.1 reached, fun _ => True.intro⟩

/-- Every actual Server, Beacon or public operation preserves routing evidence for all recorded seal occurrences, even when either role family is empty. -/
theorem family_preserves (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (roles : RawCtxSelectedFamilySourceAudit.Roles M P I D K S B)
    (history : List (Event (Owner S B))) (state : RawCtxSharedPrimitive.SharedState A)
    (result : ((RawCtxProtocolRoles.SourceSpec S B).Range query × RawCtxSelectedFamilySourceAudit.Roles M P I D K S B) ×
      (List (Event (Owner S B)) × RawCtxSharedPrimitive.SharedState A))
    (supported : result ∈ support ((simulateQ (interpreter source writer prior parent key target nonce next)
      ((frontend parent target nonce next sender route decode query).run roles)).run (history, state)))
    (valid : RoutedHistory prior parent target nonce next history) :
    RoutedHistory prior parent target nonce next result.2.1 := by
  have publicKept : ∀ request before result,
      result ∈ support ((simulateQ (interpreter (A := A) source writer prior parent key target nonce next)
        (publicService (S := S) (B := B) request)).run before) →
      RoutedHistory prior parent target nonce next before.1 → RoutedHistory prior parent target nonce next result.2.1 := by
    intro request before result reached initial
    rw [public_preserves source writer prior parent key target nonce next request before.1 result.2.1 before.2 result.2.2 result.1 reached]
    exact initial
  rw [frontend, RawCtxGenericFamilyInterpretation.step_interpretation] at supported
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  · exact (RawCtxFamilyStateInvariant.family _ _ _
      (rules source writer prior parent key target nonce next) _ publicKept sender route decode _ roles
      (history, state) result supported (.server index 0#u64)).1 valid
  · exact (RawCtxFamilyStateInvariant.family _ _ _
      (rules source writer prior parent key target nonce next) _ publicKept sender route decode _ roles
      (history, state) result supported (.beacon index)).1 valid
  · simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at supported
    change result ∈ support (((fun reply => (reply, roles)) <$>
      simulateQ (interpreter source writer prior parent key target nonce next) (publicService request)).run (history, state)) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact publicKept request (history, state) reply reached valid

/-- The complete adaptive record/public schedule preserves source routing evidence in its actual retained audit, including every failed send and rejected receive. -/
theorem schedule_preserves (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result)
    (roles : RawCtxSelectedFamilySourceAudit.Roles M P I D K S B)
    (history : List (Event (Owner S B))) (state : RawCtxSharedPrimitive.SharedState A)
    (result : (Result × RawCtxSelectedFamilySourceAudit.Roles M P I D K S B) ×
      (List (Event (Owner S B)) × RawCtxSharedPrimitive.SharedState A))
    (supported : result ∈ support ((simulateQ (interpreter source writer prior parent key target nonce next)
      ((simulateQ (frontend parent target nonce next sender route decode) client).run roles)).run (history, state)))
    (valid : RoutedHistory prior parent target nonce next history) :
    RoutedHistory prior parent target nonce next result.2.1 := by
  induction client using OracleComp.inductionOn generalizing roles history state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact valid
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, reached, tail⟩ := supported
      exact ih reply.1.1 reply.1.2 reply.2.1 reply.2.2 result tail
        (family_preserves source writer prior parent key target nonce next sender route decode query
          roles history state reply reached valid)

/-- The same complete audit used by the checked native-source equation carries the routing invariant through the entire adaptive family schedule. -/
theorem observed_routed (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result)
    (roles : RawCtxSelectedFamilySourceAudit.Roles M P I D K S B)
    (history : List (Event (Owner S B))) (state : RawCtxSharedPrimitive.SharedState A)
    (result : Option (Result × RawCtxSelectedFamilySourceAudit.Roles M P I D K S B) ×
      (List (Event (Owner S B)) × RawCtxSharedPrimitive.SharedState A))
    (supported : result ∈ support (RawCtxSelectedFamilySourceAudit.observed source writer prior parent key target nonce next
      sender route decode client roles history state))
    (valid : RoutedHistory prior parent target nonce next history) :
    RoutedHistory prior parent target nonce next result.2.1 := by
  have same : RawCtxSelectedFamilySourceAudit.observed source writer prior parent key target nonce next
      sender route decode client roles history state =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ (interpreter source writer prior parent key target nonce next)
          ((simulateQ (frontend parent target nonce next sender route decode) client).run roles)).run (history, state) :=
    RawCtxSourceEventRecorder.program (sourceServices source writer prior parent key target nonce next) _ history state
  rw [same, support_map] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  exact schedule_preserves source writer prior parent key target nonce next sender route decode client
    roles history state reply reached valid

/-- Every selected seal in an actual family audit started empty has original admission/ready evidence and the exact selected sending input. Duplicate event values, failed writers and attacker-owned role entries remain allowed. -/
theorem selected_chain (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result)
    (roles : RawCtxSelectedFamilySourceAudit.Roles M P I D K S B) (state : RawCtxSharedPrimitive.SharedState A)
    (result : Option (Result × RawCtxSelectedFamilySourceAudit.Roles M P I D K S B) ×
      (List (Event (Owner S B)) × RawCtxSharedPrimitive.SharedState A))
    (supported : result ∈ support (RawCtxSelectedFamilySourceAudit.observed source writer prior parent key target nonce next
      sender route decode client roles [] state))
    (occurrence : RawCtxSelectedSendTrace.Occurrence (Owner S B))
    (found : Event.sealing occurrence ∈ result.2.1)
    (value : NonceOutput) (selected : RawCtxSelectedSendTrace.nonce occurrence.pending = some value) :
    RawCtxSelectedSendTrace.Routed (RawCtxSelectedSendEvents.route prior parent target nonce next) occurrence ∧
      occurrence.entry.send_chain = RawCtxFreshChainCut.concreteChain target ∧
      ∀ predecessor, parent = some predecessor →
        RawCtxSelectedPendingCut.requestAddress occurrence.entry.send_chain ≠ predecessor.address := by
  have provenance := observed_routed source writer prior parent key target nonce next sender route decode client
    roles [] state result supported (by intro item impossible; cases impossible)
  have routed := provenance occurrence found
  refine ⟨routed, ?_⟩
  cases parent with
  | none =>
      refine ⟨RawCtxSelectedSendTrace.routed_chain prior target next nonce value occurrence routed selected, ?_⟩
      intro _ impossible
      cases impossible
  | some predecessor =>
      have actual := RawCtxSelectedSendTrace.later_routed_chain prior predecessor target next nonce value occurrence routed selected
      refine ⟨actual.2, ?_⟩
      intro candidate equal
      cases equal
      exact actual.1

end BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.send_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.send_lift

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.send_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.send_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.send_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.send_history

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.send_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.send_preserves

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.receive_query_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.receive_query_quiet

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.receive_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.receive_quiet

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.receive_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.receive_preserves

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.public_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.public_preserves

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.family_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.family_preserves

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.schedule_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.schedule_preserves

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.observed_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.observed_routed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.selected_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents.selected_chain
