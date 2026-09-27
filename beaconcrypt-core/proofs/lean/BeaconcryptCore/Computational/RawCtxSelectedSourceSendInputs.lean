import BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent

/-!
The nonce-event history carries actual source sending inputs. Admission and owner labels come from the original role dispatch; selected-input attribution follows the literal source trailer rather than an assumption about arbitrary audit entries.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedDriverAudit
open RawCtxSelectedRoleAuditLedger RawCtxSelectedLiveAuditLedger
variable {Owner Metadata A M P I D K Result : Type} {S B : Nat}

private theorem owner_routed (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (label : Owner) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxChainOwner.State RawCtxSelectedOwnerCompiler.Kernel Metadata)
    (occurrence : RawCtxSelectedSendTrace.Occurrence Owner)
    (found : Event.sealing occurrence ∈ ownerEvents prior parent target nonce next label sender query entry) :
    RawCtxSelectedSendTrace.Routed (RawCtxSelectedSendEvents.route prior parent target nonce next) occurrence := by
  cases query with
  | inr raw => simp only [ownerEvents, List.not_mem_nil] at found
  | inl plaintext =>
      dsimp only [ownerEvents] at found
      split at found
      · exact False.elim (List.not_mem_nil found)
      · exact (RawCtxSelectedSendEvents.sealing_routed prior parent target nonce next label entry.kernel
          ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩ occurrence found).2.2

private theorem beacon_routed (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (label : Owner)
    (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedOwnerCompiler.Kernel I D K)
    (occurrence : RawCtxSelectedSendTrace.Occurrence Owner)
    (found : Event.sealing occurrence ∈ beaconEvents prior parent target nonce next label query entry) :
    RawCtxSelectedSendTrace.Routed (RawCtxSelectedSendEvents.route prior parent target nonce next) occurrence := by
  cases phase : entry.beacon.phase
  case established control ad kernel =>
    simp only [beaconEvents, phase] at found
    exact owner_routed prior parent target nonce next label entry.beacon.identityKeyId query
      (RawCtxGenericBeacon.selected entry control ad kernel) occurrence found
  all_goals simp only [beaconEvents, phase, List.not_mem_nil] at found

private theorem server_routed (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (label : Std.U64 → Owner) (sender : M → Std.U64)
    (query : RawCtxServerMixed.SourceSpec.Domain)
    (entry : RawCtxGenericRoleStorage.ServerState RawCtxSelectedOwnerCompiler.Kernel M P)
    (occurrence : RawCtxSelectedSendTrace.Occurrence Owner)
    (found : Event.sealing occurrence ∈ serverEvents prior parent target nonce next label sender query entry) :
    RawCtxSelectedSendTrace.Routed (RawCtxSelectedSendEvents.route prior parent target nonce next) occurrence := by
  cases query with
  | inr raw => simp only [serverEvents, List.not_mem_nil] at found
  | inl request =>
      rcases request with ⟨plaintext, kid⟩
      cases associated : RawCtxGenericServer.peerAssociatedData entry.server kid with
      | none => simp only [serverEvents, associated, List.not_mem_nil] at found
      | some ad =>
          cases peerFound : entry.server.peers kid with
          | none => simp only [serverEvents, associated, peerFound, List.not_mem_nil] at found
          | some peer =>
              simp only [serverEvents, associated, peerFound] at found
              exact owner_routed prior parent target nonce next (label kid) (sender entry.server.metadata) (.inl plaintext)
                (RawCtxGenericServer.selectedOwner kid ad peer entry.rawAttempts) occurrence found

/-- The actual live callback's trailer supplies every seal's source admission and ready capability, including original role dispatch and all rejection branches. -/
theorem callback_routed (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (entry : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B) :
    RawCtxSelectedFamilySendEvents.RoutedHistory prior parent target nonce next
      (events prior parent target nonce next sender query entry) := by
  intro occurrence found
  cases query with
  | inr request => simp only [events, List.not_mem_nil] at found
  | inl request =>
      rcases request with ⟨index, request⟩ | (⟨index, request⟩ | request)
      · exact server_routed prior parent target nonce next
          (RawCtxProtocolReveals.Owner.server index : Std.U64 → RawCtxProtocolReveals.Owner S B)
          sender request (entry.1.1 index) occurrence found
      · exact beacon_routed prior parent target nonce next
          (RawCtxProtocolReveals.Owner.beacon index : RawCtxProtocolReveals.Owner S B)
          request (entry.1.2 index) occurrence found
      · simp only [events, familyEvents, List.not_mem_nil] at found

/-- The concrete augmented source callback preserves routing evidence in exactly the history used by the nonce probability comparison. -/
theorem step_routed (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxSelectedFamilyNonceCoupling.Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain)
    (before : State M P I D K A S B)
    (result : (RawCtxSelectedFamilyNonceCoupling.Optional (RawCtxProtocolReveals.SourceSpec S B)).Range query × State M P I D K A S B)
    (supported : result ∈ support ((observed source writer prior parent key target nonce next sender route read query).run before))
    (previous : RawCtxSelectedFamilySendEvents.RoutedHistory prior parent target nonce next before.1) :
    RawCtxSelectedFamilySendEvents.RoutedHistory prior parent target nonce next result.2.1 := by
  simp only [RawCtxSelectedLiveAuditLedger.observed, StateT.run, support_map] at supported
  obtain ⟨reply, _, rfl⟩ := supported
  intro occurrence found
  rcases List.mem_append.mp found with old | current
  · exact previous occurrence old
  · exact callback_routed prior parent target nonce next sender query before.2.1 occurrence current

/-- Every complete adaptive optional-interface source program retains the original admission evidence for its recorded sends. -/
theorem program_routed (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxSelectedFamilyNonceCoupling.Optional (RawCtxProtocolReveals.SourceSpec S B)) Result)
    (before : State M P I D K A S B) (result : Result × State M P I D K A S B)
    (supported : result ∈ support ((simulateQ (observed source writer prior parent key target nonce next sender route read) client).run before))
    (previous : RawCtxSelectedFamilySendEvents.RoutedHistory prior parent target nonce next before.1) :
    RawCtxSelectedFamilySendEvents.RoutedHistory prior parent target nonce next result.2.1 := by
  induction client using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact previous
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, reached, tail⟩ := supported
      exact ih reply.1 reply.2 result tail
        (step_routed source writer prior parent key target nonce next sender route read query before reply reached previous)

/-- Every selected seal in the actual nonce-event execution uses the exact selected sending input, and cannot bypass retained-predecessor priority. The empty history supplies the routing invariant. -/
theorem selected_input (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce value : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxSelectedFamilyNonceCoupling.Optional (RawCtxProtocolReveals.SourceSpec S B)) Result)
    (before : RawCtxSelectedFamilyNonceCoupling.Full M P I D K A S B) (result : Result × State M P I D K A S B)
    (supported : result ∈ support ((simulateQ (observed source writer prior parent key target nonce next sender route read) client).run ([], before)))
    (occurrence : RawCtxSelectedSendTrace.Occurrence (RawCtxProtocolReveals.Owner S B))
    (found : Event.sealing occurrence ∈ result.2.1)
    (selected : RawCtxSelectedSendTrace.nonce occurrence.pending = some value) :
    occurrence.entry.send_chain = RawCtxFreshChainCut.concreteChain target ∧
      ∀ predecessor, parent = some predecessor →
        RawCtxSelectedPendingCut.requestAddress occurrence.entry.send_chain ≠ predecessor.address := by
  have routed := program_routed source writer prior parent key target nonce next sender route read client
    ([], before) result supported (fun _ impossible => False.elim (List.not_mem_nil impossible)) occurrence found
  cases parent with
  | none =>
      refine ⟨RawCtxSelectedSendTrace.routed_chain prior target next nonce value occurrence routed selected, ?_⟩
      intro _ impossible
      cases impossible
  | some predecessor =>
      have chain := RawCtxSelectedSendTrace.later_routed_chain prior predecessor target next nonce value occurrence routed selected
      refine ⟨chain.2, ?_⟩
      intro candidate same
      cases same
      exact chain.1

/-- The repeated source nonce event supplies two ordered positions in its literal sealing history, without requiring different occurrence values. -/
theorem repeated_positions (history : List (Event Owner))
    (repeated : RawCtxSelectedNonceSourceEvent.Repeated history) :
    ∃ i j : Fin (RawCtxSourceEventRecorder.seals history).length, i.val < j.val ∧
      ∃ value, RawCtxSelectedSendTrace.nonce ((RawCtxSourceEventRecorder.seals history).get i).pending = some value ∧
        RawCtxSelectedSendTrace.nonce ((RawCtxSourceEventRecorder.seals history).get j).pending = some value := by
  classical
  change ¬ ((RawCtxSourceEventRecorder.seals history).filterMap
    (fun occurrence => RawCtxSelectedSendTrace.nonce occurrence.pending)).Nodup at repeated
  rw [List.nodup_iff_pairwise_ne, List.pairwise_filterMap, List.pairwise_iff_getElem] at repeated
  push Not at repeated
  obtain ⟨i, j, hi, hj, order, value, earlier, later, current, same⟩ := repeated
  subst later
  exact ⟨⟨i, hi⟩, ⟨j, hj⟩, order, value, earlier, current⟩

/-- Two distinct chronological source sealing positions use the same selected sending-chain input. The occurrence values and owner labels may coincide. -/
def RepeatedInput (target : RootOutput) (history : List (Event Owner)) : Prop :=
  ∃ i j : Fin (RawCtxSourceEventRecorder.seals history).length, i.val < j.val ∧
    ((RawCtxSourceEventRecorder.seals history).get i).entry.send_chain = RawCtxFreshChainCut.concreteChain target ∧
    ((RawCtxSourceEventRecorder.seals history).get j).entry.send_chain = RawCtxFreshChainCut.concreteChain target

/-- The repeated nonce event in an actually executed source schedule implies repeated visits to the exact selected sending input at ordered source positions. -/
theorem repeated_input (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxSelectedFamilyNonceCoupling.Optional (RawCtxProtocolReveals.SourceSpec S B)) Result)
    (before : RawCtxSelectedFamilyNonceCoupling.Full M P I D K A S B) (result : Result × State M P I D K A S B)
    (supported : result ∈ support ((simulateQ (observed source writer prior parent key target nonce next sender route read) client).run ([], before)))
    (repeated : RawCtxSelectedNonceSourceEvent.Repeated result.2.1) : RepeatedInput target result.2.1 := by
  obtain ⟨i, j, order, value, earlier, current⟩ := repeated_positions result.2.1 repeated
  refine ⟨i, j, order, ?_, ?_⟩
  · exact (selected_input source writer prior parent key target nonce value next sender route read client before result supported
      _ ((RawCtxSourceEventRecorder.mem_seals _ _).mp (List.get_mem _ i)) earlier).1
  · exact (selected_input source writer prior parent key target nonce value next sender route read client before result supported
      _ ((RawCtxSourceEventRecorder.mem_seals _ _).mp (List.get_mem _ j)) current).1

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual nonce refusal is charged once to ordered repeated selected inputs in the same source run. This event still requires its source path and origin probability analysis. -/
theorem nonce_input_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxSelectedFamilyNonceCoupling.Optional (RawCtxProtocolReveals.SourceSpec S B)) Result)
    (before : RawCtxSelectedFamilyNonceCoupling.Full M P I D K A S B)
    (empty : before.2.2.selected.1.usedNonces = []) :
    𝒟[(fun result => result.2.2) <$> (simulateQ
      (RawCtxSelectedFamilyNonceCoupling.marked
        (RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read)
        (RawCtxSelectedFamilyNonceCoupling.nonceBad prior parent target nonce next sender)) client).run (before, false)] {true} ≤
      𝒟[(fun result => decide (RepeatedInput target result.2.1)) <$>
        (simulateQ (observed source writer prior parent key target nonce next sender route read) client).run ([], before)] {true} := by
  apply (RawCtxSelectedNonceSourceEvent.nonce_event_bound source writer prior parent key target nonce next sender route read client before empty).trans
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def, decide_eq_true_eq]
  exact probEvent_mono (fun result supported repeated =>
    repeated_input source writer prior parent key target nonce next sender route read client before result supported repeated)

/-- The whole source-to-executable CTX comparison is bounded by this source sending-input event with coefficient one and complete state retention. -/
theorem executable_distance (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (before : RawCtxSelectedFamilyNonceCoupling.Full M P I D K A S B)
    (empty : before.2.2.selected.1.usedNonces = []) :
    tvDist
      (((simulateQ (RawCtxSelectedMessageStopping.stopping
        (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read)) client).run).run
        (RawCtxSelectedFamilyNonceCoupling.project before))
      ((fun result => (result.1.1, RawCtxSelectedFamilyNonceCoupling.project (result.1.2, result.2))) <$>
        (RawCtxSelectedReceiveCompiler.evaluated source key read
          (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before.1)).run before.2) ≤
      (𝒟[(fun result => decide (RepeatedInput target result.2.1)) <$>
        (simulateQ (observed source writer prior parent key target nonce next sender route read)
          (RawCtxSelectedFamilyNonceCoupling.optionalClient client)).run ([], before)] {true}).toReal := by
  apply (RawCtxSelectedFamilyNonceCoupling.executable_distance source writer prior parent key target nonce next sender route read client before).trans
  apply ENNReal.toReal_mono
  · simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput]
    exact probEvent_ne_top
  · exact nonce_input_bound source writer prior parent key target nonce next sender route read
      (RawCtxSelectedFamilyNonceCoupling.optionalClient client) before empty

end BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.callback_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.callback_routed
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.step_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.step_routed
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.program_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.program_routed
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.selected_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.selected_input
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.repeated_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.repeated_positions
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.repeated_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.repeated_input
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.nonce_input_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.nonce_input_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.executable_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs.executable_distance
