import BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog

/-! Successful original frontend sends retain the exact pre-send input in the same audited backend. Admission, publication and optional results remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog
open PqxdhJointKdf PqxdhJointKdfGame PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
local notation "Spec" => PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B
local notation "Backend" => PqxdhInitialNativeAudit.State A N C
local notation "impl" => PqxdhInitialNativeAudit.handler (S := S) (B := B) source writer stage pre application initial selector aux

local notation "calls" => RawCtxGenericOwnerInterpretation.interpretedCalls
  (impl ∘ₛ PqxdhInitialPendingPost.primitiveForward) RawCtxPendingOwnerQueries.calls

/-- The original owner admission and publication preserve the successful send's executed private input in the full backend history. -/
theorem owner_input {M : Type} (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (entry : RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel RatchetChain) M)
    (before : Backend)
    (result : (Option RawCtxSourceSend.Encrypted × RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel RatchetChain) M) × Backend)
    (supported : result ∈ support (((RawCtxChainOwner.sendOwner calls sender plaintext).run entry).run before))
    (record : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some record) :
    RawCtxSelectedPendingCut.requestAddress entry.kernel.send_chain ∈ result.2.1.1.2 := by
  unfold RawCtxChainOwner.sendOwner at supported
  by_cases empty : plaintext.isEmpty = true
  case neg =>
    simp only [empty, Bool.false_eq_true, ite_false, bind_pure_comp] at supported
    change result ∈ support (((fun reply => (reply.2, {entry with kernel := reply.1})) <$>
      (calls).send entry.kernel ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩).run before) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    apply PqxdhLaterChallengeInputLog.send_inputs (S := S) (B := B) source writer stage
      pre application initial selector aux entry.kernel
      ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩ before reply _ record returned
    simpa only [RawCtxGenericOwnerInterpretation.interpretedCalls, QueryImpl.simulateQ_compose] using reached
  case pos =>
    simp only [empty, ite_true] at supported
    subst result
    cases returned

open RawCtxGenericRoleStorage RawCtxProtocolReveals
local notation "Kernel" => RawCtxPendingOwnerQueries.Kernel RatchetChain

/-- Successful Server admission retains the actual requested peer's pre-send input in the same backend. -/
theorem server_input {M P : Type} (sender : M → Std.U64) (plaintext : Pqxdh.Bytes) (peer : Std.U64)
    (entry : ServerState Kernel M P) (before : Backend)
    (result : (Option RawCtxSourceSend.Encrypted × ServerState Kernel M P) × Backend)
    (supported : result ∈ support ((RawCtxGenericServer.sendServer calls sender plaintext peer entry).run before))
    (record : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some record) :
    ∃ kernel, (entry.server.peers peer).map Peer.kernel = some kernel ∧
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain ∈ result.2.1.1.2 := by
  unfold RawCtxGenericServer.sendServer at supported
  cases adFound : RawCtxGenericServer.peerAssociatedData entry.server peer with
  | some ad =>
      simp only [adFound] at supported
      cases peerFound : entry.server.peers peer with
      | some selected =>
          simp only [peerFound, bind_pure_comp] at supported
          change result ∈ support (((fun reply =>
            (reply.1, ⟨RawCtxGenericServer.putPeer entry.server peer selected reply.2.kernel,
              reply.2.rawAttempts⟩)) <$>
              (RawCtxChainOwner.sendOwner calls (sender entry.server.metadata) plaintext).run
                (RawCtxGenericServer.selectedOwner peer ad selected entry.rawAttempts)).run before) at supported
          rw [StateT.run_map, support_map] at supported
          obtain ⟨reply, reached, rfl⟩ := supported
          exact ⟨selected.kernel, rfl, owner_input source writer stage pre application initial selector aux
            _ _ _ _ _ reached record returned⟩
      | none =>
          simp only [peerFound, StateT.run_pure, mem_support_pure_iff] at supported
          subst result
          cases returned
  | none =>
      simp only [adFound, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      cases returned

/-- A successful Beacon send records the established pre-send kernel's input, including every actual primitive and writer effect. -/
theorem beacon_input (decode : RawCtxReceive.FrameDecoder) (plaintext : Pqxdh.Bytes)
    (entry : BeaconState Kernel I D K) (before : Backend)
    (result : (Option RawCtxSourceSend.Encrypted × BeaconState Kernel I D K) × Backend)
    (supported : result ∈ support (((RawCtxGenericBeacon.impl calls decode (.inl plaintext)).run entry).run before))
    (record : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some record) :
    ∃ control ad kernel, entry.beacon.phase = .established control ad kernel ∧
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain ∈ result.2.1.1.2 := by
  cases phase : entry.beacon.phase
  case established control ad kernel =>
    rw [RawCtxGenericBeacon.established calls decode (.inl plaintext) entry control ad kernel phase] at supported
    simp only [RawCtxChainOwner.ownerImpl, bind_pure_comp] at supported
    change result ∈ support (((fun reply =>
      (reply.1, RawCtxGenericBeacon.reinstall entry control ad reply.2)) <$>
        (RawCtxChainOwner.sendOwner calls entry.beacon.identityKeyId plaintext).run
          (RawCtxGenericBeacon.selected entry control ad kernel)).run before) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact ⟨control, ad, kernel, rfl, owner_input source writer stage pre application initial selector aux
      _ _ _ _ _ reached record returned⟩
  all_goals
    simp only [RawCtxGenericBeacon.impl, StateT.run, phase, RawCtxGenericBeacon.rejected] at supported
    subst result
    cases returned

/-- A publication by either original LIVE role identifies its actual pre-step kernel and the same executed private-input history. -/
theorem live_input {M P : Type}
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT Backend ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT Backend ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec S B).Domain) (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B)
    (before : Backend)
    (result : ((SourceSpec S B).Range query × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × Backend)
    (supported : result ∈ support (((RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode query).run entry).run before))
    (selected : Owner S B) (number : Std.U64)
    (recorded : (selected, number) ∈ RawCtxPublishedRecords.record query result.1.1) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel selected entry.1 = some kernel ∧
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain ∈ result.2.1.1.2 := by
  rcases query with (⟨index, request⟩ | (⟨index, request⟩ | publicQuery)) | readQuery
  case inl.inl =>
    cases request with
    | inl request =>
        rcases request with ⟨plaintext, peer⟩
        simp only [RawCtxGenericFamilyLive.impl, RawCtxGenericFamilyFrontend.impl, RawCtxGenericServer.serverImpl,
          StateT.run, bind_pure_comp, Functor.map_map] at supported
        change result ∈ support (((fun reply =>
          (reply.1, ((Function.update entry.1.1 index reply.2, entry.1.2), tick entry.2))) <$>
            RawCtxGenericServer.sendServer calls sender plaintext peer (entry.1.1 index)).run before) at supported
        rw [StateT.run_map, support_map] at supported
        obtain ⟨reply, reached, rfl⟩ := supported
        cases published : reply.1.1 with
        | some sent =>
            simp only [RawCtxPublishedRecords.record, published, List.mem_singleton, Prod.mk.injEq] at recorded
            rcases recorded with ⟨rfl, rfl⟩
            exact server_input source writer stage pre application initial selector aux sender plaintext peer
              _ before reply reached sent published
        | none =>
            simp only [RawCtxPublishedRecords.record, published, List.not_mem_nil] at recorded
    | inr raw =>
        simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded
  case inl.inr.inl =>
    cases request with
    | inl plaintext =>
        simp only [RawCtxGenericFamilyLive.impl, RawCtxGenericFamilyFrontend.impl,
          StateT.run, bind_pure_comp, Functor.map_map] at supported
        change result ∈ support (((fun reply =>
          (reply.1, ((entry.1.1, Function.update entry.1.2 index reply.2), tick entry.2))) <$>
            (RawCtxGenericBeacon.impl calls decode (.inl plaintext)).run (entry.1.2 index)).run before) at supported
        rw [StateT.run_map, support_map] at supported
        obtain ⟨reply, reached, rfl⟩ := supported
        cases published : reply.1.1 with
        | some sent =>
            simp only [RawCtxPublishedRecords.record, published, List.mem_singleton, Prod.mk.injEq] at recorded
            rcases recorded with ⟨rfl, rfl⟩
            obtain ⟨control, ad, kernel, phase, logged⟩ := beacon_input source writer stage pre application initial selector aux
              decode plaintext _ before reply reached sent published
            exact ⟨kernel, by simp only [RawCtxGenericRoleFamily.selectedKernel, phase], logged⟩
        | none =>
            simp only [RawCtxPublishedRecords.record, published, List.not_mem_nil] at recorded
    | inr raw =>
        simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded
  case inl.inr.inr =>
    simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded
  case inr =>
    simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded

private theorem live_forward :
    impl ∘ₛ PqxdhInitialPendingPost.liveForward = RawCtxPendingFamilyLiveQueries.handler
      (impl ∘ₛ PqxdhInitialPendingPost.primitiveForward)
      (fun query => impl (.inl (.inr query))) := by
  funext query
  cases query <;> simp [QueryImpl.compose, PqxdhInitialPendingPost.liveForward,
    PqxdhInitialPendingPost.primitiveForward, RawCtxPendingFamilyLiveQueries.handler, OracleSpec.query]

/-- The literal pending-query LIVE compiler retains the successful publication's same-state kernel and private-input log. -/
theorem pending_live_input {M P : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec S B).Domain) (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B)
    (before : Backend)
    (result : ((SourceSpec S B).Range query × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × Backend)
    (supported : result ∈ support ((simulateQ impl (simulateQ PqxdhInitialPendingPost.liveForward
      ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run entry))).run before))
    (selected : Owner S B) (number : Std.U64)
    (recorded : (selected, number) ∈ RawCtxPublishedRecords.record query result.1.1) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel selected entry.1 = some kernel ∧
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain ∈ result.2.1.1.2 := by
  rw [← QueryImpl.simulateQ_compose, live_forward source writer stage pre application initial selector aux,
    RawCtxPendingFamilyLiveQueries.step_interpretation] at supported
  exact live_input source writer stage pre application initial selector aux _ _ sender route decode
    query entry before result supported selected number recorded

/-- The original private-origin Post callback preserves the actual send input without erasing or reconstructing its frontend, publication trace or backend. -/
theorem origin_input {M P Origin : Type}
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec S B).Domain)
    (entry : PqxdhInitialPendingPost.Front RatchetChain M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)
    (before : Backend)
    (result : ((SourceSpec S B).Range query ×
      (PqxdhInitialPendingPost.Front RatchetChain M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) × Backend)
    (supported : result ∈ support ((simulateQ impl
      ((PqxdhInitialOriginPost.compiler mark sender route decode (.inl (.inl query))).run entry)).run before))
    (selected : Owner S B) (number : Std.U64)
    (recorded : (selected, number) ∈ RawCtxPublishedRecords.record query result.1.1) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel selected entry.1.roles.1 = some kernel ∧
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain ∈ result.2.1.1.2 := by
  simp only [PqxdhInitialOriginPost.compiler, StateT.run, bind_pure_comp, simulateQ_map] at supported
  change result ∈ support (((fun reply =>
    (reply.1, ({entry.1 with roles := reply.2}, PqxdhInitialOriginPost.record entry.2 query reply.1))) <$>
      simulateQ impl (simulateQ PqxdhInitialPendingPost.liveForward
        ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run entry.1.roles))).run before) at supported
  rw [StateT.run_map, support_map] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  exact pending_live_input source writer stage pre application initial selector aux sender route decode
    query entry.1.roles before reply reached selected number recorded

set_option backward.isDefEq.respectTransparency false in
/-- The unchanged challenge wrapper's successful source send records its actual pre-request kernel input. Both owner directions preserve the entire frontend, trace and audited backend. -/
theorem challenge_input {M P Origin : Type}
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : Owner S B) (plaintext : Pqxdh.Bytes)
    (before after : (PqxdhInitialPendingPost.Front RatchetChain M P I D K S B ×
      PqxdhInitialOriginPost.Trace Origin S B) × Backend)
    (record : RawCtxSourceSend.Encrypted)
    (supported : (some record, after) ∈ support ((simulateQ
      (PqxdhLaterChallengeCutChronology.postImpl mark sender route decode impl)
      (PqxdhRecordConfidentialityChallenge.send owner plaintext)).run before)) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1.1.roles.1 = some kernel ∧
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain ∈ after.2.1.1.2 := by
  cases owner with
  | server index peer =>
      simp only [PqxdhRecordConfidentialityChallenge.send, PqxdhRecordConfidentialityChallenge.sendRequest,
        simulateQ_spec_query] at supported
      simp only [PqxdhLaterChallengeCutChronology.postImpl, StateT.run, support_map] at supported
      obtain ⟨⟨⟨reply, front⟩, backend⟩, reached, same⟩ := supported
      rcases Prod.mk.inj same with ⟨rfl, rfl⟩
      exact origin_input source writer stage pre application initial selector aux mark sender route decode
        (.inl (.inl ⟨index, .inl (plaintext, peer)⟩)) before.1 before.2 _ reached
        (.server index peer) record.sequence (by simp only [RawCtxPublishedRecords.record, List.mem_singleton])
  | beacon index =>
      simp only [PqxdhRecordConfidentialityChallenge.send, PqxdhRecordConfidentialityChallenge.sendRequest,
        simulateQ_spec_query] at supported
      simp only [PqxdhLaterChallengeCutChronology.postImpl, StateT.run, support_map] at supported
      obtain ⟨⟨⟨reply, front⟩, backend⟩, reached, same⟩ := supported
      rcases Prod.mk.inj same with ⟨rfl, rfl⟩
      exact origin_input source writer stage pre application initial selector aux mark sender route decode
        (.inl (.inr (.inl ⟨index, .inl plaintext⟩))) before.1 before.2 _ reached
        (.beacon index) record.sequence (by simp only [RawCtxPublishedRecords.record, List.mem_singleton])

end BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.owner_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.owner_input
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.server_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.server_input
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.beacon_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.beacon_input
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.live_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.live_input
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.pending_live_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.pending_live_input
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.origin_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.origin_input
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.challenge_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog.challenge_input
