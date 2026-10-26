import BeaconcryptCore.Computational.RawCtxGenericNativeCalls
import BeaconcryptCore.Computational.RawCtxPublishedKernel

/-! Exact successful send sequence from the actual native adapter. All primitive replies and full state are retained; success is used only to exclude the source exhaustion branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxNativeSendSequence
variable {State : Type}
open RawCtxSourceSend

/-- The original adapter constructs the returned sequence from the successful source step, so both returned record and advanced kernel use exactly the old counter plus one. -/
theorem primitive (impl : QueryImpl PrimitiveSpec (StateT State ProbComp))
    (entry : ConcreteRatchetKernel) (context : SealContext) (before : State)
    (result : (ConcreteRatchetKernel × Option Encrypted) × State)
    (supported : result ∈ support ((simulateQ (impl ∘ₛ adapter) (send entry context)).run before))
    (record : Encrypted) (returned : result.1.2 = some record) :
    record.sequence.val = entry.refined.control.send_sequence.val + 1 ∧
      result.1.1.refined.control.send_sequence.val = entry.refined.control.send_sequence.val + 1 := by
  by_cases exhausted : entry.refined.control.send_sequence = core.num.U64.MAX
  · rw [send_exhausted entry context exhausted] at supported
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    cases returned
  · obtain ⟨pending, started, original, _, _, _, sequence, next, _, _⟩ := beginSend_fields entry context exhausted
    rw [send, started] at supported
    obtain ⟨response, afterKdf, reply, afterSeal, _, sealed, rfl⟩ :=
      requested_support (impl ∘ₛ adapter) pending before result supported
    simp only [QueryImpl.compose, adapter, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map] at sealed
    obtain ⟨⟨ciphertext, after⟩, _, same⟩ := sealed
    have recordFields : Option.map (encrypted (arguments (resumeSend pending response))) ciphertext = some record := by
      exact (congrArg Prod.fst same).trans returned
    obtain ⟨bytes, _, recordEq⟩ := Option.map_eq_some_iff.mp recordFields
    obtain ⟨stepped, _, ready⟩ := resumeSend_fields pending response
    simpa only [← recordEq, ready, encrypted, arguments, ← sequence, next] using And.intro next next

/-- Every actual native send reply carries the incremented counter; arbitrary KDF, AEAD, hash and writer outcomes remain inside the same full interpreter. -/
theorem native (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT State ProbComp))
    (entry : RawCtxPendingOwnerQueries.Kernel RatchetChain) (context : SealContext) (before : State)
    (result : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option Encrypted) × State)
    (supported : result ∈ support (((RawCtxGenericNativeCalls.calls impl).send entry context).run before))
    (record : Encrypted) (returned : result.1.2 = some record) :
    record.sequence.val = entry.control.send_sequence.val + 1 ∧
      result.1.1.control.send_sequence.val = entry.control.send_sequence.val + 1 := by
  apply primitive (impl ∘ₛ RawCtxMixedOwner.sendAdapter) ⟨entry⟩ context before
    ((⟨result.1.1⟩, result.1.2), result.2) _ record returned
  rw [RawCtxGenericNativeCalls.send_realized, StateT.run_map, support_map]
  exact ⟨result, supported, rfl⟩

section Frontend
variable {Kernel M P I D K : Type} {S B : Nat}
open RawCtxGenericRoleStorage RawCtxProtocolReveals

def SendNext (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp)) (sequence : Kernel → Nat) : Prop :=
  ∀ entry context state result, result ∈ support ((calls.send entry context).run state) →
    ∀ sent, result.1.2 = some sent → sent.sequence.val = sequence entry + 1

/-- Successful owner admission retains the original kernel's counter, including all primitive and optional writer outcomes. -/
theorem owner (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (sequence : Kernel → Nat) (law : SendNext calls sequence)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (entry : RawCtxChainOwner.State Kernel M)
    (state : State) (result : (Option RawCtxSourceSend.Encrypted × RawCtxChainOwner.State Kernel M) × State)
    (supported : result ∈ support (((RawCtxChainOwner.sendOwner calls sender plaintext).run entry).run state))
    (sent : RawCtxSourceSend.Encrypted) (published : result.1.1 = some sent) :
    sent.sequence.val = sequence entry.kernel + 1 := by
  unfold RawCtxChainOwner.sendOwner at supported
  by_cases empty : plaintext.isEmpty = true
  case neg =>
    simp only [empty, Bool.false_eq_true, ite_false, bind_pure_comp] at supported
    change result ∈ support (((fun reply => (reply.2, {entry with kernel := reply.1})) <$>
      calls.send entry.kernel ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩).run state) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact law _ _ _ reply reached sent published
  case pos =>
    simp only [empty, ite_true] at supported
    subst result
    cases published

/-- Successful Server admission exposes the kernel selected before the send, at the actual requested peer. -/
theorem server (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (sequence : Kernel → Nat) (law : SendNext calls sequence)
    (sender : M → Std.U64) (plaintext : Pqxdh.Bytes) (peer : Std.U64)
    (entry : ServerState Kernel M P) (state : State)
    (result : (Option RawCtxSourceSend.Encrypted × ServerState Kernel M P) × State)
    (supported : result ∈ support ((RawCtxGenericServer.sendServer calls sender plaintext peer entry).run state))
    (sent : RawCtxSourceSend.Encrypted) (published : result.1.1 = some sent) :
    ∃ kernel, (entry.server.peers peer).map Peer.kernel = some kernel ∧ sent.sequence.val = sequence kernel + 1 := by
  unfold RawCtxGenericServer.sendServer at supported
  cases adFound : RawCtxGenericServer.peerAssociatedData entry.server peer with
  | none =>
      simp only [adFound, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      cases published
  | some ad =>
      simp only [adFound] at supported
      cases peerFound : entry.server.peers peer with
      | none =>
          simp only [peerFound, StateT.run_pure, mem_support_pure_iff] at supported
          subst result
          cases published
      | some before =>
          simp only [peerFound, bind_pure_comp] at supported
          change result ∈ support (((fun reply =>
            (reply.1, ⟨RawCtxGenericServer.putPeer entry.server peer before reply.2.kernel,
              reply.2.rawAttempts⟩)) <$>
              (RawCtxChainOwner.sendOwner calls (sender entry.server.metadata) plaintext).run
                (RawCtxGenericServer.selectedOwner peer ad before entry.rawAttempts)).run state) at supported
          rw [StateT.run_map, support_map] at supported
          obtain ⟨reply, reached, rfl⟩ := supported
          exact ⟨before.kernel, rfl, owner calls sequence law _ _ _ _ _ reached sent published⟩

/-- Successful Beacon admission identifies the established kernel before any send effects. -/
theorem beacon (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (sequence : Kernel → Nat) (law : SendNext calls sequence)
    (decode : RawCtxReceive.FrameDecoder) (plaintext : Pqxdh.Bytes)
    (entry : BeaconState Kernel I D K) (state : State)
    (result : (Option RawCtxSourceSend.Encrypted × BeaconState Kernel I D K) × State)
    (supported : result ∈ support (((RawCtxGenericBeacon.impl calls decode (.inl plaintext)).run entry).run state))
    (sent : RawCtxSourceSend.Encrypted) (published : result.1.1 = some sent) :
    ∃ control ad kernel, entry.beacon.phase = .established control ad kernel ∧ sent.sequence.val = sequence kernel + 1 := by
  cases phase : entry.beacon.phase
  case established control ad kernel =>
    rw [RawCtxGenericBeacon.established calls decode (.inl plaintext) entry control ad kernel phase] at supported
    simp only [RawCtxChainOwner.ownerImpl, bind_pure_comp] at supported
    change result ∈ support (((fun reply =>
      (reply.1, RawCtxGenericBeacon.reinstall entry control ad reply.2)) <$>
        (RawCtxChainOwner.sendOwner calls entry.beacon.identityKeyId plaintext).run
          (RawCtxGenericBeacon.selected entry control ad kernel)).run state) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact ⟨control, ad, kernel, rfl, owner calls sequence law _ _ _ _ _ reached sent published⟩
  all_goals
    simp only [RawCtxGenericBeacon.impl, StateT.run, phase, RawCtxGenericBeacon.rejected] at supported
    subst result
    cases published

/-- A successful complete LIVE send identifies the selected pre-step kernel and its exact counter, for either role. -/
theorem live (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (sequence : Kernel → Nat) (law : SendNext calls sequence)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT State ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec S B).Domain) (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B)
    (state : State) (result : ((SourceSpec S B).Range query × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × State)
    (supported : result ∈ support (((RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode query).run entry).run state))
    (selected : Owner S B) (number : Std.U64)
    (recorded : (selected, number) ∈ RawCtxPublishedRecords.record query result.1.1) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel selected entry.1 = some kernel ∧ number.val = sequence kernel + 1 := by
  rcases query with (⟨index, request⟩ | (⟨index, request⟩ | publicQuery)) | readQuery
  case inl.inl =>
    cases request with
    | inl request =>
      rcases request with ⟨plaintext, peer⟩
      simp only [RawCtxGenericFamilyLive.impl, RawCtxGenericFamilyFrontend.impl, RawCtxGenericServer.serverImpl,
        StateT.run, bind_pure_comp, Functor.map_map] at supported
      change result ∈ support (((fun reply =>
        (reply.1, ((Function.update entry.1.1 index reply.2, entry.1.2), tick entry.2))) <$>
          RawCtxGenericServer.sendServer calls sender plaintext peer (entry.1.1 index)).run state) at supported
      rw [StateT.run_map, support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      cases published : reply.1.1 with
      | none => simp only [RawCtxPublishedRecords.record, published, List.not_mem_nil] at recorded
      | some sent =>
        simp only [RawCtxPublishedRecords.record, published, List.mem_singleton, Prod.mk.injEq] at recorded
        rcases recorded with ⟨rfl, rfl⟩
        obtain ⟨kernel, present, numberEq⟩ := server calls sequence law sender plaintext peer _ state reply reached sent published
        exact ⟨kernel, present, numberEq⟩
    | inr raw => simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded
  case inl.inr.inl =>
    cases request with
    | inl plaintext =>
      simp only [RawCtxGenericFamilyLive.impl, RawCtxGenericFamilyFrontend.impl,
        StateT.run, bind_pure_comp, Functor.map_map] at supported
      change result ∈ support (((fun reply =>
        (reply.1, ((entry.1.1, Function.update entry.1.2 index reply.2), tick entry.2))) <$>
          (RawCtxGenericBeacon.impl calls decode (.inl plaintext)).run (entry.1.2 index)).run state) at supported
      rw [StateT.run_map, support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      cases published : reply.1.1 with
      | none => simp only [RawCtxPublishedRecords.record, published, List.not_mem_nil] at recorded
      | some sent =>
        simp only [RawCtxPublishedRecords.record, published, List.mem_singleton, Prod.mk.injEq] at recorded
        rcases recorded with ⟨rfl, rfl⟩
        obtain ⟨control, ad, kernel, phase, numberEq⟩ := beacon calls sequence law decode plaintext _ state reply reached sent published
        exact ⟨kernel, by simp only [RawCtxGenericRoleFamily.selectedKernel, phase], numberEq⟩
    | inr raw => simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded
  case inl.inr.inr => simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded
  case inr => simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded

end Frontend

end BeaconcryptCore.Computational.RawCtxNativeSendSequence

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeSendSequence.primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSendSequence.primitive
/-- info: 'BeaconcryptCore.Computational.RawCtxNativeSendSequence.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSendSequence.native
/-- info: 'BeaconcryptCore.Computational.RawCtxNativeSendSequence.owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSendSequence.owner
/-- info: 'BeaconcryptCore.Computational.RawCtxNativeSendSequence.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSendSequence.server
/-- info: 'BeaconcryptCore.Computational.RawCtxNativeSendSequence.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSendSequence.beacon
/-- info: 'BeaconcryptCore.Computational.RawCtxNativeSendSequence.live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSendSequence.live
