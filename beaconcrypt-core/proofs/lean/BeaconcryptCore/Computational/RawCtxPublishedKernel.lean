import BeaconcryptCore.Computational.RawCtxPublishedRecords
import BeaconcryptCore.Computational.RawCtxGenericFamilyLive

/-!
A successful original send reply identifies the installed kernel at that exact source step and its returned sequence. The operational callback property is propagated through actual empty-input rejection, Server peer selection, Beacon phase admission and the complete LIVE frontend. This module does not infer publication from an internal derivation or from a counter alone. The concrete selective-table callback discharges the sole send-reply property in the source consumer.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPublishedKernel
open RawCtxGenericRoleStorage RawCtxProtocolReveals
variable {Kernel State M P I D K : Type} {S B : Nat}

def SendSequence (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (sequence : Kernel → Std.U64) : Prop :=
  ∀ entry context state result, result ∈ support ((calls.send entry context).run state) →
    ∀ sent, result.1.2 = some sent → sent.sequence = sequence result.1.1

/-- A successful owner send exposes the exact sequence of its actual returned kernel. -/
theorem owner (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (sequence : Kernel → Std.U64) (law : SendSequence calls sequence)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (entry : RawCtxChainOwner.State Kernel M)
    (state : State) (result : (Option RawCtxSourceSend.Encrypted × RawCtxChainOwner.State Kernel M) × State)
    (supported : result ∈ support (((RawCtxChainOwner.sendOwner calls sender plaintext).run entry).run state))
    (sent : RawCtxSourceSend.Encrypted) (published : result.1.1 = some sent) :
    sent.sequence = sequence result.1.2.kernel := by
  unfold RawCtxChainOwner.sendOwner at supported
  by_cases empty : plaintext.isEmpty = true
  · simp only [empty, if_true] at supported
    subst result
    cases published
  · simp only [empty, Bool.false_eq_true, if_false, bind_pure_comp] at supported
    change result ∈ support (((fun reply => (reply.2, {entry with kernel := reply.1})) <$>
      calls.send entry.kernel ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩).run state) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact law _ _ _ reply reached sent published

/-- The original Server publishes the advanced kernel at exactly the peer named by its successful send reply. -/
theorem server (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (sequence : Kernel → Std.U64) (law : SendSequence calls sequence)
    (sender : M → Std.U64) (plaintext : Pqxdh.Bytes) (peer : Std.U64)
    (entry : ServerState Kernel M P) (state : State)
    (result : (Option RawCtxSourceSend.Encrypted × ServerState Kernel M P) × State)
    (supported : result ∈ support ((RawCtxGenericServer.sendServer calls sender plaintext peer entry).run state))
    (sent : RawCtxSourceSend.Encrypted) (published : result.1.1 = some sent) :
    ∃ kernel, (result.1.2.server.peers peer).map Peer.kernel = some kernel ∧ sent.sequence = sequence kernel := by
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
          exact ⟨reply.1.2.kernel, by simp only [RawCtxGenericServer.putPeer, Function.update_self, Option.map_some],
            owner calls sequence law _ _ _ _ _ reached sent published⟩

/-- An original Beacon send can publish only in its established phase, retaining the same installed advanced kernel. -/
theorem beacon (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (sequence : Kernel → Std.U64) (law : SendSequence calls sequence)
    (decode : RawCtxReceive.FrameDecoder) (plaintext : Pqxdh.Bytes)
    (entry : BeaconState Kernel I D K) (state : State)
    (result : (Option RawCtxSourceSend.Encrypted × BeaconState Kernel I D K) × State)
    (supported : result ∈ support (((RawCtxGenericBeacon.impl calls decode (.inl plaintext)).run entry).run state))
    (sent : RawCtxSourceSend.Encrypted) (published : result.1.1 = some sent) :
    ∃ control ad kernel, result.1.2.beacon.phase = .established control ad kernel ∧ sent.sequence = sequence kernel := by
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
    exact ⟨control, ad, reply.1.2.kernel, rfl, owner calls sequence law _ _ _ _ _ reached sent published⟩
  all_goals
    simp only [RawCtxGenericBeacon.impl, StateT.run, phase, RawCtxGenericBeacon.rejected] at supported
    subst result
    cases published

/-- Every recorded original LIVE publication selects the actual post-step installed kernel and its returned sequence. -/
theorem live (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (sequence : Kernel → Std.U64) (law : SendSequence calls sequence)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT State ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec S B).Domain) (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B)
    (state : State) (result : ((SourceSpec S B).Range query × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × State)
    (supported : result ∈ support (((RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode query).run entry).run state))
    (selected : Owner S B) (number : Std.U64)
    (recorded : (selected, number) ∈ RawCtxPublishedRecords.record query result.1.1) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel selected result.1.2.1 = some kernel ∧ number = sequence kernel := by
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
        exact ⟨kernel, by simpa only [RawCtxGenericRoleFamily.selectedKernel, Function.update_self] using present, numberEq⟩
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
        exact ⟨kernel, by simp only [RawCtxGenericRoleFamily.selectedKernel, Function.update_self, phase], numberEq⟩
    | inr raw => simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded
  case inl.inr.inr => simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded
  case inr => simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded

end BeaconcryptCore.Computational.RawCtxPublishedKernel

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedKernel.owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedKernel.owner


/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedKernel.server' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedKernel.server


/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedKernel.beacon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedKernel.beacon


/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedKernel.live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedKernel.live
