-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentNative
import BeaconcryptCore.Computational.RawCtxReceiveConsumption

/-! Per-peer AD routing exposes the same selected-owner source send and receive programs while retaining complete peer metadata. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.MldsaServerRoutingCases
open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Metadata PeerMetadata : Type}

theorem send_cases (adOf : PeerMetadata → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (sender : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (view : RawCtxServerRouting.State Metadata PeerMetadata)
    (primitive : RawCtxSharedPrimitive.SharedState Unit)
    (reached : (Option RawCtxSourceSend.Encrypted × RawCtxServerRouting.State Metadata PeerMetadata) ×
      RawCtxSharedPrimitive.SharedState Unit)
    (member : reached ∈ support ((simulateQ (PqxdhDeploymentNative.primitives setup codec)
      (MldsaServerRouting.send adOf sender plaintext kid view)).run primitive)) :
    reached.1.2.server = view.server ∨
      ∃ peer step, view.server.peers kid = some peer ∧
        step ∈ support (RawCtxSourceSend.sendGame (RawCtxReceiveConsumption.sendNative setup.source codec.frameWrite)
          (sender view.server.metadata) plaintext
          ⟨MldsaServerRouting.selected adOf kid peer, view.rawAttempts⟩ primitive) ∧
        reached.1.1 = step.1.1 ∧
        reached.1.2.server = RawCtxServerRouting.putPeer view.server kid peer step.1.2.owner.kernel := by
  cases found : view.server.peers kid with
  | none =>
      simp only [MldsaServerRouting.send, found, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at member
      subst member
      exact Or.inl rfl
  | some peer =>
      simp only [MldsaServerRouting.send, found, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, member⟩ := member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      refine Or.inr ⟨peer, step, rfl, ?_, rfl, rfl⟩
      simpa only [RawCtxMixedOwner.ownerImpl, RawCtxSourceSend.sendGame,
        RawCtxReceiveConsumption.sendNative, PqxdhDeploymentNative.primitives,
        QueryImpl.simulateQ_compose] using stepMember

theorem receive_cases (adOf : PeerMetadata → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (raw : Pqxdh.Bytes)
    (view : RawCtxServerRouting.State Metadata PeerMetadata) (primitive : RawCtxSharedPrimitive.SharedState Unit)
    (reached : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxServerRouting.State Metadata PeerMetadata) ×
      RawCtxSharedPrimitive.SharedState Unit)
    (member : reached ∈ support ((simulateQ (PqxdhDeploymentNative.primitives setup codec)
      (MldsaServerRouting.receive adOf route codec.frameRead raw view)).run primitive)) :
    (reached.1.1 = .None ∧ reached.1.2.server = view.server) ∨
      ∃ kid peer step, route raw = some kid ∧ view.server.peers kid = some peer ∧
        step ∈ support (RawCtxWholeOwner.rawGame (RawCtxReceiveConsumption.receiveNative setup.source)
          codec.frameRead raw ⟨MldsaServerRouting.selected adOf kid peer, view.rawAttempts⟩ primitive) ∧
        reached.1.1 = step.1.1 ∧
        reached.1.2.server = RawCtxServerRouting.putPeer view.server kid peer step.1.2.owner.kernel := by
  cases routed : route raw with
  | none =>
      simp only [MldsaServerRouting.receive, routed, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at member
      subst member
      exact Or.inl ⟨rfl, rfl⟩
  | some kid =>
      cases found : view.server.peers kid with
      | none =>
          simp only [MldsaServerRouting.receive, routed, found, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at member
          subst member
          exact Or.inl ⟨rfl, rfl⟩
      | some peer =>
          simp only [MldsaServerRouting.receive, routed, found, simulateQ_bind, StateT.run_bind,
            mem_support_bind_iff] at member
          obtain ⟨step, stepMember, member⟩ := member
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
          subst member
          refine Or.inr ⟨kid, peer, step, rfl, found, ?_, rfl, rfl⟩
          unfold RawCtxWholeOwner.rawGame
          rw [← RawCtxReceiveConsumption.shared_receiveNative setup.source codec.frameWrite,
            QueryImpl.simulateQ_compose]
          exact stepMember

end BeaconcryptCore.Computational.MldsaServerRoutingCases

/-- info: 'BeaconcryptCore.Computational.MldsaServerRoutingCases.send_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaServerRoutingCases.send_cases

/-- info: 'BeaconcryptCore.Computational.MldsaServerRoutingCases.receive_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaServerRoutingCases.receive_cases
