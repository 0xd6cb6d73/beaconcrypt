import BeaconcryptCore.Computational.PqxdhInitialReplyErasure
import BeaconcryptCore.Computational.RawCtxPositionedOwner

/-!
An arbitrary supplied typed64-byte response establishes the exact initialized kernels, opposite directional origins and zero-state positional relations used by the source live-history theorems. This is an operational statement for either actual response or a comparison response. It supplies no entropy, distinctness or source-distribution assumption.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open BeaconcryptCore.Refinement.RepresentationBridge
open BeaconcryptCore.Refinement.PqxdhConcreteSession
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions
open PqxdhInitialRatchetComplementarity PqxdhInitialReplyErasure

/-- One supplied response gives both actual role kernels, exact opposite byte halves and complete zero-state refinements, before either role performs a send or receive. -/
theorem pair_refines (c : Pqxdh.Crypto) (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ beaconOrigin serverOrigin beacon server,
      kernelOf true response = ok beacon ∧ kernelOf false response = ok server ∧
      ChainBytesRefines beaconOrigin (secondHalf response.bytes) ∧
      ChainBytesRefines serverOrigin (firstHalf response.bytes) ∧
      KernelRefines (RawCtxPositionedOwner.crypto c) serverOrigin
        ⟨beaconOrigin, 0⟩ ⟨serverOrigin, 0, []⟩ beacon ∧
      KernelRefines (RawCtxPositionedOwner.crypto c) beaconOrigin
        ⟨serverOrigin, 0⟩ ⟨beaconOrigin, 0, []⟩ server := by
  obtain ⟨bo, so, beacon, server, hb, hs, hbo, hso, br, sr⟩ :=
    initial_kernels_refine (RawCtxPositionedOwner.crypto c)
      (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)) (fun _ => response)
  refine ⟨bo, so, beacon, server, ?_, ?_, hbo, hso, br, sr⟩
  · simpa [initializeBeacon_eq, kernelOf, PqxdhInitialResponseService.pending] using hb
  · simpa [initializeServer_eq, kernelOf, PqxdhInitialResponseService.pending] using hs

/-- The same supplied response establishes the exact initial positional invariant for both roles and complementary chain origins, with no assumption that the response is real or uniform. -/
theorem pair_positioned (c : Pqxdh.Crypto) (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ beacon server,
      kernelOf true response = ok beacon ∧ kernelOf false response = ok server ∧
      RawCtxPositionedOwner.Positioned c beacon.refined.send_chain beacon.refined.receive_chain beacon ∧
      RawCtxPositionedOwner.Positioned c server.refined.send_chain server.refined.receive_chain server ∧
      beacon.refined.send_chain = server.refined.receive_chain ∧
      beacon.refined.receive_chain = server.refined.send_chain := by
  obtain ⟨bo, so, beacon, server, hb, hs, _, _, br, sr⟩ := pair_refines c response
  refine ⟨beacon, server, hb, hs, ?_, ?_, br.sendChain.trans sr.receiveChain.symm,
    br.receiveChain.trans sr.sendChain.symm⟩
  · rw [br.sendChain, br.receiveChain]
    exact ⟨⟨bo, 0⟩, ⟨so, 0, []⟩, br, rfl⟩
  · rw [sr.sendChain, sr.receiveChain]
    exact ⟨⟨so, 0⟩, ⟨bo, 0, []⟩, sr, rfl⟩

/-- Every kernel returned by the supplied Server initializer satisfies the source positional invariant at its own two initial origins. -/
theorem server_positioned (c : Pqxdh.Crypto) (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (kernel : ConcreteRatchetKernel) (initialized : kernelOf false response = ok kernel) :
    RawCtxPositionedOwner.Positioned c kernel.refined.send_chain kernel.refined.receive_chain kernel := by
  obtain ⟨_, server, _, hs, _, positioned, _, _⟩ := pair_positioned c response
  have same : server = kernel := RustM.ok.inj (hs.symm.trans initialized)
  simpa only [same] using positioned

/-- Every normalized supplied Beacon initializer satisfies the source positional invariant before the original registration receive begins. -/
theorem beacon_positioned (c : Pqxdh.Crypto) (root : Std.Array Std.U8 32#usize)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    let kernel := PqxdhBeaconPhase2Publication.normalInitial (beaconPending root) response
    RawCtxPositionedOwner.Positioned c kernel.refined.send_chain kernel.refined.receive_chain kernel := by
  obtain ⟨beacon, _, hb, _, positioned, _, _, _⟩ := pair_positioned c response
  have same : beacon = PqxdhBeaconPhase2Publication.normalInitial (beaconPending root) response := by
    apply RustM.ok.inj
    rw [← hb]
    change pqxdh.concrete.resume_initial_ratchet_kdf
      (beaconPending (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0))) response = _
    rw [PqxdhBeaconPhase2Publication.normalInitial_exact, beacon_kernel_root_unused _ root]
  simpa only [same] using positioned

end BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions.pair_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions.pair_refines

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions.pair_positioned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions.pair_positioned

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions.server_positioned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions.server_positioned

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions.beacon_positioned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions.beacon_positioned
