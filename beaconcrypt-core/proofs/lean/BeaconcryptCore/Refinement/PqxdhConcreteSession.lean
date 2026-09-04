import BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity
import BeaconcryptCore.Refinement.RatchetInterpreter

/-! Concrete role initialization and session provenance for fixed pure KDF interpreters. The existing PQXDH and ratchet models are unchanged; this module connects their refinement relations to complete executions of the extracted initialization phases. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.PqxdhConcreteSession

abbrev InitialKdfInterpreter := ratchet.SymmetricRatchetKdfRequest → pqxdh.concrete.InitialRatchetKdfResponse

/-- Execute the extracted beacon initialization phases with a fixed pure response interpreter. -/
def initializeBeacon (root : Std.Array Std.U8 32#usize) (execute : InitialKdfInterpreter) :
    RustM ratchet.concrete.ConcreteRatchetKernel := do
  let pending ← pqxdh.concrete.start_beacon_ratchet_kdf root
  pqxdh.concrete.resume_initial_ratchet_kdf pending (execute pending.request)

/-- Execute the extracted server initialization phases with the same request interpretation. -/
def initializeServer (root : Std.Array Std.U8 32#usize) (execute : InitialKdfInterpreter) :
    RustM ratchet.concrete.ConcreteRatchetKernel := do
  let pending ← pqxdh.concrete.start_server_ratchet_kdf root
  pqxdh.concrete.resume_initial_ratchet_kdf pending (execute pending.request)

theorem initializeBeacon_eq (root : Std.Array Std.U8 32#usize) (execute : InitialKdfInterpreter) :
    initializeBeacon root execute = pqxdh.concrete.resume_initial_ratchet_kdf (beaconPending root)
      (execute { input := root, info := ratchet.SYM_RATCHET_INFO }) := by
  simp [initializeBeacon, pqxdh.concrete.start_beacon_ratchet_kdf_exact, beaconPending]

theorem initializeServer_eq (root : Std.Array Std.U8 32#usize) (execute : InitialKdfInterpreter) :
    initializeServer root execute = pqxdh.concrete.resume_initial_ratchet_kdf (serverPending root)
      (execute { input := root, info := ratchet.SYM_RATCHET_INFO }) := by
  simp [initializeServer, pqxdh.concrete.start_server_ratchet_kdf_exact, serverPending]

/-- Both roles have reachable ideal receive states, exact live material correspondence, and sending chains derived from their fixed opposite origins. -/
def ConcreteSession {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (beaconOrigin serverOrigin : ratchet.RatchetChain)
    (beacon server : ratchet.concrete.ConcreteRatchetKernel) : Prop :=
  ∃ beaconSend beaconReceive serverSend serverReceive,
    ratchet.concrete.KernelRefines cr serverOrigin beaconSend beaconReceive beacon ∧
    ratchet.concrete.KernelRefines cr beaconOrigin serverSend serverReceive server ∧
    beaconSend.ck = Ratchet.chainAt cr beaconOrigin beaconSend.n ∧
    serverSend.ck = Ratchet.chainAt cr serverOrigin serverSend.n

/-- One fixed initial interpreter gives complementary exact byte origins and zero-state kernel refinements for both extracted roles. -/
theorem initial_kernels_refine {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (root : Std.Array Std.U8 32#usize) (execute : InitialKdfInterpreter) :
    ∃ beaconOrigin serverOrigin beacon server,
      initializeBeacon root execute = ok beacon ∧ initializeServer root execute = ok server ∧
      ChainBytesRefines beaconOrigin (secondHalf (execute { input := root, info := ratchet.SYM_RATCHET_INFO }).bytes) ∧
      ChainBytesRefines serverOrigin (firstHalf (execute { input := root, info := ratchet.SYM_RATCHET_INFO }).bytes) ∧
      ratchet.concrete.KernelRefines cr serverOrigin ⟨beaconOrigin, 0⟩ ⟨serverOrigin, 0, []⟩ beacon ∧
      ratchet.concrete.KernelRefines cr beaconOrigin ⟨serverOrigin, 0⟩ ⟨beaconOrigin, 0, []⟩ server := by
  obtain ⟨left, right, hleft, hright, hleftBytes, hrightBytes⟩ :=
    initialHalves_exact (execute { input := root, info := ratchet.SYM_RATCHET_INFO }).bytes
  obtain ⟨beacon, hbeacon, hbeaconRefines⟩ := concreteKernelNew_refines_initial cr ⟨right⟩ ⟨left⟩
  obtain ⟨server, hserver, hserverRefines⟩ := concreteKernelNew_refines_initial cr ⟨left⟩ ⟨right⟩
  refine ⟨⟨right⟩, ⟨left⟩, beacon, server, ?_, ?_, hrightBytes, hleftBytes, hbeaconRefines, hserverRefines⟩
  · simp [initializeBeacon_eq, pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition,
      beaconPending, pqxdh.split_initial_ratchet_kdf_output, hleft, hright,
      ratchet.RatchetChain.from_bytes, hbeacon]
  · simp [initializeServer_eq, pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition,
      serverPending, pqxdh.split_initial_ratchet_kdf_output, hleft, hright,
      ratchet.RatchetChain.from_bytes, hserver]

/-- Initial role kernels form one concrete session, and opposing material streams agree at every logical position. -/
theorem initialize_establishes_concrete_session {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (root : Std.Array Std.U8 32#usize) (execute : InitialKdfInterpreter) :
    ∃ beaconOrigin serverOrigin beacon server,
      initializeBeacon root execute = ok beacon ∧ initializeServer root execute = ok server ∧
      ConcreteSession cr beaconOrigin serverOrigin beacon server ∧
      beacon.refined.send_chain = server.refined.receive_chain ∧
      beacon.refined.receive_chain = server.refined.send_chain ∧
      ∀ n, Ratchet.msgKeyAt cr beacon.refined.send_chain n = Ratchet.msgKeyAt cr server.refined.receive_chain n ∧
        Ratchet.msgKeyAt cr server.refined.send_chain n = Ratchet.msgKeyAt cr beacon.refined.receive_chain n := by
  obtain ⟨beaconOrigin, serverOrigin, beacon, server, hbeacon, hserver, _, _, hb, hs⟩ :=
    initial_kernels_refine cr root execute
  refine ⟨beaconOrigin, serverOrigin, beacon, server, hbeacon, hserver,
    ⟨⟨beaconOrigin, 0⟩, ⟨serverOrigin, 0, []⟩, ⟨serverOrigin, 0⟩, ⟨beaconOrigin, 0, []⟩,
      hb, hs, rfl, rfl⟩,
    hb.sendChain.trans hs.receiveChain.symm, hb.receiveChain.trans hs.sendChain.symm, ?_⟩
  simp only [hb.sendChain, hb.receiveChain, hs.sendChain, hs.receiveChain, and_self, implies_true]

/-- Candidate-bound beacon initialization executes the same production role phases. -/
def initializeBeaconCandidate (candidate : pqxdh.BeaconRegistrationCandidate)
    (root : Std.Array Std.U8 32#usize) (execute : InitialKdfInterpreter) :
    RustM ratchet.concrete.ConcreteRatchetKernel := do
  let pending ← pqxdh.concrete.start_beacon_candidate_ratchet_kdf candidate root
  pqxdh.concrete.resume_initial_ratchet_kdf pending (execute pending.request)

theorem initializeBeaconCandidate_eq (candidate : pqxdh.BeaconRegistrationCandidate)
    (root : Std.Array Std.U8 32#usize) (execute : InitialKdfInterpreter) :
    initializeBeaconCandidate candidate root execute = initializeBeacon root execute := rfl

/-- Authenticated root-input agreement remains agreement under every fixed pure root derivation. -/
theorem authenticated_roots_agree (authenticated : pqxdh.AuthenticatedBeaconRegistration)
    (pending : pqxdh.PendingServerRegistration)
    (deriveRoot : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize)
    (hroot : authenticated.candidate.root_key_input = pending.root_key_input) :
    deriveRoot authenticated.candidate.root_key_input = deriveRoot pending.root_key_input :=
  congrArg deriveRoot hroot

/-- Authentication-linked agreement establishes a concrete paired session under fixed pure initial and step interpreters. -/
theorem authenticated_registrations_establish_concrete_session {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (authenticated : pqxdh.AuthenticatedBeaconRegistration) (pending : pqxdh.PendingServerRegistration)
    (deriveRoot : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize)
    (initialExecute : InitialKdfInterpreter) (stepExecute : ratchet.concrete.KdfInterpreter)
    (hroot : authenticated.candidate.root_key_input = pending.root_key_input) :
    ∃ beaconOrigin serverOrigin beacon server,
      initializeBeaconCandidate authenticated.candidate (deriveRoot authenticated.candidate.root_key_input)
        initialExecute = ok beacon ∧
      initializeServer (deriveRoot pending.root_key_input) initialExecute = ok server ∧
      ConcreteSession (ratchet.concrete.withInterpreter cr stepExecute) beaconOrigin serverOrigin beacon server ∧
      ∀ n,
        Ratchet.msgKeyAt (ratchet.concrete.withInterpreter cr stepExecute) beacon.refined.send_chain n =
          Ratchet.msgKeyAt (ratchet.concrete.withInterpreter cr stepExecute) server.refined.receive_chain n ∧
        Ratchet.msgKeyAt (ratchet.concrete.withInterpreter cr stepExecute) server.refined.send_chain n =
          Ratchet.msgKeyAt (ratchet.concrete.withInterpreter cr stepExecute) beacon.refined.receive_chain n := by
  obtain ⟨beaconOrigin, serverOrigin, beacon, server, hb, hs, hsession, _, _, hmaterials⟩ :=
    initialize_establishes_concrete_session (ratchet.concrete.withInterpreter cr stepExecute)
      (deriveRoot authenticated.candidate.root_key_input) initialExecute
  exact ⟨beaconOrigin, serverOrigin, beacon, server, hb, by simpa only [hroot] using hs,
    hsession, hmaterials⟩

end BeaconcryptCore.Refinement.PqxdhConcreteSession
