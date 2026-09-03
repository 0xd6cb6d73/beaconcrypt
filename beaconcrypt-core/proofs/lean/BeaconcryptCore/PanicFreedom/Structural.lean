import BeaconcryptCore.PanicFreedom.Static

/-!
# Totality of structural constructors and wrappers

These operations compose normal-return constructors, accessors, and role descriptors. Their safety is independent of logical invariants and cryptographic correctness.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

namespace BeaconcryptCore.PanicFreedom.Structural

theorem ratchet_refined_empty_material_slots_total
  (Material : Type) :
    ∃ result, ratchet.refined.empty_material_slots Material = ok result := ⟨_, rfl⟩

theorem ratchet_refined_RefinedRatchet_from_counters_total
  {SendChain : Type} {ReceiveChain : Type} (Material : Type)
  (send_sequence : Std.U64) (receive_sequence : Std.U64)
  (send_chain : SendChain) (receive_chain : ReceiveChain) :
    ∃ result, ratchet.refined.RefinedRatchet.from_counters
      Material send_sequence receive_sequence send_chain receive_chain = ok result :=
  ⟨_, rfl⟩

theorem ratchet_refined_RefinedRatchet_new_total
  {SendChain : Type} {ReceiveChain : Type} (Material : Type)
  (send_chain : SendChain) (receive_chain : ReceiveChain) :
    ∃ result, ratchet.refined.RefinedRatchet.new Material send_chain receive_chain = ok result :=
  ⟨_, rfl⟩

theorem ratchet_concrete_ConcreteRatchetKernel_from_counters_total
  (send_sequence : Std.U64) (receive_sequence : Std.U64)
  (send_chain : ratchet.RatchetChain) (receive_chain : ratchet.RatchetChain) :
    ∃ result, ratchet.concrete.ConcreteRatchetKernel.from_counters
      send_sequence receive_sequence send_chain receive_chain = ok result :=
  ⟨_, rfl⟩

theorem ratchet_concrete_ConcreteRatchetKernel_new_total
  (send_chain : ratchet.RatchetChain) (receive_chain : ratchet.RatchetChain) :
    ∃ result, ratchet.concrete.ConcreteRatchetKernel.new send_chain receive_chain = ok result :=
  ⟨_, rfl⟩

theorem pqxdh_concrete_start_initial_ratchet_kdf_total
  (root : Array Std.U8 32#usize) (initialization : pqxdh.RatchetInitialization) :
    ∃ result, pqxdh.concrete.start_initial_ratchet_kdf root initialization = ok result := ⟨_, rfl⟩

theorem pqxdh_concrete_start_beacon_ratchet_kdf_total
  (root : Array Std.U8 32#usize) :
    ∃ result, pqxdh.concrete.start_beacon_ratchet_kdf root = ok result :=
  (Static.pqxdh_BEACON_RATCHETS_total).elim fun i hi => ⟨_, by
    simp [pqxdh.concrete.start_beacon_ratchet_kdf, pqxdh.concrete.start_initial_ratchet_kdf,
      ratchet.SymmetricRatchetKdfRequest.new, hi]
    rfl⟩

theorem pqxdh_concrete_start_server_ratchet_kdf_total
  (root : Array Std.U8 32#usize) :
    ∃ result, pqxdh.concrete.start_server_ratchet_kdf root = ok result :=
  (Static.pqxdh_SERVER_RATCHETS_total).elim fun i hi => ⟨_, by
    simp [pqxdh.concrete.start_server_ratchet_kdf, pqxdh.concrete.start_initial_ratchet_kdf,
      ratchet.SymmetricRatchetKdfRequest.new, hi]
    rfl⟩

theorem pqxdh_concrete_start_beacon_candidate_ratchet_kdf_total
  (candidate : pqxdh.BeaconRegistrationCandidate)
  (root : Array Std.U8 32#usize) :
    ∃ result, pqxdh.concrete.start_beacon_candidate_ratchet_kdf candidate root = ok result :=
  (Static.pqxdh_BEACON_RATCHETS_total).elim fun i hi => ⟨_, by
    simp [pqxdh.concrete.start_beacon_candidate_ratchet_kdf,
      pqxdh.BeaconRegistrationCandidate.ratchet_initialization,
      pqxdh.concrete.start_initial_ratchet_kdf, ratchet.SymmetricRatchetKdfRequest.new, hi]
    rfl⟩

theorem pqxdh_concrete_start_server_candidate_ratchet_kdf_total
  (candidate : pqxdh.ServerRegistrationCandidate)
  (root : Array Std.U8 32#usize) :
    ∃ result, pqxdh.concrete.start_server_candidate_ratchet_kdf candidate root = ok result :=
  (Static.pqxdh_SERVER_RATCHETS_total).elim fun i hi => ⟨_, by
    simp [pqxdh.concrete.start_server_candidate_ratchet_kdf,
      pqxdh.ServerRegistrationCandidate.ratchet_initialization,
      pqxdh.concrete.start_initial_ratchet_kdf, ratchet.SymmetricRatchetKdfRequest.new, hi]
    rfl⟩

theorem pqxdh_BeaconRegistrationCandidate_ratchet_initialization_total
  (self : pqxdh.BeaconRegistrationCandidate) :
    ∃ result, pqxdh.BeaconRegistrationCandidate.ratchet_initialization self = ok result :=
  Static.pqxdh_BEACON_RATCHETS_total

theorem pqxdh_ServerRegistrationCandidate_ratchet_initialization_total
  (self : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.ServerRegistrationCandidate.ratchet_initialization self = ok result :=
  Static.pqxdh_SERVER_RATCHETS_total

theorem pqxdh_validate_registration_status_total
  (registration_status : pqxdh.RegistrationStatus) :
    ∃ result, pqxdh.validate_registration_status registration_status = ok result := by
  cases registration_status <;> simp [pqxdh.validate_registration_status]

theorem pqxdh_BeaconRegistrationCandidate_key_id_binding_total
  (self : pqxdh.BeaconRegistrationCandidate) :
    ∃ result, pqxdh.BeaconRegistrationCandidate.key_id_binding self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerRegistrationCandidate_key_id_binding_total
  (self : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.ServerRegistrationCandidate.key_id_binding self = ok result := ⟨_, rfl⟩

theorem pqxdh_beacon_commit_total
  (authenticated : pqxdh.AuthenticatedBeaconRegistration) :
    ∃ result, pqxdh.beacon_commit authenticated = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetMaterial_from_bytes_total
  (key : Array Std.U8 32#usize) (nonce : Array Std.U8 12#usize) :
    ∃ result, ratchet.RatchetMaterial.from_bytes key nonce = ok result := ⟨_, rfl⟩

theorem ratchet_refined_RefinedRatchet_send_sequence_total
  {SendChain : Type} {ReceiveChain : Type} {Material : Type}
  (self : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material) :
    ∃ result, ratchet.refined.RefinedRatchet.send_sequence self = ok result := ⟨_, rfl⟩

theorem ratchet_refined_RefinedRatchet_receive_sequence_total
  {SendChain : Type} {ReceiveChain : Type} {Material : Type}
  (self : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material) :
    ∃ result, ratchet.refined.RefinedRatchet.receive_sequence self = ok result := ⟨_, rfl⟩

theorem ratchet_refined_RefinedRatchet_receive_cache_len_total
  {SendChain : Type} {ReceiveChain : Type} {Material : Type}
  (self : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material) :
    ∃ result, ratchet.refined.RefinedRatchet.receive_cache_len self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_ConcreteRatchetKernel_send_sequence_total
  (self : ratchet.concrete.ConcreteRatchetKernel) :
    ∃ result, ratchet.concrete.ConcreteRatchetKernel.send_sequence self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_ConcreteRatchetKernel_receive_sequence_total
  (self : ratchet.concrete.ConcreteRatchetKernel) :
    ∃ result, ratchet.concrete.ConcreteRatchetKernel.receive_sequence self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_ConcreteRatchetKernel_receive_cache_len_total
  (self : ratchet.concrete.ConcreteRatchetKernel) :
    ∃ result, ratchet.concrete.ConcreteRatchetKernel.receive_cache_len self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_ConcreteRatchetKernel_send_chain_total
  (self : ratchet.concrete.ConcreteRatchetKernel) :
    ∃ result, ratchet.concrete.ConcreteRatchetKernel.send_chain self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_ConcreteRatchetKernel_receive_chain_total
  (self : ratchet.concrete.ConcreteRatchetKernel) :
    ∃ result, ratchet.concrete.ConcreteRatchetKernel.receive_chain self = ok result := ⟨_, rfl⟩

end BeaconcryptCore.PanicFreedom.Structural
