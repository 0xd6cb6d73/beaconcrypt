-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldAgreement
import BeaconcryptCore.Computational.RegistrationBeaconInitHistory

/-! The complete actual Beacon Init runs in the same World and primitive state used by Server agreement and records. Its three Ed signing attempts retain their native auxiliary state and chronological replies. The Init transcript hash uses the existing shared World cache and coin counter; the Beacon issues no ML signing request, and the global Server signing ledger is preserved. Unrelated native request ledgers remain in the full state. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing

open RegistrationBeaconInitExecutor (Spec EdSpec)
open RegistrationBeaconInitShared (EdReceipt)
open RegistrationSigningShared (SignReply)
variable {n : Nat} {Auxiliary Encoded : Type}

abbrev State (n : Nat) (Auxiliary : Type) := RegistrationWorldAgreement.State n (Auxiliary × List EdReceipt)

def project (state : State n Auxiliary) : RegistrationBeaconInitShared.WorldState n Auxiliary :=
  (state.world, state.auxiliary)

noncomputable def implementation (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) : QueryImpl Spec (StateT (State n Auxiliary) ProbComp) :=
  fun query state => (fun result => (result.1, {state with world := result.2.1, auxiliary := result.2.2})) <$>
    (RegistrationBeaconInitShared.worldImplementation sign ed query).run (project state)

theorem query_project (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) (query : Spec.Domain) (before : State n Auxiliary) :
    Prod.map id project <$> (implementation sign ed query).run before =
      (RegistrationBeaconInitShared.worldImplementation sign ed query).run (project before) := by
  simp only [implementation, StateT.run, Functor.map_map, project, Prod.map, id_eq, Prod.mk.eta]
  exact id_map _

theorem program_project {Output : Type} (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) (work : OracleComp Spec Output) (before : State n Auxiliary) :
    Prod.map id project <$> (simulateQ (implementation sign ed) work).run before =
      (simulateQ (RegistrationBeaconInitShared.worldImplementation sign ed) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (query_project sign ed) work before

/-- Every native agreement/record request already reached by another role is retained through the complete outgoing Init. -/
theorem program_ledgers {Output : Type} (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) (work : OracleComp Spec Output) (before : State n Auxiliary)
    (result : Output × State n Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation sign ed) work).run before)) :
    result.2.requests = before.requests ∧ result.2.recordRequests = before.recordRequests := by
  apply simulateQ_run_preservesInv (implementation sign ed)
    (fun state => state.requests = before.requests ∧ state.recordRequests = before.recordRequests)
    _ work before ⟨rfl, rfl⟩ result supported
  intro query current earlier after reached
  simp only [implementation, StateT.run, support_map] at reached
  obtain ⟨_, _, rfl⟩ := reached
  exact earlier

theorem begin_coherent (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded) (before after : State n Auxiliary)
    (supported : (.ok (.Ok published), after) ∈ support
      ((simulateQ (implementation sign ed) (RegistrationBeaconInitExecutor.begin encode control inputs coins pin)).run before)) :
    published.pending.control.expected_server_binding = published.pending.binding.server_pin.binding :=
  RegistrationBeaconInitExecutor.simulated_coherent (implementation sign ed) encode control inputs coins pin published before after supported

/-- Cached chronological ML signing receipts of the shared Server signing ledger are preserved through all native Ed, transcript-hash and encoder outcomes. -/
theorem begin_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (before : State n Auxiliary)
    (cached : RegistrationSigningShared.Cached (RegistrationWorldSigning.project before.world))
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × State n Auxiliary)
    (supported : result ∈ support
      ((simulateQ (implementation sign ed) (RegistrationBeaconInitExecutor.begin encode control inputs coins pin)).run before)) :
    RegistrationSigningShared.Cached (RegistrationWorldSigning.project result.2.world) := by
  apply RegistrationBeaconInitHistory.world_cached sign ed encode control inputs coins pin
    (project before) cached (result.1, project result.2)
  rw [← program_project sign ed _ before, support_map]
  exact Set.mem_image_of_mem (Prod.map id project) supported

end BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing.query_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing.program_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing.program_ledgers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing.program_ledgers

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing.begin_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing.begin_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing.begin_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconOutgoing.begin_cached
