-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerRegistrationPublication

/-! A pure change of the outer response representation preserves publication effects and every optional failure. No cryptographic callback is changed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborResponseWriterMap
open PqxdhServerRegistrationPublication
variable {Metadata PeerMetadata Consumed PrimitiveState : Type}

def response (encode : Pqxdh.Bytes → Pqxdh.Bytes) (value : Response) : Response :=
  { value with serialized := encode value.serialized }

def outcome (encode : Pqxdh.Bytes → Pqxdh.Bytes)
    (value : Option Response × State Metadata PeerMetadata Consumed) :
    Option Response × State Metadata PeerMetadata Consumed :=
  (value.1.map (response encode), value.2)

def writer (encode : Pqxdh.Bytes → Pqxdh.Bytes)
    (implementation : QueryImpl TailSpec (StateT PrimitiveState ProbComp)) :
    QueryImpl TailSpec (StateT PrimitiveState ProbComp)
  | .inr (.write fields) => Option.map encode <$> implementation (.inr (.write fields))
  | query => implementation query

theorem send_unchanged (encode : Pqxdh.Bytes → Pqxdh.Bytes)
    (implementation : QueryImpl TailSpec (StateT PrimitiveState ProbComp))
    {α : Type} (work : OracleComp RawCtxSourceSend.PrimitiveSpec α) :
    simulateQ (writer encode implementation) (simulateQ sendLift work) =
      simulateQ implementation (simulateQ sendLift work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  rfl

theorem after_map (encode : Pqxdh.Bytes → Pqxdh.Bytes)
    (implementation : QueryImpl TailSpec (StateT PrimitiveState ProbComp))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState) :
    (simulateQ (writer encode implementation)
      (afterInitialization candidate authenticated kernel metadata state)).run primitive =
      (fun result => (outcome encode result.1, result.2)) <$>
        (simulateQ implementation
          (afterInitialization candidate authenticated kernel metadata state)).run primitive := by
  simp only [afterInitialization, simulateQ_bind, StateT.run_bind, send_unchanged,
    map_bind]
  apply bind_congr
  intro sent
  simp only [simulateQ_spec_query, writer]
  apply bind_congr
  intro erased
  cases encrypted : sent.1.2 <;>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, outcome, Option.map_none]
  simp only [simulateQ_bind, simulateQ_spec_query, writer, StateT.run_bind,
    bind_map_left, map_bind]
  apply bind_congr
  intro written
  cases written.1 <;>
    simp only [Option.map_none, Option.map_some, simulateQ_pure, StateT.run_pure,
      map_pure, response]

theorem candidate_map (encode : Pqxdh.Bytes → Pqxdh.Bytes)
    (implementation : QueryImpl TailSpec (StateT PrimitiveState ProbComp))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState) :
    (simulateQ (writer encode implementation) (candidateTail source candidate root data metadata state)).run primitive =
      (fun result => (outcome encode <$> result.1, result.2)) <$>
        (simulateQ implementation (candidateTail source candidate root data metadata state)).run primitive := by
  simp only [candidateTail, simulateQ_bind, simulateQ_spec_query, writer, StateT.run_bind,
    map_bind]
  apply bind_congr
  intro valid
  cases valid.1 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    simulateQ_pure, StateT.run_pure, map_pure]
  · rfl
  simp only [simulateQ_bind, simulateQ_spec_query, writer, StateT.run_bind, map_bind]
  apply bind_congr
  intro reserved
  cases reserved.1 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ite_true, ite_false, simulateQ_pure, StateT.run_pure, map_pure]
  · rfl
  cases initialized : BeaconcryptCore.Refinement.ServerTransactionRefinement.initializeCandidate candidate
      (PqxdhRootTableInitialization.rootArray root)
      (PqxdhRootTableInitialization.initialResponse source.crypto) <;>
    simp only [continueRust, simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
  case ok kernel =>
    split <;> (try simp only [simulateQ_pure, StateT.run_pure, map_pure]) <;> try rfl
    split <;> (try simp only [simulateQ_pure, StateT.run_pure, map_pure]) <;> try rfl
    simp only [simulateQ_bind, simulateQ_spec_query, writer, StateT.run_bind, map_bind]
    apply bind_congr
    intro allocated
    cases allocated.1 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_true, ite_false, simulateQ_pure, StateT.run_pure, map_pure]
    · rfl
    cases binding : candidate.key_id_binding <;>
      simp only [simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
    simp only [simulateQ_map, StateT.run_map, after_map, Functor.map_map]
    rfl

theorem build_map (encode : Pqxdh.Bytes → Pqxdh.Bytes)
    (implementation : QueryImpl TailSpec (StateT PrimitiveState ProbComp))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState) :
    (simulateQ (writer encode implementation) (build source pending root data metadata state)).run primitive =
      (fun result => (outcome encode <$> result.1, result.2)) <$>
        (simulateQ implementation (build source pending root data metadata state)).run primitive := by
  unfold build
  cases first : pqxdh.server_next_key_id state.control <;>
    simp only [continueRust, simulateQ_pure, StateT.run_pure, map_pure]
  all_goals try rfl
  case ok next =>
    cases next <;> simp only [simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
    case Ok nextId =>
      cases prepared : pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩
          (if (state.server.peers nextId).isSome then .Occupied else .Available) <;>
        simp only [simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
      case ok preparedResult =>
        cases preparedResult <;>
          simp only [simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
        exact candidate_map encode implementation source _ root data metadata state primitive

end BeaconcryptCore.Computational.CborResponseWriterMap

/-- info: 'BeaconcryptCore.Computational.CborResponseWriterMap.send_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseWriterMap.send_unchanged
/-- info: 'BeaconcryptCore.Computational.CborResponseWriterMap.after_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseWriterMap.after_map
/-- info: 'BeaconcryptCore.Computational.CborResponseWriterMap.candidate_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseWriterMap.candidate_map
/-- info: 'BeaconcryptCore.Computational.CborResponseWriterMap.build_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseWriterMap.build_map
