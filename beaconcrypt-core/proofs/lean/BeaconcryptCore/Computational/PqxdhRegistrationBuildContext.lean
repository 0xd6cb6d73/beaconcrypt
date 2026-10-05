-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerRegistrationPublication

/-! The actual response builder is independent of the already-consumed registration context. Mapping that context commutes with its complete callback program, not merely its returned response. This is a local source fact: it does not relocate an earlier admission between Server objects or establish a global ProVerif scheduling abstraction. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRegistrationBuildContext
open PqxdhServerRegistrationPublication

variable {Metadata PeerMetadata Consumed Other : Type}

/-- Change only the consumed context, retaining the entire peer map and allocation state. -/
def mapContext (f : Consumed → Other) (state : State Metadata PeerMetadata Consumed) :
    State Metadata PeerMetadata Other :=
  ⟨state.server, state.identityKeyId, state.control, f state.consumed⟩

/-- The same map on an ordinary optional publication result. -/
def mapReply (f : Consumed → Other) :
    Option Response × State Metadata PeerMetadata Consumed →
      Option Response × State Metadata PeerMetadata Other :=
  fun result => (result.1, mapContext f result.2)

/-- Preserve diagnostic failure and divergence as well as the actual optional response. -/
def mapResult (f : Consumed → Other) :
    RustM (Option Response × State Metadata PeerMetadata Consumed) →
      RustM (Option Response × State Metadata PeerMetadata Other)
  | .ok result => .ok (mapReply f result)
  | .fail error => .fail error
  | .div => .div

/-- Publication never inspects the consumed context. -/
theorem publish_map (f : Consumed → Other) (state : State Metadata PeerMetadata Consumed)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (metadata : PeerMetadata) :
    publish (mapContext f state) candidate kernel metadata =
      mapContext f (publish state candidate kernel metadata) := rfl

/-- The complete seal, erase and outer-writer tail commutes with the context map. -/
theorem after_map (f : Consumed → Other) (state : State Metadata PeerMetadata Consumed)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Bytes)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (metadata : PeerMetadata) :
    afterInitialization candidate authenticated kernel metadata (mapContext f state) =
      mapReply f <$> afterInitialization candidate authenticated kernel metadata state := by
  simp only [afterInitialization, map_bind]
  congr 1
  funext sent
  congr 1
  funext erased
  cases sent.2 <;> simp only [map_bind, map_pure, mapReply]
  congr 1
  funext written
  cases written <;> simp only [map_pure, mapReply, publish_map]

private theorem continue_map {α : Type} (f : Consumed → Other) (value : RustM α)
    (next : α → OracleComp TailSpec
      (RustM (Option Response × State Metadata PeerMetadata Consumed))) :
    continueRust value (fun result => mapResult f <$> next result) =
      mapResult f <$> continueRust value next := by
  cases value <;> simp only [continueRust, map_pure, mapResult]

/-- Identity, reservation, initialization and binding retain the same complete callback tree. -/
theorem candidate_map (f : Consumed → Other) (state : State Metadata PeerMetadata Consumed)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Bytes) (metadata : PeerMetadata) :
    candidateTail source candidate root data metadata (mapContext f state) =
      mapResult f <$> candidateTail source candidate root data metadata state := by
  simp only [candidateTail, map_bind]
  congr 1
  funext valid
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true,
    ite_false, map_pure, map_bind, mapResult, mapReply]
  congr 1
  funext reserved
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true,
    ite_false, map_pure, mapResult, mapReply]
  rw [← continue_map]
  congr 1
  funext kernel
  split_ifs <;> simp only [map_pure, mapResult, mapReply, map_bind]
  congr 1
  funext allocated
  cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true,
    ite_false, map_pure, mapResult, mapReply]
  rw [← continue_map]
  congr 1
  funext binding
  simp only [after_map, Functor.map_map, mapResult]

/-- The actual builder's only consumed-context operation is returning that context unchanged. -/
theorem build_map (f : Consumed → Other) (state : State Metadata PeerMetadata Consumed)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Bytes) (metadata : PeerMetadata) :
    build source pending root data metadata (mapContext f state) =
      mapResult f <$> build source pending root data metadata state := by
  simp only [build, mapContext]
  rw [← continue_map]
  congr 1
  funext next
  cases next <;> simp only [map_pure, mapResult, mapReply, mapContext]
  rw [← continue_map]
  congr 1
  funext prepared
  cases prepared <;> simp only [map_pure, mapResult, mapReply, ← candidate_map] <;> rfl

/-- Any stateful probabilistic implementation keeps its entire final private state under the map. -/
theorem build_interpreted {PrimitiveState ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (f : Consumed → Other) (state : State Metadata PeerMetadata Consumed)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Bytes) (metadata : PeerMetadata) (primitive : PrimitiveState) :
    ((simulateQ impl (build source pending root data metadata (mapContext f state))).run primitive) =
      (fun result => (mapResult f result.1, result.2)) <$>
        ((simulateQ impl (build source pending root data metadata state)).run primitive) := by
  rw [build_map, simulateQ_map, StateT.run_map]

/-- The equality quantifies over the complete continuation, including the original interpreter state. -/
theorem build_continuation {PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (f : Consumed → Other) (state : State Metadata PeerMetadata Consumed)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Bytes) (metadata : PeerMetadata) (primitive : PrimitiveState)
    (next : RustM (Option Response × State Metadata PeerMetadata Other) × PrimitiveState →
      OracleComp base Result) :
    (((simulateQ impl (build source pending root data metadata (mapContext f state))).run primitive)
      >>= next) =
    (((simulateQ impl (build source pending root data metadata state)).run primitive)
      >>= fun result => next (mapResult f result.1, result.2)) := by
  rw [build_interpreted, bind_map_left]

/-- Every selective logical query bound is unchanged; no discarded callback is declared free. -/
theorem build_queries (f : Consumed → Other) (state : State Metadata PeerMetadata Consumed)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Bytes) (metadata : PeerMetadata) (select : TailSpec.Domain → Prop)
    [DecidablePred select] (bound : Nat) :
    (build source pending root data metadata (mapContext f state)).IsQueryBoundP select bound ↔
      (build source pending root data metadata state).IsQueryBoundP select bound := by
  rw [build_map, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.PqxdhRegistrationBuildContext

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.publish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.publish_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.after_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.after_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.candidate_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.candidate_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.build_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.build_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.build_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.build_interpreted

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.build_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.build_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.build_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBuildContext.build_queries
