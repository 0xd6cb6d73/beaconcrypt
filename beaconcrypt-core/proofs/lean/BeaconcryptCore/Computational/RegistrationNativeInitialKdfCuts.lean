-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitializedRootAgreement

/-! Actual initial-record success retains the reached concrete initial-KDF reply and its source resume, rather than replacing an abstract path's arbitrary reply afterward. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitialKdfCuts
open RegistrationRecordPrimitives (Spec)
variable {S : Type}

/-- The reached Server initializer actually consumes its interpreter's concrete initial response before the rest of the first-record computation. -/
theorem server (implementation : QueryImpl Spec (StateT S ProbComp))
    (response : ratchet.SymmetricRatchetKdfRequest → pqxdh.concrete.InitialRatchetKdfResponse)
    (law : ∀ request before answer after, (answer, after) ∈ support ((implementation (.initialKdf request)).run before) → answer = .Some (response request))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((simulateQ implementation (RegistrationServerRecordExecutor.fromInitial initial)).run before)) :
    ∃ request atStep next,
      initial.request = .ok request ∧
      (.Some (response request), atStep) ∈ support ((implementation (.initialKdf request)).run before) ∧
      initial.resume (.Some (response request)) = .ok (.Ok next) ∧
      (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (RegistrationServerRecordExecutor.fromRatchet next)).run atStep) := by
  cases requested : initial.request with
  | fail error | div => simp [RegistrationServerRecordExecutor.fromInitial, RegistrationServerRecordExecutor.continueWith, requested] at supported
  | ok request =>
    simp only [RegistrationServerRecordExecutor.fromInitial, requested, RegistrationServerRecordExecutor.continueWith,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, atStep⟩, called, continued⟩ := supported
    have answerEq := law request before answer atStep called
    subst answer
    cases resumed : initial.resume (.Some (response request)) with
    | fail error | div => simp [RegistrationServerRecordExecutor.continueResult, resumed] at continued
    | ok result => cases result with
      | Err state => simp [RegistrationServerRecordExecutor.continueResult, resumed] at continued
      | Ok next =>
        exact ⟨request, atStep, next, rfl, called, resumed, by simpa only [RegistrationServerRecordExecutor.continueResult, resumed] using continued⟩

/-- The reached Beacon initializer actually consumes its concrete initial response before the unchanged first-record receive loop. -/
theorem beacon (implementation : QueryImpl Spec (StateT S ProbComp))
    (response : ratchet.SymmetricRatchetKdfRequest → pqxdh.concrete.InitialRatchetKdfResponse)
    (law : ∀ request before answer after, (answer, after) ∈ support ((implementation (.initialKdf request)).run before) → answer = .Some (response request))
    (initial : registration.BeaconInitialKdf) (completed : registration.CompletedBeacon) (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((simulateQ implementation (RegistrationBeaconRecordExecutor.fromInitial initial)).run before)) :
    ∃ request atStep next,
      initial.request = .ok request ∧
      (.Some (response request), atStep) ∈ support ((implementation (.initialKdf request)).run before) ∧
      initial.resume (.Some (response request)) = .ok (.Ok next) ∧
      (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (RegistrationBeaconRecordExecutor.program next)).run atStep) := by
  cases requested : initial.request with
  | fail error | div => simp [RegistrationBeaconRecordExecutor.fromInitial, RegistrationBeaconRecordExecutor.continueWith, requested] at supported
  | ok request =>
    simp only [RegistrationBeaconRecordExecutor.fromInitial, requested, RegistrationBeaconRecordExecutor.continueWith,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, atStep⟩, called, continued⟩ := supported
    have answerEq := law request before answer atStep called
    subst answer
    cases resumed : initial.resume (.Some (response request)) with
    | fail error | div => simp [resumed] at continued
    | ok result => cases result with
      | Err state => simp [resumed] at continued
      | Ok next =>
        exact ⟨request, atStep, next, rfl, called, resumed, by simpa only [resumed] using continued⟩

/-- The actual instrumented World initial getter returns the concrete fixed source response, with all reached counters and state retained. -/
theorem world_reply {n : Nat} {Auxiliary ι KemSK Reader Encoded : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Encoded)
    (request : ratchet.SymmetricRatchetKdfRequest) (before after : RegistrationWorldAgreement.State n Auxiliary)
    (answer : Spec.Range (.initialKdf request))
    (supported : (answer, after) ∈ support ((RegistrationWorldRecords.handler setup codec (.initialKdf request)).run before)) :
    answer = .Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request) := by
  have projected : (answer, RegistrationWorldAgreement.project after) ∈ support
      ((RegistrationRecordPrimitives.implementation setup.source codec.frameWrite (.initialKdf request)).run (RegistrationWorldAgreement.project before)) := by
    rw [← RegistrationWorldRecords.handler_project setup codec (.initialKdf request) before, support_map]
    exact Set.mem_image_of_mem (Prod.map id RegistrationWorldAgreement.project) supported
  rw [RegistrationRecordPrimitives.initial_exact] at projected
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at projected
  exact projected.1

end BeaconcryptCore.Computational.RegistrationNativeInitialKdfCuts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitialKdfCuts.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitialKdfCuts.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitialKdfCuts.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitialKdfCuts.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitialKdfCuts.world_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitialKdfCuts.world_reply
