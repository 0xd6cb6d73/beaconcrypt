-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitialKdfCuts
import BeaconcryptCore.Computational.RegistrationNativeInitialKdfSource

/-! Concrete original Server and Beacon first-record success retain their actually consumed fixed-source initial-KDF replies and complete reached states. The Beacon begin receipt also ties the initializer to its original root-bearing agreement. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitialKdfReceipt
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeBeaconFrontend (M)
open RegistrationNativeResponseAuthentication (lower_bind lower_pure)
variable {n : Nat} {ι KemSK Auxiliary Reader Encoded V κ : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source} {spec : OracleSpec κ}

private theorem lower_simulate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (implementation : QueryImpl spec (M n KemSK source RegistrationServerRoleBackend.State)) (work : OracleComp spec V) :
    lower setup checks representation created (simulateQ implementation work) =
      simulateQ (fun query => lower setup checks representation created (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, lower_bind, ih]

/-- Actual Server record success consumes the concrete initial reply at its same instrumented World state. -/
theorem server (setup : Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Encoded)
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (before after : RegistrationWorldAgreement.State n Auxiliary)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((simulateQ (RegistrationWorldRecords.handler setup codec) (RegistrationServerRecordExecutor.fromInitial initial)).run before)) :
    ∃ request atStep next,
      initial.request = .ok request ∧
      (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request), atStep) ∈ support
        ((RegistrationWorldRecords.handler setup codec (.initialKdf request)).run before) ∧
      initial.resume (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request)) = .ok (.Ok next) ∧
      (.ok (.Ok completed), after) ∈ support
        ((simulateQ (RegistrationWorldRecords.handler setup codec) (RegistrationServerRecordExecutor.fromRatchet next)).run atStep) :=
  RegistrationNativeInitialKdfCuts.server (RegistrationWorldRecords.handler setup codec)
    (RawCtxSourceHkdf.initialResponse setup.source.crypto) (fun request before answer after =>
      RegistrationNativeInitialKdfCuts.world_reply setup codec request before after answer) initial completed before after supported

/-- Actual lowered Beacon record success consumes the concrete initial reply before its unchanged source receive loop. -/
theorem beacon (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (initial : registration.BeaconInitialKdf) (completed : registration.CompletedBeacon) (before after : Local n KemSK source)
    (supported : (.ok (.Ok completed), after) ∈ support ((lower setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial))).run before)) :
    ∃ request atStep next,
      initial.request = .ok request ∧
      (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request), atStep) ∈ support
        ((lower setup checks representation created (RegistrationNativeBeaconFrontend.record setup wire (.initialKdf request))).run before) ∧
      initial.resume (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request)) = .ok (.Ok next) ∧
      (.ok (.Ok completed), after) ∈ support ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.program next))).run atStep) := by
  rw [lower_simulate] at supported
  obtain ⟨request, atStep, next, requested, called, resumed, continued⟩ := RegistrationNativeInitialKdfCuts.beacon
    (fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.record setup wire query))
    (RawCtxSourceHkdf.initialResponse setup.source.crypto) (fun request before answer after =>
      RegistrationNativeInitialKdfSource.beacon_reply setup checks wire representation created request before after answer)
    initial completed before after supported
  exact ⟨request, atStep, next, requested, called, resumed, by simpa only [lower_simulate] using continued⟩

/-- Successful original Beacon first-record begin exposes its actual root-bearing initializer and same-cut concrete initial response. -/
theorem beacon_begin (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (capability : agreement.BeaconAgreement) (completed : registration.CompletedBeacon) (before after : Local n KemSK source)
    (supported : (.ok (.Ok completed), after) ∈ support ((lower setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run before)) :
    ∃ initial request atStep next,
      registration.begin_beacon_completion capability = .ok initial ∧ initial.agreement = capability ∧
      initial.request = .ok request ∧
      (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request), atStep) ∈ support
        ((lower setup checks representation created (RegistrationNativeBeaconFrontend.record setup wire (.initialKdf request))).run before) ∧
      initial.resume (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request)) = .ok (.Ok next) ∧
      (.ok (.Ok completed), after) ∈ support ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.program next))).run atStep) := by
  cases started : registration.begin_beacon_completion capability with
  | fail error | div =>
    simp only [RegistrationBeaconRecordExecutor.begin, started, RegistrationBeaconRecordExecutor.continueWith,
      simulateQ_pure, lower_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    cases supported.1
  | ok initial =>
    simp only [RegistrationBeaconRecordExecutor.begin, started, RegistrationBeaconRecordExecutor.continueWith] at supported
    obtain ⟨request, atStep, next, requested, called, resumed, continued⟩ := beacon setup checks wire representation created initial completed before after supported
    exact ⟨initial, request, atStep, next, rfl, RegistrationBeaconRecordExecutor.initial_agreement capability initial started,
      requested, called, resumed, continued⟩

end BeaconcryptCore.Computational.RegistrationNativeInitialKdfReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitialKdfReceipt.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitialKdfReceipt.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitialKdfReceipt.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitialKdfReceipt.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitialKdfReceipt.beacon_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitialKdfReceipt.beacon_begin
