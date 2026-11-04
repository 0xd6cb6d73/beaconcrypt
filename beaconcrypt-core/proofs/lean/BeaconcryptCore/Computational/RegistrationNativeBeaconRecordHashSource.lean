-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconRecordTrace
import BeaconcryptCore.Computational.RegistrationNativeInitialKdfReceipt

/-! Actual successful native Beacon first-record execution supplies its actually checked commitment preimage, returned digest and supplied commitment in one later shared-cache anchor, with the concrete source initializer and exact hash/open trace retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconRecordHashSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeBeaconFrontend (M)
open RegistrationNativeResponseAuthentication (lower_bind lower_pure)
open RegistrationNativeBeaconRecordTrace (Trace)
variable {n : Nat} {ι KemSK V κ : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source} {spec : OracleSpec κ}

private theorem lower_simulate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (implementation : QueryImpl spec (M n KemSK source RegistrationServerRoleBackend.State)) (work : OracleComp spec V) :
    lower setup checks representation created (simulateQ implementation work) =
      simulateQ (fun query => lower setup checks representation created (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, lower_bind, ih]

/-- The actually checked Beacon commitment has the same returned/supplied digest and remains cached at the actual later source anchor. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (capability : agreement.BeaconAgreement) (completed : registration.CompletedBeacon) (before after : Local n KemSK source)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (supported : (.ok (.Ok completed), after) ∈ support ((lower setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run before))
    (extension : RegistrationNativeWorldCache.cache after.2.2 ≤ cache) :
    ∃ (initial : registration.BeaconInitialKdf) (request : ratchet.SymmetricRatchetKdfRequest)
      (atStep : Local n KemSK source) (phase : registration.BeaconInitialOpen)
      (trace : Trace (fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.record setup wire query)) phase completed atStep after),
    ∃ digest, registration.begin_beacon_completion capability = .ok initial ∧ initial.agreement = capability ∧
      initial.request = .ok request ∧ initial.resume (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request)) = .ok (.Ok phase) ∧
      trace.hashReply = .Some (RegistrationAuthenticationShared.digestArray digest) ∧
      absBytes trace.supplied = digest.toList ∧ cache ((), absBytes trace.transcript.bytes) = some digest := by
  obtain ⟨initial, request, atStep, phase, started, sameAgreement, requested, _initialCalled, resumed, continued⟩ :=
    RegistrationNativeInitialKdfReceipt.beacon_begin setup checks wire representation created capability completed before after supported
  rw [lower_simulate] at continued
  obtain ⟨trace⟩ := RegistrationNativeBeaconRecordTrace.run
    (fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.record setup wire query)) phase completed atStep after
    (RegistrationNativeBeaconCommitmentOrder.initial initial _ phase resumed) continued
  obtain ⟨digest, replyEq, _beforeHash, cached⟩ := RegistrationNativeRecordHashReceipt.beacon setup checks wire representation created
    trace.transcript trace.atHash trace.afterHash trace.hashReply trace.hashCalled
  have throughOpen : RegistrationNativeWorldCache.cache trace.afterHash.2.2 ≤ RegistrationNativeWorldCache.cache after.2.2 :=
    RegistrationNativeWorldCache.localProgram setup checks representation created
      (RegistrationNativeBeaconFrontend.record setup wire (.openAead trace.aeadRequest)) trace.afterHash (trace.openReply, after) trace.aeadCalled
  have matched := trace.matched
  rw [replyEq] at matched
  simp only [RegistrationBeaconRecordExecutor.commitmentMatches, RegistrationAuthenticationShared.digest_array_bytes, decide_eq_true_eq] at matched
  exact ⟨initial, request, atStep, phase, trace, digest, started, sameAgreement, requested, resumed, replyEq,
    matched.symm, extension (throughOpen cached)⟩

end BeaconcryptCore.Computational.RegistrationNativeBeaconRecordHashSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRecordHashSource.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRecordHashSource.run
