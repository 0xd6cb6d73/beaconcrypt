-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitializedRootAgreement

/-! The actual native Beacon initial-KDF callback returns the concrete fixed source output before resuming the original first-record controller. Request instrumentation and every actual source prefix remain retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitialKdfSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeResponseAuthentication (lower_bind lower_pure)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- The actual optional initial getter is the fixed native source result, after its literal request-marker append. -/
theorem record_initial (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (request : ratchet.InitialRatchetKdfRequest) :
    RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire (.initialKdf request) =
      (do RegistrationNativeBeaconFrontend.updateEnv fun env => {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall (.initialKdf request)]}
          pure (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request))) := by
  change (do
    RegistrationNativeBeaconFrontend.updateEnv fun env => {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall (.initialKdf request)]}
    RegistrationNativeBeaconFrontend.sample (Prod.fst <$>
      (RegistrationRecordPrimitives.implementation setup.source wire.frameWrite (.initialKdf request)).run ((), ∅))) = _
  rw [RegistrationRecordPrimitives.initial_exact]
  simp only [map_pure, RegistrationNativeBeaconFrontend.sample, simulateQ_pure]

/-- Every reached lowered initial callback has this actual source reply, without a state-reset or reply-simulation premise. -/
theorem beacon_reply (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (request : ratchet.InitialRatchetKdfRequest) (before after : Local n KemSK source)
    (answer : RegistrationRecordPrimitives.Spec.Range (.initialKdf request))
    (supported : (answer, after) ∈ support ((lower setup checks representation created
      (RegistrationNativeBeaconFrontend.record setup wire (.initialKdf request))).run before)) :
    answer = .Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request) := by
  rw [record_initial, lower_bind] at supported
  simp only [lower_pure, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨ignored, current⟩, _updated, returned⟩ := supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  exact returned.1

end BeaconcryptCore.Computational.RegistrationNativeInitialKdfSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitialKdfSource.record_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitialKdfSource.record_initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitialKdfSource.beacon_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitialKdfSource.beacon_reply
