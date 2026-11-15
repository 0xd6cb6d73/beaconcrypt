-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconRecordHashSource

/-! The actual native Beacon open callback returns the fixed source AEAD opening on its literal request. The record marker and lowered shared native state are retained; no protocol success or partner assumption enters this operational equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconOpenSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeResponseAuthentication (lower_bind lower_pure)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- The concrete record primitive executes the ordinary combined-ciphertext source opening. -/
theorem primitive (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (request : record.AeadRequest)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (RegistrationRecordPrimitives.implementation setup.source wire.frameWrite (.openAead request)).run state =
      pure (RegistrationAuthenticationShared.openedBytes
        (RawCtxSourceOpen.baseOpen setup.source.crypto (RegistrationRecordPrimitives.openInput request)), state) := by
  rfl

/-- The actual callback records the request, then returns precisely that source opening. -/
theorem record_open (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (request : record.AeadRequest) :
    RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire (.openAead request) =
      (do RegistrationNativeBeaconFrontend.updateEnv fun env => {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall (.openAead request)]}
          pure (RegistrationAuthenticationShared.openedBytes
            (RawCtxSourceOpen.baseOpen setup.source.crypto (RegistrationRecordPrimitives.openInput request)))) := by
  change (do
    RegistrationNativeBeaconFrontend.updateEnv fun env => {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall (.openAead request)]}
    RegistrationNativeBeaconFrontend.sample (Prod.fst <$>
      (RegistrationRecordPrimitives.implementation setup.source wire.frameWrite (.openAead request)).run ((), ∅))) = _
  rw [primitive]
  simp only [map_pure, RegistrationNativeBeaconFrontend.sample, simulateQ_pure]

/-- Every reached actual lowered opening reply has those exact source operands and result. -/
theorem reply (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (request : record.AeadRequest) (before after : Local n KemSK source)
    (answer : RegistrationRecordPrimitives.Spec.Range (.openAead request))
    (supported : (answer, after) ∈ support ((lower setup checks representation created
      (RegistrationNativeBeaconFrontend.record setup wire (.openAead request))).run before)) :
    answer = RegistrationAuthenticationShared.openedBytes
      (RawCtxSourceOpen.baseOpen setup.source.crypto (RegistrationRecordPrimitives.openInput request)) := by
  rw [record_open, lower_bind] at supported
  simp only [lower_pure, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨ignored, current⟩, _updated, returned⟩ := supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  exact returned.1

end BeaconcryptCore.Computational.RegistrationNativeBeaconOpenSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconOpenSource.primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconOpenSource.primitive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconOpenSource.record_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconOpenSource.record_open

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconOpenSource.reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconOpenSource.reply
