-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceNativeProgram

/-! Actual indexed preparation and ordinary source preparation share the literal pure-pin prefix and source seed/prekey suffix. The only erased state here is the indexed identity pool/transcript, after its exact stored seed has realized the returned native preparation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityPreparationSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation ambient)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every actual public preparation query program has the complete original native preparation reply and World/context after private credential realization. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK) :
    (fun result => (RegistrationNativeIdentityRealization.preparedReply result.2.identities result.1, result.2.context)) <$>
      (simulateQ (implementation (mlSource := source) setup checks representation created)
        (RegistrationNativeIdentitySourcePrepare.program source edPin mlPin keyId)).run before =
      (simulateQ (ambient (mlSource := source) setup checks representation created)
        (RegistrationNativeIdentitySourceCommon.nativeProgram source edPin mlPin keyId)).run before.context := by
  rw [RegistrationNativeIdentitySourceCommon.exposed_factor]
  simp only [RegistrationNativeIdentitySourceCommon.exposedProgram,
    RegistrationNativeIdentitySourceCommon.nativeProgram, simulateQ_bind, StateT.run_bind, map_bind]
  rw [RegistrationNativeIdentitySourceFrame.ambient_program]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨earlier, current⟩
  cases earlier with
  | fail error =>
      simp only [RegistrationNativeIdentitySourceCommon.afterExposed, RegistrationNativeIdentitySourceCommon.afterNative,
        simulateQ_pure, StateT.run_pure, map_pure, RegistrationNativeIdentityRealization.preparedReply]
  | div =>
      simp only [RegistrationNativeIdentitySourceCommon.afterExposed, RegistrationNativeIdentitySourceCommon.afterNative,
        simulateQ_pure, StateT.run_pure, map_pure, RegistrationNativeIdentityRealization.preparedReply]
  | ok reply => cases reply with
    | none =>
        simp only [RegistrationNativeIdentitySourceCommon.afterExposed, RegistrationNativeIdentitySourceCommon.afterNative,
          simulateQ_pure, StateT.run_pure, map_pure, RegistrationNativeIdentityRealization.preparedReply, Option.map_none]
    | some prepared =>
        exact RegistrationNativeIdentitySourceSuffix.source_exact setup checks representation created prepared
          ⟨current, before.identities⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityPreparationSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPreparationSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPreparationSource.program_source
