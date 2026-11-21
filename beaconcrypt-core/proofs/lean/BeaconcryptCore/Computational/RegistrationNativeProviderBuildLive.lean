-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBuildSource
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildLive

/-! The actual provider-parametric build keeps its provider state and its remaining live prepared roots through every native failure or success. These internal adaptive invariants are derived from the literal one-use controller rather than imposed on a later public event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBuildLive
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (FrontState execute)
open RegistrationNativePublicSourceState (Live MemoCorrect)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

theorem provider_kept (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (handle : Nat) (application : Option (Slice U8))
    (before : FrontState n KemSK ProviderState source)
    (result : RegistrationServerMaterialFrontend.Result × FrontState n KemSK ProviderState source)
    (supported : result ∈ support ((execute setup wire route sign seed scalar provider
      (RegistrationNativePublicFrontend.serverOpen false
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application))).run before)) :
    result.2.2.2 = before.2.2 := by
  rw [RegistrationNativeProviderBuildSource.execute_frame, support_map] at supported
  obtain ⟨inner, _reached, returned⟩ := supported
  exact congrArg (fun output => output.2.2.2) returned.symm

/-- Actual build consumption preserves all other prepared sessions and the literal memo under every provider. -/
theorem build_live (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (handle : Nat) (application : Option (Slice U8))
    (before : FrontState n KemSK ProviderState source)
    (result : RegistrationServerMaterialFrontend.Result × FrontState n KemSK ProviderState source)
    (live : Live before.1 before.2.1) (correct : MemoCorrect setup seed scalar before.2.1.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar provider
      (RegistrationNativePublicFrontend.serverOpen false
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application))).run before)) :
    Live result.2.1 result.2.2.1 ∧ MemoCorrect setup seed scalar result.2.2.1.roots := by
  rw [RegistrationNativeProviderBuildSource.execute_frame, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  cases returned
  exact RegistrationNativePublicSourceBuildLive.build_live setup wire checks route sign seed scalar handle application
    (before.1, before.2.1) inner live correct reached

end BeaconcryptCore.Computational.RegistrationNativeProviderBuildLive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildLive.provider_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildLive.provider_kept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildLive.build_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildLive.build_live
