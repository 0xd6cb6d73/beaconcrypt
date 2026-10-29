-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallFreeTyped
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelSupport
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedEntry

/-! Actual nonmaterial typed callbacks preserve the installation chronology and have no successful installation handle. The receipt follows the same original G2 trace projected from the guarded physical kernel, retaining all reached private state. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelFreeStep
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveInstallKernel (State typed)
open RegistrationNativeInstallKernelStorage (events slots Selected)
open RegistrationNativeInstallTypedEntry (entry)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every actual nonmaterial callback supplies its exact empty installation suffix under the guarded physical execution. -/
theorem step (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (selectedOwner selectedAccept : Nat)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5)
    (before : State n KemSK ProviderState Secret source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept query).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    RegistrationNativeInstallStep.RoleStep role (events before) (events result.2) (entry query result.1)
      (slots result.2) (Selected setup seed scalar candidate) := by
  apply RegistrationNativeInstallStep.of_quiet
  · exact RegistrationNativeInstallFreeTyped.messages_free role setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
      query quiet before.2.1.1.1.1 before.1 ((result.1, result.2.2.1.1.1.1), result.2.1)
      (RegistrationNativeInstallKernelSupport.open_support setup checks wire sign seed scalar candidate provider service codec route
        selectedOwner selectedAccept query before result supported)
  · cases query with
    | inl coin => cases role <;> rfl
    | inr query =>
        cases query <;> cases role <;> first
          | rfl
          | simp only [RegistrationNativeRawAdapter.kind, ne_eq, not_true_eq_false, false_and, and_false] at quiet

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelFreeStep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelFreeStep.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelFreeStep.step
