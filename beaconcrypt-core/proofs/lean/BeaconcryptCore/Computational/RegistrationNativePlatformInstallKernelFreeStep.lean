-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelStorage
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedEntry
import BeaconcryptCore.Computational.RegistrationNativeInstallStep
import BeaconcryptCore.Computational.RegistrationNativeInstallTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconRuntime
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconPreparationRuntime
/-! The actual corrected shared-platform typed finish pairs its own concrete descriptor with its actual returned owner handle. Physical hiddenness follows from that same prepared descriptor and complete runtime. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelFreeStep
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformSelectiveInstallKernel (State)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativePlatformInstallKernelStorage (Valid events slots Selected)
open RegistrationNativeInstallTypedEntry (entry)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "sign" => RegistrationNativeMldsa.owned source credential
local notation "callback" => RegistrationNativeInstallRuntimeTrace.callback setup canonical sign seed scalar candidate provider service codec route
local notation "actual" => RegistrationNativePlatformSelectiveInstallKernel.typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route


/-- Every actual nonmaterial callback has no new installation descriptor or public installed handle. -/
theorem step (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5)
    (before : State n KemSK ProviderState Platform Secret source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK ProviderState Platform Secret source)
    (supported : result ∈ support ((actual query).run before)) (role : PqxdhRecordLiftInterface.Role) :
    RegistrationNativeInstallStep.RoleStep role (events before) (events result.2) (entry query result.1)
      (slots result.2) (Selected setup seed scalar candidate) := by
  have ordinary : ¬ RegistrationNativePublicCaps.IsMaterial query := by
    cases query with
    | inl coin => simp only [RegistrationNativePublicCaps.IsMaterial,not_false_eq_true]
    | inr command => cases command <;> simp_all [RegistrationNativePublicCaps.IsMaterial,RegistrationNativeRawAdapter.kind]
  have bound := RegistrationNativePlatformPublicOrdinaryInstall.handler_free (n := n) setup checks canonical source sign selectedOwner selectedAccept
    (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer role query ordinary before.2.1.1.1.1
  have sourceSupport := RegistrationNativePlatformSelectiveInstallKernel.open_support setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query before result supported
  apply RegistrationNativeInstallStep.of_quiet
  · exact RegistrationNativeInstallTrace.free role _ bound before.1 ((result.1,result.2.2.1.1.1.1),result.2.1) sourceSupport
  · cases query with
    | inl coin => cases role <;> rfl
    | inr command => cases command <;> cases role <;> first
        | rfl
        | simp only [RegistrationNativeRawAdapter.kind,ne_eq,not_true_eq_false,false_and,and_false] at quiet

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelFreeStep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelFreeStep.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelFreeStep.step
