-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld

/-! A supported actual guarded typed callback retains its exact original frontend result and G2 chronology when private interpretation is forgotten. This is the same execution's support projection, with no independently chosen trace or frontend state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelSupport
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeSelectiveInstallKernel (State typed)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Forgetting only private interpretation preserves the literal same typed result, frontend poststate and chronological trace. -/
theorem open_support (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) (query : TypedSpec.Domain) (before : State n KemSK ProviderState Secret source)
    (result : TypedSpec.Range query × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept query).run before)) :
    ((result.1, result.2.2.1.1.1.1), result.2.1) ∈ support
      ((simulateQ RegistrationNativeG2Trace.handler
        ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar) query).run
          before.2.1.1.1.1)).run before.1) := by
  simp only [typed, StateT.run, support_map] at supported
  obtain ⟨raw, actual, returned⟩ := supported
  rcases raw with ⟨⟨reply, trace⟩, after⟩
  cases returned
  have opened := RegistrationNativeSelectiveHiddenDemandWorld.lower_support service codec route _ before.2 ((reply, trace), after) actual
  rw [RegistrationNativeSelectiveEntropyEffects.close_run, support_map] at opened
  obtain ⟨closed, called, closedEq⟩ := opened
  have original : closed.1 ∈ support
      ((RegistrationNativeSelectiveInstallKernel.front
        (RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar))
          before.1 query).run before.2.1.1.1.1) := by
    apply support_simulateQ_run'_subset
      (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) _ before.2.1.1.1.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  simp only [RegistrationNativeSelectiveInstallKernel.front, StateT.run, support_map] at original
  obtain ⟨native, possible, nativeEq⟩ := original
  have value : closed.1.1 = (reply, trace) := congrArg Prod.fst closedEq
  have frontend : closed.1.2 = after.1.1.1.1 := congrArg (fun result => result.2.1) closedEq
  have same : native = ((reply, after.1.1.1.1), trace) :=
    Prod.ext
      (Prod.ext ((congrArg (fun result => result.1.1) nativeEq).trans (congrArg Prod.fst value))
        ((congrArg Prod.snd nativeEq).trans frontend))
      ((congrArg (fun result => result.1.2) nativeEq).trans (congrArg Prod.snd value))
  rw [← same]
  exact possible

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelSupport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelSupport.open_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelSupport.open_support
