-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconRuntime
import BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation
import BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController

/-! The actual complete chronological preparation cut preserves every role's successful descriptor prefix. Ordinary-owner translation is performed in that same source runtime before the returned Ready is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallBeaconPreparationRuntime
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeInstallRuntimeTrace (Runtime callback)
open RegistrationNativeInstallOrdinals (messages)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- The same guarded preparation execution preserves its exact per-role successful installation prefix. -/
theorem preparation_count (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (role : PqxdhRecordLiftInterface.Role) (ordinaryScalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner source) (env : EnvState Auxiliary) (packet : Option registration.ResponsePacket)
    (before : Runtime n KemSK ProviderState Secret)
    (result : (RustM (Option RegistrationBeaconReferenceRoot.Ready) × SelectedOwner source) × (EnvState Auxiliary × Runtime n KemSK ProviderState Secret))
    (supported : result ∈ support
      ((RegistrationNativeBeaconFinishController.lower
        (RegistrationNativeTypedBeaconAllController.interpreter
          (callback setup wire sign seed scalar candidate provider service codec route) setup ordinaryScalar)
        ((RegistrationBeaconReferenceCompiler.finishPreparation (n := n) setup source packet).run owner)).run (env, before))) :
    messages role result.2.2.1.events = messages role before.1.events := by
  simp only [RegistrationNativeBeaconFinishController.lower, StateT.run, support_map] at supported
  obtain ⟨native, called, returned⟩ := supported
  have actual : native ∈ support ((simulateQ (callback setup wire sign seed scalar candidate provider service codec route)
    (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
      (RegistrationNativeTypedBeaconAllController.translated setup ordinaryScalar
        (((RegistrationBeaconReferenceCompiler.finishPreparation (n := n) setup source packet).run owner).run env)))).run before) := by
    cases ordinaryScalar <;> simpa only [RegistrationNativeTypedBeaconAllController.interpreter,
      RegistrationNativeTypedBeaconAllController.translated, QueryImpl.simulateQ_compose, StateT.run] using called
  have original := RegistrationNativeInstallRuntimeTrace.open_support setup wire sign seed scalar candidate provider service codec route _ before native actual
  have quiet := RegistrationNativeInstallFreePreparation.preparation_free (n := n) role setup source packet owner env
  have bounded : (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
      (RegistrationNativeTypedBeaconAllController.translated setup ordinaryScalar
        (((RegistrationBeaconReferenceCompiler.finishPreparation (n := n) setup source packet).run owner).run env))).IsQueryBoundP
          (RegistrationNativeInstallPredicate.GlobalInstall (KemSK := KemSK) role) 0 := by
    cases ordinaryScalar with
    | none => exact RegistrationNativeInstallRouting.local_bound role false _ 0 quiet
    | some scalar =>
        exact RegistrationNativeInstallRouting.local_bound role false _ 0
          (RegistrationNativeInstallRouting.ordinary_bound role setup scalar _ 0 quiet)
  have same := RegistrationNativeInstallTrace.free role _ bounded before.1 (native.1, native.2.1) original
  cases returned
  exact same

end BeaconcryptCore.Computational.RegistrationNativeInstallBeaconPreparationRuntime

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallBeaconPreparationRuntime.preparation_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallBeaconPreparationRuntime.preparation_count
