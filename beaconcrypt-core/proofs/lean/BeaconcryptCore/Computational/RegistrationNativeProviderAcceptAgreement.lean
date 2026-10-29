-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptStage

/-! Actual reference agreement reconstructs the native source capability while retaining the same current provider. Only the private prepared-root memo is reset in the observation. The extra generic-engine cache has already been removed without touching the actual World cache inside the auxiliary state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAgreement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (localImpl)
open RegistrationNativeProviderAcceptRun (State close)
open RegistrationNativeProviderAcceptStage (resetAux)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}

def project (roots : RegistrationServerReferenceRestore.Roots) (memo : RegistrationNativeReferenceInterpreter.State)
    (before : State n KemSK ProviderState) : RegistrationNativeProviderAcceptSdk.State n KemSK ProviderState :=
  (RegistrationNativeProviderAcceptFields.restore roots before.1, resetAux memo before.2)

def nativeProject (memo : RegistrationNativeReferenceInterpreter.State)
    (before : RegistrationNativeProviderAcceptSdk.State n KemSK ProviderState) : RegistrationNativeProviderAcceptSdk.State n KemSK ProviderState :=
  (before.1, resetAux memo before.2)

def restore (roots : RegistrationServerReferenceRestore.Roots) (before : State n KemSK ProviderState) :
    RegistrationNativeProviderAcceptSdk.State n KemSK ProviderState :=
  (RegistrationNativeProviderAcceptFields.restore roots before.1, before.2)

/-- The literal actual reference agreement restores the complete extracted native agreement under the identical arbitrary total provider. -/
theorem agreement_native (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK ProviderState) :
    Prod.map (RegistrationServerReferenceSourceClient.restore
      (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar))
      (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar) memo) <$>
        (close (localImpl setup wire route sign seed scalar provider selected)
          (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before =
      Prod.map id (nativeProject memo) <$>
        (RegistrationNativeProviderAcceptSdk.agree setup checks wire route sign seed scalar provider selected authenticated).run
          (restore (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar) before) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar
  have prepared := congrArg (fun distribution => Prod.map
      (RegistrationServerReferenceSourceClient.restore roots)
      (fun current : State n KemSK ProviderState => (RegistrationNativeProviderAcceptFields.restore roots current.1, current.2)) <$> distribution)
    (RegistrationNativeProviderAcceptStage.agreement_project setup checks wire route sign seed scalar provider selected packet authenticated memo before)
  have native := congrArg (fun distribution => (fun result => (result.1,
      (RegistrationNativeProviderAcceptFields.restore roots before.1, resetAux memo result.2))) <$> distribution)
    (RegistrationServerProviderReferenceStage.reference_native setup checks wire route sign seed scalar provider selected correct
      before.1.control packet authenticated before.2 ∅)
  calc
    _ = (fun result => (RegistrationServerReferenceSourceClient.restore roots result.1,
      (RegistrationNativeProviderAcceptFields.restore roots before.1, resetAux memo result.2))) <$>
        (RegistrationServerProviderReferenceStage.plainStage setup checks wire route sign seed scalar provider selected packet authenticated).run before.2 := by
      simpa only [Functor.map_map, Prod.map_def, id_eq, project, RegistrationNativeProviderAcceptStage.reset] using prepared
    _ = _ := by
      simpa only [Functor.map_map, Prod.map_def, id_eq, RegistrationNativeProviderAcceptSdk.agree,
        nativeProject, restore, RegistrationNativeProviderAcceptFields.restore, StateT.run] using native

end BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAgreement.agreement_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAgreement.agreement_native
