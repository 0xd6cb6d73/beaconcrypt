-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerCommit
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage
/-! Source owner masking, exact public embedding and the derived trusted leaf lens compose before the current returned owner/environment/P state is committed. Concrete callbacks instantiate the syntactic equality and role restriction from their literal source bodies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerBody
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformSourceOwnerCommit (Output PublicOutput restoreOutput observe view commit)
open RegistrationNativePublicSourceState (restore project nativeView)
open RegistrationNativePlatformSourceOwnerJoint (Spec sourceHandler nativeHandler Allowed)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def returned (result : (((Value × RegistrationNativeBeaconFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × RegistrationNativeExperiment.State n KemSK source) × Platform) :=
  commit ((result.1.1, result.2), result.1.2)

/-- The real native owner/writer dictionary commits exactly its reached outputs after the joint-language reassociation. -/
theorem native_returned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (tree : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK)
      ((Value × RegistrationNativeBeaconFrontend.State source) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State))
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    (view ∘ commit) <$>
      (simulateQ (nativeHandler setup checks representation created source)
        ((simulateQ (RegistrationNativePlatformSourceOwnerLanguage.handler writer) tree).run previous)).run before =
      (view ∘ returned) <$>
        ((simulateQ (RegistrationNativePlatformExperiment.bundleHandler RegistrationNativePlatformMldsaProgram.coins
          setup checks representation created source writer) tree).run before).run previous := by
  have actual := congrArg (fun action => (view ∘ returned) <$> (action.run before).run previous)
    (RegistrationNativePlatformSourceOwnerLanguage.native_program setup checks representation created writer tree)
  simpa only [RegistrationNativePlatformSourceOwnerLanguage.native, StateT.run, Functor.map_map, Function.comp_def, returned] using actual

/-- The actual public owner wrapper's explicit source syntax composes with the same complete reached source state, before native representation is committed. -/
theorem raw_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (roots : Roots)
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) Value)
    (tree : OracleComp (Spec n KemSK) (Output source Platform Value))
    (before : RegistrationNativePlatformPublicSourceExecution.State n KemSK Platform source)
    (equation : restoreOutput scalar <$> (((work.run before.1.1.beacons).run before.1.1.environment).run before.1.2) =
      simulateQ RegistrationNativePlatformSourceOwnerEmbedding.embed tree)
    (allowed : tree.AllQueriesSatisfy (Allowed (KemSK := KemSK))) :
    (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (RegistrationNativePlatformPublicSourceExecution.execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon work))).run before =
      (view ∘ commit) <$>
        (simulateQ (nativeHandler setup checks representation created source) tree).run (restore roots scalar before.1.1 before.2) := by
  rw [RegistrationNativePlatformSourceOwnerCommit.layout, equation,
    RegistrationNativePlatformSourceOwnerEmbedding.program_source]
  exact RegistrationNativePlatformSourceOwnerCommit.program_source setup checks wire route representation created scalar credential roots tree allowed before.1.1 before.2
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerBody

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerBody.native_returned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerBody.native_returned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerBody.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerBody.raw_source
