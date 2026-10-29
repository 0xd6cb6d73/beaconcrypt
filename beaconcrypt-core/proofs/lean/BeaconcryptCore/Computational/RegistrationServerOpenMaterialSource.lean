-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenMaterialInterface

/-! The complete actual open Server build closes through its current-Env material lens to the native SDK build source. The private generated-key pool and other services are outside the local projection, and the whole native/coin/log instrumentation view remains explicit at the SDK boundary. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerOpenMaterialSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationServerOpenMaterialInterface (callbacks)
variable {n : Nat} {ι KemSK Extra Value Index : Type} {base : OracleSpec ι} {spec : OracleSpec Index}

private theorem lower_run (setup : Setup base KemSK) (services : Callbacks n KemSK Extra)
    (work : StateT Environment (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)) Value)
    (before : Environment × Private n KemSK Extra) :
    (RegistrationNativeKemReferencePrefix.lower setup services work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (implementation setup services) (work.run before.1)).run before.2 := rfl

private theorem lower_program (setup : Setup base KemSK) (services : Callbacks n KemSK Extra)
    (interpreter : QueryImpl spec (StateT Environment (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK))))
    (work : OracleComp spec Value) :
    RegistrationNativeKemReferencePrefix.lower setup services (simulateQ interpreter work) =
      simulateQ (fun query => RegistrationNativeKemReferencePrefix.lower setup services (interpreter query)) work := by
  have same : (fun query => RegistrationNativeKemReferencePrefix.lower setup services (interpreter query)) =
      ((implementation setup services).mapStateTBase interpreter).flattenStateT := rfl
  rw [same]
  funext before
  change (RegistrationNativeKemReferencePrefix.lower setup services (simulateQ interpreter work)).run before =
    (simulateQ ((implementation setup services).mapStateTBase interpreter).flattenStateT work).run before
  rw [lower_run, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  change id <$> (simulateQ ((implementation setup services).mapStateTBase interpreter).flattenStateT work).run before = _
  exact id_map _

/-- Arbitrary adaptive service components preserve the entire actual current environment and World. -/
theorem program (setup : Setup base KemSK) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (services : Callbacks n KemSK Extra)
    (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value)
    (before : Environment × Private n KemSK Extra) :
    Prod.map id RegistrationServerOpenMaterialInterface.project <$>
      (RegistrationNativeKemReferencePrefix.lower setup (callbacks setup.source roots services)
        (simulateQ (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
          RegistrationServerOpenReferenceCompiler.demand setup.source writer sign) work)).run before =
      (simulateQ (RegistrationServerMaterialSourceState.service setup.source writer sign roots) work).run
        (RegistrationServerOpenMaterialInterface.project before) := by
  rw [lower_program]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ RegistrationServerOpenMaterialInterface.project
    (RegistrationServerOpenMaterialInterface.query setup writer sign roots services) work before

abbrev State (n : Nat) (KemSK Extra : Type) :=
  RegistrationServerMaterialFrontend.State × (Environment × Private n KemSK Extra)

def project (before : State n KemSK Extra) : RegistrationServerMaterialSourceState.State n :=
  (before.1, RegistrationServerOpenMaterialInterface.project before.2)

noncomputable def close (setup : Setup base KemSK)
    (roots : RegistrationServerReferenceRestore.Roots) (services : Callbacks n KemSK Extra)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value) : StateT (State n KemSK Extra) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RegistrationNativeKemReferencePrefix.lower setup (callbacks setup.source roots services) (work.run before.1)).run before.2

/-- The actual open build executes exactly the whole current-Env material service rather than a disconnected source specialization. -/
theorem build (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (services : Callbacks n KemSK Extra)
    (handle : Nat) (application : Option (Slice U8)) (before : State n KemSK Extra) :
    Prod.map id project <$>
      (close setup roots services (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run before =
      (RegistrationServerMaterialSourceState.close setup.source wire.frameWrite sign roots
        (RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application)).run (project before) := by
  have lowered := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution)
    (program setup wire.frameWrite sign roots services
      ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before.1) before.2)
  simp only [close, RegistrationServerOpenReferenceCompiler.build, RegistrationServerMaterialSourceState.close,
    StateT.run, Functor.map_map, Prod.map_def, id_eq, project] at lowered ⊢
  exact lowered

/-- Complete real source restoration yields the actual SDK build, including cancellation, native gates, both KDFs, signing, dynamic encoding, installation and final commit. -/
theorem native (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (services : Callbacks n KemSK Extra)
    (handle : Nat) (application : Option (Slice U8)) (before : State n KemSK Extra) :
    Prod.map id (fun current => RegistrationServerMaterialSourceState.project roots (project current)) <$>
      (close setup roots services (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run before =
      Prod.map id RegistrationServerMaterialSourceState.nativeView <$>
        (RegistrationServerSdkSource.build setup (RegistrationNativeWire.ledgerCodec wire) checks sign wire.encodeResponse
          handle application).run (RegistrationServerMaterialSourceState.restore roots (project before)) := by
  have source := congrArg (fun distribution => Prod.map id (RegistrationServerMaterialSourceState.project roots) <$> distribution)
    (build setup checks wire sign roots services handle application before)
  rw [RegistrationServerMaterialBuildSource.native setup checks wire sign roots handle application (project before)] at source
  simp only [Functor.map_map, Prod.map_def, id_eq] at source ⊢
  exact source

end BeaconcryptCore.Computational.RegistrationServerOpenMaterialSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenMaterialSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenMaterialSource.program
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenMaterialSource.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenMaterialSource.build
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenMaterialSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenMaterialSource.native
