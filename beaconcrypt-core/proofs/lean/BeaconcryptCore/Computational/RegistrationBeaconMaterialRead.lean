-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconChargedNative
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner
/-! A local environment interpreter retains the same chronological record markers while leaving the selected owner outside the primitive dispatcher. Its stateful World effects and exact functional source replies are the real native record callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconMaterialRead
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {Auxiliary : Type} {m : Type → Type} [Monad m]

def charge (kind : RegistrationWorldAgreement.RecordCall) : StateT (EnvState Auxiliary) m Unit :=
  modify fun env => {env with recordRequests := env.recordRequests ++ [kind]}

noncomputable def read (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RegistrationRawReceiveBridge.Spec (StateT (EnvState Auxiliary) m) := fun query => do
  let _ ← charge (RegistrationBeaconChargedNative.kind query)
  StateT.lift (simulateQ environment (RegistrationBeaconRecordSourceProgram.read source writer query))

variable [LawfulMonad m]
private theorem lift_pure {Value : Type} (value : Value) :
    (StateT.lift (pure value) : StateT (EnvState Auxiliary) m Value) = pure value := by
  apply StateT.ext
  intro env
  simp only [StateT.run_lift, pure_bind, StateT.run_pure]

theorem initial (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (request : InitialRatchetKdfRequest) :
    read (Auxiliary := Auxiliary) environment source writer (.inl (.initialKdf request)) =
      charge .initialKdf *> pure (.Some (RawCtxSourceHkdf.initialResponse source.crypto request)) := by
  simp only [read, RegistrationBeaconChargedNative.kind, RegistrationWorldAgreement.recordCall,
    RegistrationBeaconRecordSourceProgram.initial_source, simulateQ_pure, lift_pure]
  rfl

theorem ratchet (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (request : SymmetricRatchetKdfRequest) :
    RegistrationBeaconChargedSource.primitive (read (Auxiliary := Auxiliary) environment source writer) (.inl request) =
      charge .ratchetKdf *> pure (RawCtxSourceHkdf.response source.crypto request) := by
  have fixed : RegistrationBeaconRecordSourceProgram.read (n := n) source writer (.inr (.inl request)) =
      pure (RawCtxSourceHkdf.response source.crypto request) := rfl
  simp only [RegistrationBeaconChargedSource.primitive, QueryImpl.apply_compose,
    RawCtxSourceOpen.nativeAdapter, simulateQ_spec_query, RegistrationRawReceiveBridge.modelAdapter,
    read, RegistrationBeaconChargedNative.kind, fixed, simulateQ_pure, lift_pure]
  rfl

theorem map_read (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    environment.mapStateTBase (read (Auxiliary := Auxiliary) (QueryImpl.ofLift (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp (PqxdhRecordLiftInterface.EnvEffects n))) source writer) =
      read environment source writer := by
  funext query
  apply StateT.ext
  intro env
  simp only [QueryImpl.mapStateTBase, read, charge, StateT.run_bind, StateT.run_modify,
    pure_bind, StateT.run_lift, simulateQ_bind, simulateQ_pure, simulateQ_ofLift_eq_self]
  rfl

theorem program (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {Value : Type} (work : OracleComp RegistrationRawReceiveBridge.Spec Value) (env : EnvState Auxiliary) :
    simulateQ environment ((simulateQ (read (QueryImpl.ofLift (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp (PqxdhRecordLiftInterface.EnvEffects n))) source writer) work).run env) =
      (simulateQ (read environment source writer) work).run env := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, map_read]

theorem primitive_program (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {Value : Type} (work : OracleComp RawCtxWholeOwner.PrimitiveSpec Value) (env : EnvState Auxiliary) :
    simulateQ environment ((simulateQ (RegistrationBeaconChargedSource.primitive
      (read (QueryImpl.ofLift (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp (PqxdhRecordLiftInterface.EnvEffects n))) source writer)) work).run env) =
      (simulateQ (RegistrationBeaconChargedSource.primitive (read environment source writer)) work).run env := by
  simp only [RegistrationBeaconChargedSource.primitive, QueryImpl.simulateQ_compose]
  exact program environment source writer _ env

variable {ι KemSK : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}
theorem native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) :
    RegistrationBeaconReferenceNativeOwner.record (n := n) (mlSource := mlSource) (Auxiliary := Auxiliary) setup wire query =
      simulateQ (read RegistrationBeaconReferenceNativeRecord.environment setup.source wire.frameWrite)
        (RegistrationRawReceiveBridge.nativeAdapter query) := by
  apply StateT.ext
  intro env
  cases query <;> first | rfl | (rename_i writing; cases writing <;> rfl)

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.initial
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.ratchet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.ratchet
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.map_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.map_read

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.primitive_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconMaterialRead.primitive_program

end BeaconcryptCore.Computational.RegistrationBeaconMaterialRead
