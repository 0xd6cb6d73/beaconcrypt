-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal
import BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld
/-! Unchanged ordinary World computations and public platform work occupy separate source coordinates. These leaf/program lenses preserve the complete private state and actual external poststate; they do not identify registration handlers or initialized profiles. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOrdinaryLens
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePublicSourceEffects (Private close toPrivate fromPrivate)
variable {n : Nat} {I KemSK Platform A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def oldProgram (work : StateT (RegistrationNativePublicFrontend.State source)
    (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) A) :
    RegistrationNativePlatformPublicFrontend.M n KemSK Platform source A := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$>
    simulateQ RegistrationNativePlatformPublicFrontend.old (work.run before.1)

def publicWork (work : StateT Platform ProbComp A) : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source A :=
  RegistrationNativePlatformPublicFrontend.executeLocal (fun before =>
    (fun result => (result.1, (before.1, result.2))) <$>
      ((RegistrationNativePlatformPublicFrontend.platform (n := n) (KemSK := KemSK) work).run before.2))

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

private theorem old_tree (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A) :
    simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign)
      (simulateQ RegistrationNativePlatformPublicFrontend.old work) =
      simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, RegistrationNativePlatformPublicFrontend.old, simulateQ_spec_query,
    RegistrationNativePlatformPublicSourceExecution.handler]

/-- Embedding any unchanged ordinary primitive program keeps its complete private source execution and leaves P literal. -/
theorem old_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : StateT (RegistrationNativePublicFrontend.State source)
      (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) A)
    (before : State n KemSK Platform source) :
    (execute setup wire route sign seed scalar (oldProgram work)).run before =
      (fun result => (result.1, ((result.2.1, before.1.2), result.2.2))) <$>
        (RegistrationNativePublicSourceExecution.execute setup wire route sign seed scalar work).run (before.1.1, before.2) := by
  simp only [execute, oldProgram, StateT.run, simulateQ_map, old_tree,
    close, RegistrationNativePublicSourceExecution.execute, map_apply, Functor.map_map]
  rfl

/-- A public platform action retains the whole native/private source frame on every reached outcome. -/
theorem public_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : StateT Platform ProbComp A) (before : State n KemSK Platform source) :
    (execute setup wire route sign seed scalar (publicWork work)).run before =
      (fun result => (result.1, ((before.1.1, result.2), before.2))) <$> work.run before.1.2 := by
  have actual := congrArg (fun computation => (computation.run (toPrivate before.2)).run before.1.2)
    (RegistrationNativePlatformPublicSourceLocal.interpret_platform setup wire route sign seed scalar work)
  simp only [RegistrationNativePlatformPublicSourceLocal.interpret, StateT.run] at actual
  have mapped := congrArg (fun action => (fun result =>
      (result.1.1, ((before.1.1, result.2), fromPrivate result.1.2))) <$> action) actual
  convert mapped using 1 <;> simp only [execute, publicWork, RegistrationNativePlatformPublicFrontend.executeLocal,
    close, StateT.run, lift_apply, bind_pure_comp, map_apply, simulateQ_map,
    Functor.map_map, fromPrivate, toPrivate, Prod.map_def, id_eq]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOrdinaryLens

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOrdinaryLens.old_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOrdinaryLens.old_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOrdinaryLens.public_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOrdinaryLens.public_source
