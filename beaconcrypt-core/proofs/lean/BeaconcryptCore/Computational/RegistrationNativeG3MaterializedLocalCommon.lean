-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalKeys
import BeaconcryptCore.Computational.RegistrationNativeG3LocalEffects

/-! The actual fixed-material publication and environment callbacks use the literal complete private receipt/World frame. The finite Common interpretation has their exact source after the named accounting projection on input and output. Actual guarded record callbacks are outside this Common interface. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalCommon
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot EnvEffects)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3MaterializedState (Core View view restore)
open RegistrationNativeG3LocalMaterialCompletion (fixed)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

def project (before : View n KemSK ProviderState) : View n KemSK ProviderState :=
  (before.1, (before.2.1, RegistrationNativeG3MetricWorld.mask before.2.2))

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    StateT.lift work before = (fun reply => (reply, before)) <$> work := by
  simp only [StateT.lift, bind_pure_comp]

private theorem publication_apply (query : RegistrationBoundPublication.Spec.Domain)
    (before : RegistrationNativeG3Common.State n) :
    (PqxdhRecordLiftWorld.effects.mapStateTBase
      (RegistrationBoundSourceCompiler.compiler setup.source wire.frameWrite sign)).flattenStateT query before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          ((RegistrationBoundSourceCompiler.compiler setup.source wire.frameWrite sign query).run before.1)).run before.2 := rfl

/-- The current private publication receipt log and complete World have the exact actual source under the receipt-separating view. -/
theorem publication (query : RegistrationBoundPublication.Spec.Domain) (before : View n KemSK ProviderState) :
    Prod.map id project <$>
      (RegistrationNativeG3MaterializedFrontend.common
        (RegistrationNativeG3Common.handler setup.source wire.frameWrite sign) (.inl query)).run before =
      Prod.map id view <$>
        (fixed table setup codec route wire sign seed scalar candidate provider
          (.inl (.inr (.inl (.inr (.inl query)))))).run (restore (project before)) := by
  rw [RegistrationNativeG3LocalMaterialFixed.fixed_ordinary table setup codec route wire sign seed scalar candidate provider _ (by trivial)]
  have source := RegistrationNativeG3LocalEffects.program_source setup codec route
    ((RegistrationBoundSourceCompiler.compiler setup.source wire.frameWrite sign query).run before.2.1) before.2.2
  simp only [RegistrationNativeG3MaterializedFrontend.common, RegistrationNativeG3Common.handler,
    RegistrationNativeG3Common.publication, publication_apply,
    RegistrationNativeG3LocalKeys.actual, RegistrationNativeG3LocalKeys.execute,
    RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.publication,
    StateT.run, state_map_apply, simulateQ_map, Functor.map_map, Prod.map_def, id_eq,
    project, view, restore]
  have mapped := congrArg
    (fun distribution => (fun result => (result.1.1, before.1, result.1.2, result.2)) <$> distribution) source
  simp only [Functor.map_map, Prod.map_def, id_eq, StateT.run] at mapped
  convert mapped using 1 <;> rfl

/-- Every actual environment callback has the same complete private receipt/World source; administrative installation checks remain the actual World checks. -/
theorem effect (query : (EnvEffects n).Domain) (before : View n KemSK ProviderState) :
    Prod.map id project <$>
      (RegistrationNativeG3MaterializedFrontend.common
        (RegistrationNativeG3Common.handler setup.source wire.frameWrite sign) (.inr query)).run before =
      Prod.map id view <$>
        (fixed table setup codec route wire sign seed scalar candidate provider
          (.inl (.inr (.inl (.inr (.inr query)))))).run (restore (project before)) := by
  rw [RegistrationNativeG3LocalMaterialFixed.fixed_ordinary table setup codec route wire sign seed scalar candidate provider _ (by trivial)]
  simp only [RegistrationNativeG3MaterializedFrontend.common, RegistrationNativeG3Common.handler,
    RegistrationNativeG3Common.effect, RegistrationNativeG3LocalKeys.actual, RegistrationNativeG3LocalKeys.execute,
    RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect,
    StateT.run, state_map_apply, lift_apply, simulateQ_map, Functor.map_map, Prod.map_def, id_eq,
    project, view, restore]
  have raw := RegistrationNativeG3LocalEffects.program_source setup codec route
    ((EnvEffects n).query query : OracleComp (EnvEffects n) _) before.2.2
  simp only [simulateQ_spec_query] at raw
  have mapped := congrArg
    (fun distribution => (fun result => (result.1, before.1, before.2.1, result.2)) <$> distribution) raw
  simp only [Functor.map_map, Prod.map_def, id_eq, StateT.run] at mapped
  convert mapped using 1 <;> rfl
end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalCommon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalCommon.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalCommon.publication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalCommon.effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalCommon.effect
