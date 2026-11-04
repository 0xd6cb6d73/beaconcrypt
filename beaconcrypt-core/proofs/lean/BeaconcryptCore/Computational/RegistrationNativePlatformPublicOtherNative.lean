-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOrdinaryLens
/-! Uniform and public hash callbacks use the same actual private World on the new shared platform execution. External P is untouched by these native draws, and only the named instrumentation view is compared. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicOtherNative
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePublicSourceState (restore project nativeView)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem effect_tree (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    (RegistrationNativePlatformPublicFrontend.executeLocal
      (StateT.lift (RegistrationNativePlatformPublicFrontend.effect query)) :
        RegistrationNativePlatformPublicFrontend.M n KemSK Platform source _) =
      RegistrationNativePlatformPublicSourceOrdinaryLens.oldProgram (StateT.lift (RegistrationNativePublicFrontend.effect query)) := by
  funext before
  simp only [RegistrationNativePlatformPublicFrontend.executeLocal,
    RegistrationNativePlatformPublicSourceOrdinaryLens.oldProgram, StateT.run_lift, bind_pure_comp,
    simulateQ_map, RegistrationNativePlatformPublicFrontend.effect, RegistrationNativePlatformPublicFrontend.localQuery,
    RegistrationNativePlatformPublicFrontend.embedLocal, RegistrationNativePublicFrontend.effect,
    RegistrationNativePublicFrontend.liftLocal, RegistrationNativePlatformPublicFrontend.old, simulateQ_spec_query,
    Functor.map_map]

/-- Native uniform/hash effects retain the same complete reached World and P in the final runtime source interpretation. -/
theorem effect (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : State n KemSK Platform source) :
    (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (execute setup wire route sign seed scalar (RegistrationNativePlatformPublicFrontend.executeLocal
        (StateT.lift (RegistrationNativePlatformPublicFrontend.effect query)))).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
          (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.effects query))).run
            (restore roots scalar before.1.1 before.2)).run before.1.2 := by
  rw [effect_tree, RegistrationNativePlatformPublicSourceOrdinaryLens.old_source]
  have actual := RegistrationNativePublicSourceWorld.effect_source setup wire route sign seed scalar roots query (before.1.1, before.2)
  have mapped := congrArg (fun action => (fun result => ((result.1, result.2), before.1.2)) <$> action) actual
  simp only [Functor.map_map, Prod.map_def, id_eq] at mapped ⊢
  change _ = (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
    (simulateQ RegistrationNativePlatformMldsaProgram.coins
      ((RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.effects query)).run
        (restore roots scalar before.1.1 before.2))).run before.1.2
  rw [RegistrationNativePlatformMldsaProgram.lift_coins, StateT.run_lift]
  simpa only [bind_pure_comp, Functor.map_map] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicOtherNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOtherNative.effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOtherNative.effect
