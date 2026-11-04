-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner
import BeaconcryptCore.Computational.RegistrationAgreementNestedState
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! OPEN Server environment callbacks expose actual CTX addresses before lookup. Physical interpretation restores that one shared cache into the same private World, keeping its pool, Extra state, public platform state and complete native counters. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxEffects
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork)
open RegistrationNativePlatformCtxBackend (Spec)
variable {n : Nat} {KemSK Extra Platform A : Type}

def replace (cache : CtxRomAuth.CtxRO.QueryCache) (before : Private n KemSK Extra) : Private n KemSK Extra :=
  { before with world := RegistrationNativePlatformCtxCacheFrame.replace cache before.world }

def realize (before : Full (Private n KemSK Extra) Platform) : Private n KemSK Extra × Platform :=
  (replace before.2.1 before.1.1, before.1.2)

noncomputable def effect (query : (EnvEffects n).Domain) : M (Private n KemSK Extra) Platform ((EnvEffects n).Range query) :=
  privateWork (RegistrationNativePlatformServerOpenEffects.withWorld (RegistrationNativePlatformCtxEffects.program query))

noncomputable def native (query : (EnvEffects n).Domain) : StateT (Private n KemSK Extra × Platform) ProbComp ((EnvEffects n).Range query) :=
  RegistrationAgreementNestedState.flatten (RegistrationNativePlatformInterpret.state RegistrationNativePlatformMldsaProgram.coins
    (RegistrationNativeKemReferenceWorld.effect query))

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

theorem query (request : (EnvEffects n).Domain) (before : Full (Private n KemSK Extra) Platform) :
    Prod.map id realize <$> (interpret (effect request)).run before =
      (native request).run (realize before) := by
  unfold effect
  rw [RegistrationNativePlatformCtxRunner.private_run]
  have source := RegistrationNativePlatformCtxEffects.query request (before.1.1.world, before.2)
  have mapped := congrArg (fun action => (fun result => (result.1,
    ({ (realize before).1 with world := result.2 }, before.1.2))) <$> action) source
  simpa only [RegistrationNativePlatformServerOpenEffects.withWorld,
    RegistrationNativePlatformCtxEffects.implementation, native, RegistrationAgreementNestedState.flatten,
    RegistrationNativePlatformInterpret.state, RegistrationNativePlatformMldsaProgram.lift_coins,
    RegistrationNativeKemReferenceWorld.effect, RegistrationNativeKemReferenceWorld.withWorld,
    StateT.run, simulateQ_map, state_map_apply, state_lift_apply, bind_pure_comp,
    Functor.map_map, realize, replace, RegistrationNativePlatformCtxEffects.realize,
    RegistrationNativePlatformCtxCacheFrame.replace, Prod.map_def, id_eq] using mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxEffects.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxEffects.query
