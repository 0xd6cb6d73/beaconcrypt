-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual ordinary environment callbacks run on the reached private World and preserve the exact provider pool and extra state. This is an effect-by-effect interpretation law in the same common monad, not a secrecy condition on arbitrary platform dictionaries. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeKemReferenceWorld (Private)
variable {n : Nat} {ι KemSK Extra Value : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def withWorld (work : StateT (PqxdhRecordLiftWorld.State n) m Value) : StateT (Private n KemSK Extra) m Value := fun before =>
  (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world

private theorem withWorld_pure (value : Value) :
    withWorld (pure value : StateT (PqxdhRecordLiftWorld.State n) m Value) =
      (pure value : StateT (Private n KemSK Extra) m Value) := by
  funext before
  simp only [withWorld, StateT.run_pure, map_pure]
  rfl

private theorem withWorld_bind {Next : Type} (work : StateT (PqxdhRecordLiftWorld.State n) m Value)
    (next : Value → StateT (PqxdhRecordLiftWorld.State n) m Next) :
    withWorld (work >>= next) =
      (withWorld work >>= fun value => withWorld (KemSK := KemSK) (Extra := Extra) (next value)) := by
  funext before
  simp only [withWorld, StateT.run, StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]

theorem source_withWorld (coins : QueryImpl unifSpec m) (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) :
    RegistrationNativePlatformInterpret.state coins (RegistrationNativeKemReferenceWorld.withWorld (KemSK := KemSK) (Extra := Extra) work) =
      withWorld (RegistrationNativePlatformInterpret.state coins work) := by
  funext before
  simp only [RegistrationNativePlatformInterpret.state, RegistrationNativeKemReferenceWorld.withWorld,
    StateT.run, withWorld, simulateQ_map]

theorem effect (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (callbacks : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra m)
    (query : (EnvEffects n).Domain) :
    RegistrationNativePlatformServerOpenControl.effects (RegistrationNativePlatformServerOpenKernel.handler coins setup callbacks) query =
      withWorld (RegistrationNativePlatformServerReferencePrefix.effects coins query) := by
  simp only [RegistrationNativePlatformServerOpenControl.effects, QueryImpl.compose,
    RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query,
    RegistrationNativePlatformServerOpenKernel.handler, RegistrationNativeKemReferenceWorld.effect]
  exact source_withWorld coins _

theorem world_program {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (StateT (PqxdhRecordLiftWorld.State n) m))
    (work : OracleComp spec Value) (before : Private n KemSK Extra) :
    (simulateQ (fun query => withWorld (implementation query)) work).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ implementation work).run before.world := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure output => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change ((withWorld (implementation query)).run before >>= fun result =>
      (simulateQ (fun query => withWorld (implementation query)) (next result.1)).run result.2) = _
    simp only [withWorld, StateT.run, bind_map_left, map_bind]
    apply bind_congr
    intro result
    exact ih result.1 { before with world := result.2 }

theorem program (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (callbacks : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra m)
    (work : OracleComp (EnvEffects n) Value) (before : Private n KemSK Extra) :
    (simulateQ (RegistrationNativePlatformServerOpenControl.effects
      (RegistrationNativePlatformServerOpenKernel.handler coins setup callbacks)) work).run before =
    (fun result => (result.1, { before with world := result.2 })) <$>
      (simulateQ (RegistrationNativePlatformServerReferencePrefix.effects coins) work).run before.world := by
  have handlers : RegistrationNativePlatformServerOpenControl.effects
      (RegistrationNativePlatformServerOpenKernel.handler coins setup callbacks) =
      fun query => withWorld (RegistrationNativePlatformServerReferencePrefix.effects coins query) :=
    funext (effect coins setup callbacks)
  rw [handlers]
  exact world_program _ work before

theorem hash (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (callbacks : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra m)
    (request : registration.HashRequest) :
    RegistrationNativePlatformServerReferenceAccept.hash
      (RegistrationNativePlatformServerOpenControl.effects (RegistrationNativePlatformServerOpenKernel.handler coins setup callbacks)) request =
    withWorld (RegistrationNativePlatformServerReferenceAccept.hash (RegistrationNativePlatformServerReferencePrefix.effects coins) request) := by
  unfold RegistrationNativePlatformServerReferenceAccept.hash
  rw [effect, withWorld_bind]
  simp only [withWorld_pure]

theorem pin (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (callbacks : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra m)
    (stored : session.ServerAuthenticationPin) :
    RegistrationNativePlatformServerReferenceAccept.pin
      (RegistrationNativePlatformServerOpenControl.effects (RegistrationNativePlatformServerOpenKernel.handler coins setup callbacks)) stored =
    withWorld (RegistrationNativePlatformServerReferenceAccept.pin (RegistrationNativePlatformServerReferencePrefix.effects coins) stored) := by
  unfold RegistrationNativePlatformServerReferenceAccept.pin
  have handlers : RegistrationNativePlatformServerReferenceAccept.hash
      (RegistrationNativePlatformServerOpenControl.effects (RegistrationNativePlatformServerOpenKernel.handler coins setup callbacks)) =
      fun request => withWorld (RegistrationNativePlatformServerReferenceAccept.hash (RegistrationNativePlatformServerReferencePrefix.effects coins) request) :=
    funext (hash coins setup callbacks)
  rw [handlers]
  funext before
  exact world_program _ _ before

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.source_withWorld' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.source_withWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.effect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.world_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.world_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects.pin
