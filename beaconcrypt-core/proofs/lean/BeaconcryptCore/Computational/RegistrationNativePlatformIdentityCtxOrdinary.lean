-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMain
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxContext
/-! Ordinary full-context work shares the indexed owner's physical CTX backend. Opaque owner state is retained and only auxiliary uniform transcript entries are normalized in the source projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityCtxMain (M Full interpret project)
variable {n : Nat} {KemSK Platform A Next : Type} {source : RegistrationNativeMldsa.Source}

def ordinary (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A) : M n KemSK Platform source A :=
  RegistrationNativePlatformIdentityCtxCompiler.ordinary (fun current =>
    simulateQ RegistrationNativePlatformIdentityCtxCompiler.backend (work.run current))

def attach (before : Full n KemSK Platform source) (result : A × (RegistrationNativeIdentityWorld.Context n KemSK × Platform)) :
    A × ((State n KemSK source × Platform) × PqxdhDynamicIdentityPool.SourceState) :=
  (result.1, (({before.1.1 with context := result.2.1}, result.2.2), RegistrationNativeIdentityCompiler.poolView before.2.1))

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The common physical interpreter retains every opaque owner and full context/P field for arbitrary ordinary source work. -/
theorem ordinary_source (joint : PqxdhJointIdentity.Primitives)
    (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A)
    (before : Full n KemSK Platform source) :
    Prod.map id project <$> (interpret joint (ordinary work)).run before =
      attach before <$> (Prod.map id RegistrationNativePlatformCtxContext.realize <$>
        (RegistrationNativePlatformCtxContext.interpret work).run ((before.1.1.context, before.1.2), before.2.2)) := by
  have same := congrArg (fun distribution => (fun (result : (A × (RegistrationNativeIdentityWorld.Context n KemSK × Platform)) × RegistrationNativePlatformIdentityCtxSource.State) =>
    (result.1.1, (({before.1.1 with context := RegistrationNativePlatformIdentityCtxAmbient.replace result.2.2.1 result.1.2.1}, result.1.2.2), result.2.1))) <$> distribution)
    (RegistrationNativePlatformIdentityCtxSource.backend_source joint (work.run (before.1.1.context, before.1.2)) before.2)
  simpa only [interpret, ordinary, RegistrationNativePlatformIdentityCtxCompiler.ordinary, StateT.run,
    simulateQ_map, state_map_apply, Functor.map_map, Prod.map_def, id_eq, project,
    RegistrationNativePlatformIdentityCtxSource.normalize, RegistrationNativePlatformCtxContext.interpret,
    RegistrationNativePlatformCtxContext.realize, attach] using same

/-- All actual ordinary routes and failures use the same private CTX and joint-Ed source, without revealing the generated identity rows. -/
theorem guarded_source {I Reader Response E : Type} {base : OracleSpec I}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (before : Full n KemSK Platform source) :
    Prod.map id project <$> (interpret setup.joint (ordinary (RegistrationNativePlatformCtxContext.guarded setup codec reserve route query))).run before =
      attach before <$> (RegistrationNativePlatformCtxContext.nativeWorld
        (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route query)).run
          (RegistrationNativePlatformCtxContext.realize ((before.1.1.context, before.1.2), before.2.2)) := by
  rw [ordinary_source, RegistrationNativePlatformCtxContext.guarded_source]

/-- Pure continuation results retain every physical and local source coordinate. -/
theorem interpret_pure (joint : PqxdhJointIdentity.Primitives) (value : A) :
    interpret joint (pure value : M n KemSK Platform source A) = pure value := by
  funext before
  simp only [interpret, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

/-- One shared source interpreter threads arbitrary adaptive Main continuations. -/
theorem interpret_bind (joint : PqxdhJointIdentity.Primitives) (work : M n KemSK Platform source A)
    (next : A → M n KemSK Platform source Next) :
    interpret joint (work >>= next) = (interpret joint work >>= fun value => interpret joint (next value)) := by
  funext before
  simp only [interpret, StateT.run, StateT.monad_bind_def, StateT.bind, simulateQ_bind, map_bind, bind_map_left]

def report (packet : beaconcrypt_core.registration.InitPacket) : M n KemSK Platform source Unit := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$>
    simulateQ RegistrationNativePlatformIdentityCtxCompiler.protocol ((RegistrationNativeIdentityMain.report packet).run before.1)

/-- Reporting all current public aliases is a source ghost operation before authentication, with the physical hash state and full platform state retained. -/
theorem report_source (joint : PqxdhJointIdentity.Primitives) (packet : beaconcrypt_core.registration.InitPacket)
    (before : Full n KemSK Platform source) :
    (interpret joint (report packet)).run before = pure ((), before) := by
  have protocol := RegistrationNativePlatformIdentityCtxSource.protocol_source joint
    ((RegistrationNativeIdentityMain.report packet).run before.1.1) before.2
  simp only [StateT.run] at protocol
  have previous := RegistrationNativeIdentityMainOrdinary.report_source joint packet (before.1.1, before.2.1)
  have same := congrArg (fun distribution => (fun result =>
    (result.1, ((result.2.1, before.1.2), (result.2.2, before.2.2)))) <$> distribution) previous
  simp only [interpret, report, StateT.run, simulateQ_map, state_map_apply, Functor.map_map]
  rw [protocol]
  simpa only [RegistrationNativeIdentityMainSource.interpret, StateT.run, map_pure, Functor.map_map, Prod.map_def, id_eq] using same
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary.ordinary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary.ordinary_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary.guarded_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary.guarded_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary.report_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary.report_source
