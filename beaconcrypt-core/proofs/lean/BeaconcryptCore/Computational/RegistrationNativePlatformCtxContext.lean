-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld
/-! The non-Beacon context lens runs the actual ordinary callbacks through the same physical hash backend. Full Server state, raw signing receipts, KEM pool and persistent platform state remain in the exact source marginal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxContext
open RegistrationNativeIdentityWorld (Context)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformCtxBackend (Spec)
variable {n : Nat} {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}
abbrev M (n : Nat) (KemSK Platform : Type) := StateT (Context n KemSK × Platform) (OracleComp Spec)
abbrev Full (n : Nat) (KemSK Platform : Type) := (Context n KemSK × Platform) × RegistrationNativePlatformCtxBackend.State

def realize (before : Full n KemSK Platform) : Context n KemSK × Platform :=
  (RegistrationNativePlatformIdentityCtxAmbient.replace before.2.1 before.1.1, before.1.2)

noncomputable def interpret (work : M n KemSK Platform A) : StateT (Full n KemSK Platform) ProbComp A := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ RegistrationNativePlatformCtxBackend.implementation (work.run before.1)).run before.2

def attach (before : Context n KemSK) (after : PqxdhRecordLiftWorld.State n) : Context n KemSK :=
  {before with server := {before.server with world := {before.server.world with world := (after, before.server.world.world.2)}}}

def world (work : RegistrationNativePlatformCtxRunner.M (PqxdhRecordLiftWorld.State n) Platform A) : M n KemSK Platform A := fun before =>
  (fun result => (result.1.1, (attach before.1 result.1.2, result.2))) <$>
    (work.run before.1.server.world.world.1).run before.2

def nativeWorld (work : RegistrationNativePlatformOrdinaryWorld.M n Platform A) : StateT (Context n KemSK × Platform) ProbComp A := fun before =>
  (fun result => (result.1.1, (attach before.1 result.1.2, result.2))) <$>
    (work.run before.1.server.world.world.1).run before.2

noncomputable def guarded (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (M n KemSK Platform) :=
  fun query => world (RegistrationNativePlatformCtxOrdinaryWorld.guarded setup codec reserve route query)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Every actual ordinary callback retains the exact complete Context, private pool, source counters and common platform state. -/
theorem guarded_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (guarded setup codec reserve route query)).run before =
      (nativeWorld (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route query)).run (realize before) := by
  have same := congrArg (fun distribution => (fun result =>
    (result.1, (attach (realize before).1 result.2.1, result.2.2))) <$> distribution)
    (RegistrationNativePlatformCtxOrdinaryWorld.guarded_source setup codec reserve route query
      ((before.1.1.server.world.world.1, before.1.2), before.2))
  simpa only [interpret, guarded, world, nativeWorld, RegistrationNativePlatformCtxRunner.interpret,
    RegistrationAgreementNestedState.flatten, StateT.run, simulateQ_map, state_map_apply,
    Functor.map_map, realize, attach, RegistrationNativePlatformIdentityCtxAmbient.replace,
    RegistrationNativePlatformCtxOrdinaryWorld.realize, RegistrationNativePlatformCtxCacheFrame.replace,
    Prod.map_def, id_eq] using same

/-- Arbitrary later ordinary callbacks share one backend and preserve the same complete reached context, including all refused paths. -/
theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) A)
    (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (simulateQ (guarded setup codec reserve route) work)).run before =
      (simulateQ (fun query => nativeWorld (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route query)) work).run (realize before) := by
  have linked : (fun (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain) => interpret (guarded (KemSK := KemSK) setup codec reserve route query)) =
      QueryImpl.Stateful.link (guarded setup codec reserve route) RegistrationNativePlatformCtxBackend.implementation := by
    funext query current
    rfl
  have run_program : (interpret (simulateQ (guarded setup codec reserve route) work)).run before =
      (simulateQ (fun query => interpret (guarded setup codec reserve route query)) work).run before := by
    rw [linked, QueryImpl.Stateful.simulateQ_link_run]
    rfl
  rw [run_program]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ realize (guarded_source setup codec reserve route) work before
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxContext

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxContext.guarded_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxContext.guarded_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxContext.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxContext.complete
