-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner
import BeaconcryptCore.Computational.RegistrationAgreementNestedState
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives
/-! The actual ordinary writer shares the persistent public platform state, while every private native hash uses the explicit backend. Failed reservations retain full private primitive counters and cache. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryPrimitives
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork)
variable {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}

noncomputable def primitives (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl RawCtxMixedOwner.NativeSpec (M Primitive Platform)
  | .inr (.inr (.inr (.inr frame))) => fun before previous =>
      (fun result => ((result.1, RegistrationNativePlatformOrdinaryWorld.chargeWriter before), result.2)) <$>
        simulateQ RegistrationNativePlatformCtxBackend.coin
          ((RegistrationNativePlatformOrdinaryWriter.write reserve frame).run previous)
  | query => privateWork (RegistrationNativePlatformCtxPrimitives.program setup codec query)

def realize (before : Full Primitive Platform) : Primitive × Platform :=
  ((before.1.1.1, before.2.1), before.1.2)

private theorem source_private (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : Full Primitive Platform) :
    Prod.map id realize <$> (interpret (privateWork (RegistrationNativePlatformCtxPrimitives.program setup codec query) :
      M Primitive Platform _)).run before =
      (fun result => (result.1, (result.2, before.1.2))) <$>
        (PqxdhRecordLiftWorld.primitives setup codec query).run (before.1.1.1, before.2.1) := by
  rw [RegistrationNativePlatformCtxRunner.private_run]
  have source := RegistrationNativePlatformCtxPrimitives.query setup codec query (before.1.1, before.2)
  have mapped := congrArg (fun action => (fun result => (result.1, (result.2, before.1.2))) <$> action) source
  simpa only [RegistrationNativePlatformCtxPrimitives.implementation, StateT.run, Functor.map_map, realize,
    RegistrationNativePlatformCtxPrimitives.realize, Prod.map_def, id_eq] using mapped

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

/-- Actual ordinary primitive calls preserve the complete common platform state and all native cache/counter coordinates under physical interpretation. -/
theorem query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (request : RawCtxMixedOwner.NativeSpec.Domain) (before : Full Primitive Platform) :
    Prod.map id realize <$> (interpret (primitives setup codec reserve request)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve request).run
          (realize before).1).run (realize before).2 := by
  rcases request with request | input | opening | bytes | frame
  · simpa only [primitives, RegistrationNativePlatformOrdinaryWorld.primitives, StateT.run, state_lift_apply,
      bind_pure_comp, Functor.map_map, realize] using source_private setup codec (.inl request) before
  · simpa only [primitives, RegistrationNativePlatformOrdinaryWorld.primitives, StateT.run, state_lift_apply,
      bind_pure_comp, Functor.map_map, realize] using source_private setup codec (.inr (.inl input)) before
  · simpa only [primitives, RegistrationNativePlatformOrdinaryWorld.primitives, StateT.run, state_lift_apply,
      bind_pure_comp, Functor.map_map, realize] using source_private setup codec (.inr (.inr (.inl opening))) before
  · simpa only [primitives, RegistrationNativePlatformOrdinaryWorld.primitives, StateT.run, state_lift_apply,
      bind_pure_comp, Functor.map_map, realize] using source_private setup codec (.inr (.inr (.inr (.inl bytes)))) before
  · rw [RegistrationNativePlatformOrdinaryWorld.writer_joint]
    unfold primitives RegistrationNativePlatformCtxRunner.interpret
    simp only [StateT.run, simulateQ_map, RegistrationNativePlatformCtxBackend.coins,
      state_map_apply, state_lift_apply, bind_pure_comp, Functor.map_map,
      realize,
      RegistrationNativePlatformOrdinaryWorld.chargeWriter, Prod.map_def, id_eq]

theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : OracleComp RawCtxMixedOwner.NativeSpec A) (before : Full Primitive Platform) :
    Prod.map id realize <$> (interpret (simulateQ (primitives setup codec reserve) work)).run before =
      (RegistrationAgreementNestedState.flatten
        (simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve) work)).run (realize before) := by
  rw [RegistrationNativePlatformCtxRunner.simulate]
  have same := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun request => interpret (primitives setup codec reserve request))
    (RegistrationAgreementNestedState.implementation (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve))
    realize (query setup codec reserve) work before
  rw [RegistrationAgreementNestedState.program] at same
  exact same
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryPrimitives

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryPrimitives.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryPrimitives.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryPrimitives.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryPrimitives.complete
