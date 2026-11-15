-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHandlerCache

/-! The finite actual native protected-origin cover charges every earlier cache collision to the literal final shared cache. No cache-extension or event-coverage premise is assumed: both follow from actual native callbacks and the derived reached source invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyFinalCover
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaGhostFamily (State callback nativeState coordinateState)
open RegistrationNativeMldsaFamilyCover (Safe observe bad collision counter cost marked)
open RegistrationNativeMldsaEuf (Forgery)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n cap : Nat} {ι KemSK V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source)) (fallback : Credential source)

private theorem bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl

private theorem collision_flag (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK) (Fin cap) Forgery)
    (initial : Safe source credential fallback before.native)
    (already : before.collision = true → collision source before.native)
    (result : V × RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK) (Fin cap) Forgery)
    (supported : result ∈ support ((simulateQ (marked source setup checks wire route representation created credential) work).run before)) :
    Safe source credential fallback result.2.native ∧ (result.2.collision = true → collision source result.2.native) := by
  classical
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact ⟨initial, already⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_apply, marked, RegistrationNativeMldsaFiniteMonitor.handler,
        StateT.run, mem_support_bind_iff, support_map] at supported
      obtain ⟨middle, ⟨raw, reached, same⟩, continued⟩ := supported
      cases same
      have safeAfter := RegistrationNativeMldsaFamilyCover.step_safe source setup checks wire route representation created credential fallback
        query before.native raw initial reached
      have extended := RegistrationNativeHandlerCache.family source setup checks wire route representation created credential fallback
        query before.native initial raw reached
      apply ih raw.1 _ safeAfter _ continued
      intro active
      change before.collision || decide (collision source raw.2) = true at active
      rcases Bool.or_eq_true_iff.mp active with old | fresh
      · obtain ⟨first, second, left, right, distinct, firstAt, secondAt, equal⟩ := already old
        exact ⟨first, second, left, right, distinct, extended firstAt, extended secondAt, equal⟩
      · exact of_decide_eq_true fresh

/-- Erasing all family monitors and generation metadata retains the original actual complete typed source run and its full private table. -/
theorem native_erase (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK) (Fin cap) Forgery) :
    (fun result => (result.1, nativeState source result.2.native)) <$>
      (simulateQ (marked source setup checks wire route representation created credential) work).run before =
      (simulateQ (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential) work).run
        (nativeState source before.native) := by
  have familyErase := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (callback (cap := cap) (n := n) source setup checks wire route representation created credential)
    (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential)
    (nativeState source)
    (fun query current => RegistrationNativeMldsaGhostFamily.callback_erase source setup checks wire route representation created credential query current)
    work before.native
  have flagsErase := congrArg (fun distribution => Prod.map id (nativeState source) <$> distribution)
    (RegistrationNativeMldsaFiniteMonitor.erase
      (callback source setup checks wire route representation created credential) (bad source credential) (collision source) (observe source) work before)
  simp only [Functor.map_map, Prod.map, id_eq] at flagsErase familyErase
  exact flagsErase.trans familyErase

/-- Actual protected native bad cuts are bounded by the literal final shared-cache collision event of the original source execution and the finite family of actual dynamic candidate monitors. -/
theorem bound (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (remaining : Nat)
    (bounded : work.IsQueryBoundP cost remaining) (before : State source cap n KemSK)
    (initial : Safe source credential fallback before) (room : counter source before + remaining ≤ cap) :
    Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK) (Fin cap) Forgery)}[result.2.bad = true] ≤
      Pr{let result ← (simulateQ (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential) work).run (nativeState source before)}[
        CacheHasCollision result.2.1.server.world.world.1.primitive.2] +
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativeMldsaGhostNative.callback source index.val setup checks wire route representation created credential)
        (RegistrationNativeMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
  have covered := RegistrationNativeMldsaFamilyCover.bound source setup checks wire route representation created credential fallback
    work remaining bounded before initial room
  have collisionBound :
      Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK) (Fin cap) Forgery)}[result.2.collision = true] ≤
        Pr{let result ← (simulateQ (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential) work).run (nativeState source before)}[
          CacheHasCollision result.2.1.server.world.world.1.primitive.2] := by
    have erased := native_erase source setup checks wire route representation created credential work
      ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK) (Fin cap) Forgery)
    change (fun result => (result.1, nativeState source result.2.native)) <$>
      (simulateQ (marked source setup checks wire route representation created credential) work).run
        ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK) (Fin cap) Forgery) =
      (simulateQ (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential) work).run
        (nativeState source before) at erased
    rw [← erased, prEvent_map]
    exact prEvent_mono_of_support _ _ _ fun result supported active =>
      (collision_flag source setup checks wire route representation created credential fallback work
        ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK) (Fin cap) Forgery)
        initial (by intro impossible; cases impossible) result supported).2 active
  exact covered.trans (add_le_add collisionBound le_rfl)

end BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyFinalCover
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyFinalCover.native_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyFinalCover.native_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyFinalCover.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyFinalCover.bound
