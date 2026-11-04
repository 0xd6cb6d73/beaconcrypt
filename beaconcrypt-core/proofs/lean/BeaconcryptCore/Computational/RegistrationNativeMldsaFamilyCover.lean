-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaBadCut
import BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds

/-! The finite native origin cover uses one actual true-count source execution. Its per-cut invariant and generation ceiling come from the original typed controllers; the source bad event and all dynamic generation observers are monitored together. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaGhostFamily (State callback nativeState coordinateState)
open RegistrationNativeMldsaEuf (Forgery)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n cap : Nat} {ι KemSK V : Type} {base : OracleSpec ι}
variable (source : Source)

def Safe (credential : Credential (handleSource source)) (fallback : Credential source) (before : State source cap n KemSK) : Prop :=
  RegistrationNativeMldsaProtectedInvariant.Holds source credential fallback (nativeState source before) ∧
    ∀ index : Fin cap, RegistrationNativeMldsaGhostRows.Safe source index.val (before.2.1 index, before.2.2)

def observe (index : Fin cap) : RegistrationNativeMldsaStop.Observer (spec := RegistrationNativeRawAdapter.TypedSpec)
    (State := State source cap n KemSK) (Candidate := Forgery) := fun query before reply after =>
  RegistrationNativeMldsaGhostNative.observe source query (coordinateState source index before) reply (coordinateState source index after)

def bad (credential : Credential (handleSource source)) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) (_after : State source cap n KemSK) : Prop :=
  RegistrationNativeMldsaBadCut.Bad source credential query (nativeState source before) reply

def collision (before : State source cap n KemSK) : Prop := CacheHasCollision before.1.server.world.world.1.primitive.2

def counter (before : State source cap n KemSK) : Nat := before.2.2.attempts

def cost (query : RegistrationNativeRawAdapter.TypedSpec.Domain) : Prop := RegistrationNativeRawAdapter.kind query = (1 : Fin 12)
instance : DecidablePred cost := fun query => inferInstanceAs (Decidable (RegistrationNativeRawAdapter.kind query = (1 : Fin 12)))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source)) (fallback : Credential source)

private theorem projected (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before)) :
    (result.1, nativeState source result.2) ∈ support
      ((RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential query).run (nativeState source before)) := by
  rw [← RegistrationNativeMldsaGhostFamily.callback_erase, support_map]
  exact ⟨result, supported, rfl⟩

/-- Every complete actual family callback preserves the simultaneous reached source invariants. -/
theorem step_safe (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK)
    (safe : Safe source credential fallback before)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before)) :
    Safe source credential fallback result.2 :=
  ⟨RegistrationNativeMldsaProtectedInvariant.step source setup checks wire route representation created credential fallback query
      (nativeState source before) safe.1 (result.1, nativeState source result.2)
      (projected source setup checks wire route representation created credential query before result supported),
    RegistrationNativeMldsaGhostFamily.callback_rows source setup checks wire route representation created credential query before safe.2 result supported⟩

private theorem predicate (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) :
    RegistrationNativeMldsaGenerateBounds.IsGenerate query ↔ RegistrationNativeMldsaEager.IsGenerate source query := by
  cases query with
  | inl coin => simp only [RegistrationNativeMldsaGenerateBounds.IsGenerate, RegistrationNativeMldsaNoGenerate.Allowed,
      RegistrationNativeMldsaEager.IsGenerate, not_true_eq_false]
  | inr query => cases query <;> simp only [RegistrationNativeMldsaGenerateBounds.IsGenerate,
      RegistrationNativeMldsaNoGenerate.Allowed, RegistrationNativeMldsaEager.IsGenerate, not_true_eq_false, not_false_eq_true]

/-- Actual failed and successful generation attempts are bounded by this original callback's syntactic creation slot. -/
theorem step_count (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK)
    (safe : Safe source credential fallback before)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before)) :
    counter source result.2 ≤ counter source before + (if cost query then 1 else 0) := by
  have possible := projected source setup checks wire route representation created credential query before result supported
  simp only [RegistrationNativeMldsaTableStop.callback, StateT.run, RegistrationNativeMldsaTableProgram.runState, support_map] at possible
  obtain ⟨inner, reached, same⟩ := possible
  have bounded := (isQueryBoundP_congr_pred (predicate source)).mp
    (RegistrationNativeMldsaGenerateBounds.handler setup checks wire route representation created credential query before.1)
  have ceiling := RegistrationNativeMldsaBirthProvenance.attempts source _ _ bounded before.2.2 safe.1.provenance inner reached
  have poolSame := congrArg (fun value => value.2.2) same
  change inner.2 = result.2.2.2 at poolSame
  simpa only [counter, cost, poolSame] using ceiling

def coordinateMonitor (index : Fin cap) (before : State source cap n KemSK × Option Forgery) :=
  (coordinateState source index before.1, before.2)

private theorem monitor_step (index : Fin cap) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK × Option Forgery) :
    Prod.map id (coordinateMonitor source index) <$>
      (RegistrationNativeMldsaStop.monitor (callback source setup checks wire route representation created credential)
        (observe source index) query).run before =
      (RegistrationNativeMldsaStop.monitor
        (RegistrationNativeMldsaGhostNative.callback source index.val setup checks wire route representation created credential)
        (RegistrationNativeMldsaGhostNative.observe source) query).run (coordinateMonitor source index before) := by
  have same := congrArg (fun distribution => (fun result => (result.1, (result.2,
    before.2.orElse fun _ => RegistrationNativeMldsaGhostNative.observe source query (coordinateState source index before.1) result.1 result.2))) <$> distribution)
    (RegistrationNativeMldsaGhostFamily.callback_coordinate source index setup checks wire route representation created credential query before.1)
  simpa only [RegistrationNativeMldsaStop.monitor, StateT.run, bind_pure_comp, Functor.map_map,
    coordinateMonitor, observe, Prod.map, id_eq] using same

/-- Every full coordinate monitor is the actual single-ordinal dynamic native experiment, jointly retaining its original reply and true-count source state. -/
theorem monitor_coordinate (index : Fin cap) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : State source cap n KemSK × Option Forgery) :
    Prod.map id (coordinateMonitor source index) <$>
      (simulateQ (RegistrationNativeMldsaStop.monitor (callback source setup checks wire route representation created credential)
        (observe source index)) work).run before =
      (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativeMldsaGhostNative.callback source index.val setup checks wire route representation created credential)
        (RegistrationNativeMldsaGhostNative.observe source)) work).run (coordinateMonitor source index before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _
    (monitor_step source setup checks wire route representation created credential index) work before

noncomputable def marked := RegistrationNativeMldsaFiniteMonitor.handler
  (callback (cap := cap) (n := n) source setup checks wire route representation created credential)
  (bad source credential) (collision source) (observe source)

/-- One original native bad-cut marker is covered by its same-run collision marker plus the finite family of actual dynamic single-ordinal candidate monitors. The syntactic creation cap is charged independently of generation success and private coin counts. -/
theorem bound (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (remaining : Nat)
    (bounded : work.IsQueryBoundP cost remaining) (before : State source cap n KemSK)
    (initial : Safe source credential fallback before) (room : counter source before + remaining ≤ cap) :
    Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK) (Fin cap) Forgery)}[result.2.bad = true] ≤
    Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK) (Fin cap) Forgery)}[result.2.collision = true] +
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativeMldsaGhostNative.callback source index.val setup checks wire route representation created credential)
        (RegistrationNativeMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
  have cover := RegistrationNativeMldsaFiniteMonitor.bound
    (callback source setup checks wire route representation created credential) (bad source credential) (collision source) (observe source)
    (Safe source credential fallback) (counter source) cost cap
    (step_safe source setup checks wire route representation created credential fallback)
    (step_count source setup checks wire route representation created credential fallback)
    (fun query first result safe room supported failure => RegistrationNativeMldsaBadCut.cover source setup checks wire route representation
      created credential fallback query first result safe.1 safe.2 room supported failure)
    work remaining bounded before initial room
  have coordinates : (∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
      (callback source setup checks wire route representation created credential) (observe source index)) work).run (before, none)}[
        result.2.2.isSome = true]) =
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativeMldsaGhostNative.callback source index.val setup checks wire route representation created credential)
        (RegistrationNativeMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
    apply Finset.sum_congr rfl
    intro index _member
    have same := monitor_coordinate source setup checks wire route representation created credential index work (before, none)
    simp only [coordinateMonitor] at same
    rw [← same, prEvent_map]
    rfl
  rw [coordinates] at cover
  exact cover

end BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover.step_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover.step_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover.step_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover.step_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover.monitor_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover.monitor_coordinate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover.bound
