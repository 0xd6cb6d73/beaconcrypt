-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadCut
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostFamily
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds
import BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds

/-! The finite native origin cover uses one actual true-count source execution. Its per-cut invariant and generation ceiling come from the original typed controllers; the source bad event and all dynamic generation observers are monitored together. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformMldsaGhostFamily (State callback nativeState coordinateState)
open RegistrationNativeMldsaEuf (Forgery)
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n cap : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : Source)

def Safe (credential : Credential (handleSource source)) (fallback : Credential source) (before : State source cap n KemSK Platform) : Prop :=
  RegistrationNativeMldsaProtectedInvariant.Holds source credential fallback (before.1.1, before.2.2) ∧
    before.1.1.server.pin.public_key = credential.publicKey ∧
    ∀ index : Fin cap, RegistrationNativeMldsaGhostRows.Safe source index.val (before.2.1 index, before.2.2)

def observe (index : Fin cap) : RegistrationNativeMldsaStop.Observer (spec := RegistrationNativeRawAdapter.TypedSpec)
    (State := State source cap n KemSK Platform) (Candidate := Forgery) := fun query before reply after =>
  RegistrationNativePlatformMldsaGhostNative.observe source query (coordinateState source index before) reply (coordinateState source index after)

def bad (credential : Credential (handleSource source)) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK Platform) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) (_after : State source cap n KemSK Platform) : Prop :=
  RegistrationNativeMldsaBadCut.Bad source credential query (before.1.1, before.2.2) reply

def collision (before : State source cap n KemSK Platform) : Prop := CacheHasCollision before.1.1.server.world.world.1.primitive.2

def counter (before : State source cap n KemSK Platform) : Nat := before.2.2.attempts

def cost (query : RegistrationNativeRawAdapter.TypedSpec.Domain) : Prop := RegistrationNativeRawAdapter.kind query = (1 : Fin 12)
instance : DecidablePred cost := fun query => inferInstanceAs (Decidable (RegistrationNativeRawAdapter.kind query = (1 : Fin 12)))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (fallback : Credential source)

private theorem projected (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK Platform)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before)) :
    (result.1, nativeState source result.2) ∈ support
      ((RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run (nativeState source before)) := by
  rw [← RegistrationNativePlatformMldsaGhostFamily.callback_erase, support_map]
  exact ⟨result, supported, rfl⟩

omit primitive in
private theorem predicate (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) :
    RegistrationNativeMldsaGenerateBounds.IsGenerate query ↔ RegistrationNativeMldsaEager.IsGenerate source query := by
  cases query with
  | inl coin => simp only [RegistrationNativeMldsaGenerateBounds.IsGenerate, RegistrationNativeMldsaNoGenerate.Allowed,
      RegistrationNativeMldsaEager.IsGenerate, not_true_eq_false]
  | inr query => cases query <;> simp only [RegistrationNativeMldsaGenerateBounds.IsGenerate,
      RegistrationNativeMldsaNoGenerate.Allowed, RegistrationNativeMldsaEager.IsGenerate, not_true_eq_false, not_false_eq_true]

/-- Actual failed and successful generation attempts are bounded by this original callback's syntactic creation slot. -/
theorem step_count (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK Platform)
    (safe : Safe source credential fallback before)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before)) :
    counter source result.2 ≤ counter source before + (if cost query then 1 else 0) := by
  have possible := projected source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query before result supported
  simp only [RegistrationNativePlatformMldsaTableCallback.callback, StateT.run, RegistrationNativePlatformMldsaTableProgram.runState, support_map] at possible
  obtain ⟨inner, reached, same⟩ := possible
  have bounded := (isQueryBoundP_congr_pred (predicate source)).mp
    (RegistrationNativePlatformMldsaGenerateBounds.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query before.1.1 before.1.2)
  have ceiling := RegistrationNativeMldsaBirthProvenance.attempts source _ _ bounded before.2.2 safe.1.provenance inner reached
  have poolSame := congrArg (fun value => value.2.2) same
  change inner.2 = result.2.2.2 at poolSame
  simpa only [counter, cost, poolSame] using ceiling

def coordinateMonitor (index : Fin cap) (before : State source cap n KemSK Platform × Option Forgery) :=
  (coordinateState source index before.1, before.2)

private theorem monitor_step (index : Fin cap) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK Platform × Option Forgery) :
    Prod.map id (coordinateMonitor source index) <$>
      (RegistrationNativeMldsaStop.monitor (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (observe source index) query).run before =
      (RegistrationNativeMldsaStop.monitor
        (RegistrationNativePlatformMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaGhostNative.observe source) query).run (coordinateMonitor source index before) := by
  have same := congrArg (fun distribution => (fun result => (result.1, (result.2,
    before.2.orElse fun _ => RegistrationNativePlatformMldsaGhostNative.observe source query (coordinateState source index before.1) result.1 result.2))) <$> distribution)
    (RegistrationNativePlatformMldsaGhostFamily.callback_coordinate source index setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query before.1)
  simpa only [RegistrationNativeMldsaStop.monitor, StateT.run, bind_pure_comp, Functor.map_map,
    coordinateMonitor, observe, Prod.map, id_eq] using same

/-- Every full coordinate monitor is the actual single-ordinal dynamic native experiment, jointly retaining its original reply and true-count source state. -/
theorem monitor_coordinate (index : Fin cap) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : State source cap n KemSK Platform × Option Forgery) :
    Prod.map id (coordinateMonitor source index) <$>
      (simulateQ (RegistrationNativeMldsaStop.monitor (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (observe source index)) work).run before =
      (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativePlatformMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaGhostNative.observe source)) work).run (coordinateMonitor source index before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _
    (monitor_step source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer index) work before

noncomputable def marked := RegistrationNativeMldsaFiniteMonitor.handler
  (callback (cap := cap) (n := n) source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
  (bad source credential) (collision source) (observe source)



/-- One actual corrected family callback preserves every simultaneous reached source invariant. -/
theorem step_safe (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK Platform)
    (safe : Safe source credential fallback before)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query).run before)) : Safe source credential fallback result.2 := by
  have current : RegistrationNativePlatformMldsaTableStop.Safe source credential fallback (nativeState source before) :=
    ⟨safe.1.safe, safe.2.1, safe.1.provenance⟩
  have after := RegistrationNativePlatformMldsaTableStop.step_safe source setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer fallback query (nativeState source before) (result.1, nativeState source result.2) current
    (projected source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query before result supported)
  exact ⟨⟨after.toSafe, after.provenance⟩, after.pinned,
    RegistrationNativePlatformMldsaGhostFamily.callback_rows source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query before safe.2.2 result supported⟩


/-- One original native bad-cut marker is covered by its same-run collision marker plus the finite family of actual dynamic single-ordinal candidate monitors. The syntactic creation cap is charged independently of generation success and private coin counts. -/
theorem bound (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (remaining : Nat)
    (bounded : work.IsQueryBoundP cost remaining) (before : State source cap n KemSK Platform)
    (initial : Safe source credential fallback before) (room : counter source before + remaining ≤ cap) :
    Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)}[result.2.bad = true] ≤
    Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)}[result.2.collision = true] +
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativePlatformMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
  have cover := RegistrationNativeMldsaFiniteMonitor.bound
    (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) (bad source credential) (collision source) (observe source)
    (Safe source credential fallback) (counter source) cost cap
    (step_safe source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback)
    (step_count source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback)
    (fun query first result safe room supported badEvent => RegistrationNativePlatformMldsaBadCut.cover source setup checks wire route representation
      created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback query first result
        ⟨safe.1.safe, safe.2.1, safe.1.provenance⟩ safe.2.2 room supported badEvent)
    work remaining bounded before initial room
  have coordinates : (∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
      (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) (observe source index)) work).run (before, none)}[
        result.2.2.isSome = true]) =
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativePlatformMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
    apply Finset.sum_congr rfl
    intro index _member
    have same := monitor_coordinate source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer index work (before, none)
    simp only [coordinateMonitor] at same
    rw [← same, prEvent_map]
    rfl
  rw [coordinates] at cover
  exact cover

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover.step_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover.step_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover.step_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover.step_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover.monitor_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover.monitor_coordinate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover.bound
