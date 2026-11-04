-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyFinalCover

/-! The original actual typed source carries only its first protected unsigned-origin failure marker. Erasing all simultaneous ghost/candidate metadata preserves this exact bad-cut event. Its finite reduction bound therefore concerns the original source marker, rather than an event defined by the reductions' success. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadSource
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformMldsaGhostFamily (State nativeState coordinateState)
open RegistrationNativePlatformMldsaFamilyCover (Safe cost counter marked)
open RegistrationNativeMldsaEuf (Forgery)
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n cap : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source))
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def handler : QueryImpl RegistrationNativeRawAdapter.TypedSpec
    (StateT (RegistrationNativePlatformMldsaTableCallback.State (n := n) (KemSK := KemSK) (Platform := Platform) source × Bool) ProbComp) := by
  classical
  exact fun query before => (fun result => (result.1, (result.2, before.2 ||
    decide (RegistrationNativeMldsaBadCut.Bad source credential query (RegistrationNativePlatformMldsaTableStop.core source before.1) result.1)))) <$>
      (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before.1

def project (before : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery) :=
  (nativeState source before.native, before.bad)

private theorem step (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery) :
    Prod.map id (project source) <$>
      (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before =
      (handler source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run (project source before) := by
  classical
  have same := congrArg (fun distribution => (fun result => (result.1, (result.2, before.bad ||
    decide (RegistrationNativeMldsaBadCut.Bad source credential query (RegistrationNativePlatformMldsaTableStop.core source (nativeState source before.native)) result.1)))) <$> distribution)
    (RegistrationNativePlatformMldsaGhostFamily.callback_erase source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query before.native)
  simpa only [handler, marked, RegistrationNativeMldsaFiniteMonitor.handler, RegistrationNativeMldsaFiniteMonitor.advance,
    RegistrationNativePlatformMldsaFamilyCover.bad, project, RegistrationNativePlatformMldsaTableStop.core, RegistrationNativePlatformMldsaGhostFamily.nativeState, StateT.run, Functor.map_map, Prod.map, id_eq] using same

/-- The complete original source bad marker is retained exactly when all finite ghost and candidate metadata is erased. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery) :
    Prod.map id (project source) <$>
      (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run before =
      (simulateQ (handler source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run (project source before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _
    (step source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work before

/-- Actual protected source failure probability equals its simultaneous analysis instrument, without any event-coverage premise. -/
theorem probability (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (before : State source cap n KemSK Platform) :
    Pr{let result ← (simulateQ (handler source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run (nativeState source before, false)}[result.2.2 = true] =
      Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)}[result.2.bad = true] := by
  have same := program source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer work
    ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)
  simp only [project] at same
  rw [← same, prEvent_map]
  rfl

/-- The original actual protected unsigned-origin failure marker is covered by one literal final-cache collision charge and the finite family of actual dynamic generation monitors. -/
theorem bound (fallback : Credential source) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (remaining : Nat)
    (bounded : work.IsQueryBoundP cost remaining) (before : State source cap n KemSK Platform)
    (initial : Safe source credential fallback before) (room : counter source before + remaining ≤ cap) :
    Pr{let result ← (simulateQ (handler source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run (nativeState source before, false)}[result.2.2 = true] ≤
      Pr{let result ← (simulateQ (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run (nativeState source before)}[
        CacheHasCollision result.2.1.1.server.world.world.1.primitive.2] +
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativePlatformMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
  rw [probability source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer work before]
  exact RegistrationNativePlatformMldsaFamilyFinalCover.bound source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback
    work remaining bounded before initial room

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadSource.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadSource.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadSource.probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadSource.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadSource.bound
