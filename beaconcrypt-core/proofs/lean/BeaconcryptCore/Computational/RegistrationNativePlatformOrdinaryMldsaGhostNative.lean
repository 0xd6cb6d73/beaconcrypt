-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows
import BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableCallback

/-! Actual native callbacks retain the selected-generation ghost and true-count ML table. Ghost erasure recovers the original callback exactly. Literal same-cut successful-birth and candidate receipts select the dynamic observer, without postulating adaptive key independence. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGhostNative
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Platform E : Type} {base : OracleSpec ι}
variable (source : Source)

abbrev State (n : Nat) (KemSK Platform : Type) :=
  RegistrationNativePlatformOrdinaryMldsaCountStop.State n KemSK Platform (handleSource source) × (RegistrationNativeMldsaGenerationGhost.State × Pool source)

def nativeState (before : State source n KemSK Platform) : RegistrationNativePlatformOrdinaryMldsaTableCallback.State (n := n) (KemSK := KemSK) (Platform := Platform) source := (before.1, before.2.2)
def rowState (before : State source n KemSK Platform) := before.2

noncomputable def callback (selected : Nat) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source))
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State source n KemSK Platform) ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
    RegistrationNativeMldsaTableProgram.runState source
      (RegistrationNativeMldsaGhostState.track source selected
        (RegistrationNativePlatformOrdinaryMldsaCountStop.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)) (before.1, before.2.1) before.2.2

def observe (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source n KemSK Platform)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) (after : State source n KemSK Platform) :=
  after.2.1.publicKey.bind (fun publicKey => RegistrationNativeMldsaTrialObserver.observe source.verify publicKey query before.1.1 reply after.1.1)

private theorem map_apply {S A B : Type} (function : A → B) (work : StateT S ProbComp A) (before : S) :
    (function <$> work) before = (fun pair => (function pair.1, pair.2)) <$> work before := StateT.run_map function work before

/-- Erasing only the generation ghost retains the exact callback reply, complete native state and actual private table. -/
theorem project (selected : Nat) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source))
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source n KemSK Platform) :
    (fun result => (result.1, nativeState source result.2)) <$>
      (callback source selected setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before =
      (RegistrationNativePlatformOrdinaryMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run (nativeState source before) := by
  rw [RegistrationNativePlatformOrdinaryMldsaTableCallback.generic]
  have erased := congrArg (fun program => RegistrationNativeMldsaTableProgram.evaluate source program before.2.2)
    (RegistrationNativeMldsaGhostState.erase source selected
      (RegistrationNativePlatformOrdinaryMldsaCountStop.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query) before.1 before.2.1)
  simp only [RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, StateT.run_map] at erased
  have observed := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution) erased
  simpa only [callback, RegistrationNativeMldsaTableProgram.runState,
    RegistrationNativeMldsaTableProgram.evaluate, StateT.run, Functor.map_map, nativeState] using observed

/-- Every reached actual tracked callback retains complete selected-row public-key provenance. -/
theorem rows (selected : Nat) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source))
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source n KemSK Platform)
    (good : RegistrationNativeMldsaGhostRows.Safe source selected (rowState source before))
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source n KemSK Platform)
    (supported : result ∈ support ((callback source selected setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    RegistrationNativeMldsaGhostRows.Safe source selected (rowState source result.2) := by
  simp only [callback, StateT.run, RegistrationNativeMldsaTableProgram.runState,
    RegistrationNativeMldsaGhostState.track, simulateQ_map, map_apply, Functor.map_map,
    RegistrationNativeMldsaTableProgram.evaluate, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  have joint : (inner.1.1, (inner.1.2, inner.2)) ∈ support
      ((simulateQ (RegistrationNativeMldsaGhostRows.handler source selected)
        ((RegistrationNativePlatformOrdinaryMldsaCountStop.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before.1)).run
        (rowState source before)) := by
    rw [RegistrationNativeMldsaGhostRows.source_program, support_map]
    exact ⟨inner, possible, rfl⟩
  exact RegistrationNativeMldsaGhostRows.program_keep source selected _ _ good (inner.1.1, (inner.1.2, inner.2)) joint

/-- A candidate at the literal selected successful birth is selected by the dynamic actual ghost observer. -/
theorem capture (selected : Nat) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source))
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source n KemSK Platform)
    (good : RegistrationNativeMldsaGhostRows.Safe source selected (rowState source before))
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source n KemSK Platform)
    (supported : result ∈ support ((callback source selected setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before))
    (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (born : RegistrationNativeMldsaProtectedCoverage.BornKey source result.2.2.2 selected publicKey)
    (forgery : RegistrationNativeMldsaEuf.Forgery)
    (chosen : RegistrationNativePlatformOrdinaryMldsaTableCallback.observe source publicKey query (nativeState source before) result.1
      (nativeState source result.2) = some forgery) : observe source query before result.1 result.2 = some forgery := by
  have learned := RegistrationNativeMldsaGhostRows.learned source selected (rowState source result.2)
    (rows source selected setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before good result supported) publicKey born
  change result.2.2.1.publicKey.bind _ = some forgery
  change result.2.2.1.publicKey = some publicKey at learned
  rw [learned, Option.bind_some]
  exact chosen

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGhostNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGhostNative.project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGhostNative.project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGhostNative.rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGhostNative.rows

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGhostNative.capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGhostNative.capture
