-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows
import BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant

/-! Actual native callbacks retain the selected-generation ghost and true-count ML table. Ghost erasure recovers the original callback exactly. Literal same-cut successful-birth and candidate receipts select the dynamic observer, without postulating adaptive key independence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostNative
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (source : Source)

abbrev State (n : Nat) (KemSK : Type) :=
  RegistrationNativeExperiment.State n KemSK (handleSource source) × (RegistrationNativeMldsaGenerationGhost.State × Pool source)

def nativeState (before : State source n KemSK) : RegistrationNativeMldsaTableStop.State (n := n) (KemSK := KemSK) source := (before.1, before.2.2)
def rowState (before : State source n KemSK) := before.2

noncomputable def callback (selected : Nat) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source)) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State source n KemSK) ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
    RegistrationNativeMldsaTableProgram.runState source
      (RegistrationNativeMldsaGhostState.track source selected
        (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query)) (before.1, before.2.1) before.2.2

def observe (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source n KemSK)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) (after : State source n KemSK) :=
  after.2.1.publicKey.bind (fun publicKey => RegistrationNativeMldsaTrialObserver.observe source.verify publicKey query before.1 reply after.1)

private theorem map_apply {S A B : Type} (function : A → B) (work : StateT S ProbComp A) (before : S) :
    (function <$> work) before = (fun pair => (function pair.1, pair.2)) <$> work before := StateT.run_map function work before

/-- Erasing only the generation ghost retains the exact callback reply, complete native state and actual private table. -/
theorem project (selected : Nat) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source n KemSK) :
    (fun result => (result.1, nativeState source result.2)) <$>
      (callback source selected setup checks wire route representation created credential query).run before =
      (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential query).run (nativeState source before) := by
  have erased := congrArg (fun program => RegistrationNativeMldsaTableProgram.evaluate source program before.2.2)
    (RegistrationNativeMldsaGhostState.erase source selected
      (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query) before.1 before.2.1)
  simp only [RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, StateT.run_map] at erased
  have observed := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution) erased
  simpa only [callback, RegistrationNativeMldsaTableStop.callback, RegistrationNativeMldsaTableProgram.runState,
    RegistrationNativeMldsaTableProgram.evaluate, StateT.run, Functor.map_map, nativeState] using observed

/-- Every reached actual tracked callback retains complete selected-row public-key provenance. -/
theorem rows (selected : Nat) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source n KemSK)
    (good : RegistrationNativeMldsaGhostRows.Safe source selected (rowState source before))
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source n KemSK)
    (supported : result ∈ support ((callback source selected setup checks wire route representation created credential query).run before)) :
    RegistrationNativeMldsaGhostRows.Safe source selected (rowState source result.2) := by
  simp only [callback, StateT.run, RegistrationNativeMldsaTableProgram.runState,
    RegistrationNativeMldsaGhostState.track, simulateQ_map, map_apply, Functor.map_map,
    RegistrationNativeMldsaTableProgram.evaluate, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  have joint : (inner.1.1, (inner.1.2, inner.2)) ∈ support
      ((simulateQ (RegistrationNativeMldsaGhostRows.handler source selected)
        ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query).run before.1)).run
        (rowState source before)) := by
    rw [RegistrationNativeMldsaGhostRows.source_program, support_map]
    exact ⟨inner, possible, rfl⟩
  exact RegistrationNativeMldsaGhostRows.program_keep source selected _ _ good (inner.1.1, (inner.1.2, inner.2)) joint

/-- A candidate at the literal selected successful birth is selected by the dynamic actual ghost observer. -/
theorem capture (selected : Nat) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source n KemSK)
    (good : RegistrationNativeMldsaGhostRows.Safe source selected (rowState source before))
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source n KemSK)
    (supported : result ∈ support ((callback source selected setup checks wire route representation created credential query).run before))
    (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (born : RegistrationNativeMldsaProtectedCoverage.BornKey source result.2.2.2 selected publicKey)
    (forgery : RegistrationNativeMldsaEuf.Forgery)
    (chosen : RegistrationNativeMldsaTableStop.observe source publicKey query (nativeState source before) result.1
      (nativeState source result.2) = some forgery) : observe source query before result.1 result.2 = some forgery := by
  have learned := RegistrationNativeMldsaGhostRows.learned source selected (rowState source result.2)
    (rows source selected setup checks wire route representation created credential query before good result supported) publicKey born
  change result.2.2.1.publicKey.bind _ = some forgery
  change result.2.2.1.publicKey = some publicKey at learned
  rw [learned, Option.bind_some]
  exact chosen

end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostNative
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostNative.project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostNative.project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostNative.rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostNative.rows

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostNative.capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostNative.capture
