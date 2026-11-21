-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostProtected

/-! A finite family of generation ghosts observes one actual free source execution. Each coordinate projects to its literal single-ordinal tracker; the family does not sample independent worlds or inspect future keys. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource Pool)
open RegistrationNativeMldsaProgram (Spec)
variable {V : Type} {cap : Nat} (source : Source)
abbrev Family (cap : Nat) := Fin cap → RegistrationNativeMldsaGenerationGhost.State

def step (query : (Spec (handleSource source)).Domain) (reply : (Spec (handleSource source)).Range query)
    (before : Family cap) : Family cap := fun index => RegistrationNativeMldsaGenerationGhost.step source index.val query reply (before index)

def handler : QueryImpl (Spec (handleSource source)) (StateT (Family cap) (OracleComp (Spec (handleSource source)))) :=
  fun query before => (fun reply => (reply, step source query reply before)) <$> (Spec (handleSource source)).query query

def run (work : OracleComp (Spec (handleSource source)) V) (before : Family cap) :
    OracleComp (Spec (handleSource source)) (V × Family cap) := (simulateQ (handler source) work).run before

private theorem run_bind (query : (Spec (handleSource source)).Domain)
    (next : (Spec (handleSource source)).Range query → OracleComp (Spec (handleSource source)) V) (before : Family cap) :
    run source ((Spec (handleSource source)).query query >>= next) before = (do
      let reply ← (Spec (handleSource source)).query query
      run source (next reply) (step source query reply before)) := by
  simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((fun reply => (reply, step source query reply before)) <$>
      ((Spec (handleSource source)).query query : OracleComp (Spec (handleSource source)) _) >>= fun middle =>
      (simulateQ (handler source) (next middle.1)).run middle.2) = _
  rw [bind_map_left]

private theorem single_bind (selected : Nat) (query : (Spec (handleSource source)).Domain)
    (next : (Spec (handleSource source)).Range query → OracleComp (Spec (handleSource source)) V)
    (before : RegistrationNativeMldsaGenerationGhost.State) :
    RegistrationNativeMldsaGenerationGhost.run source selected ((Spec (handleSource source)).query query >>= next) before = (do
      let reply ← (Spec (handleSource source)).query query
      RegistrationNativeMldsaGenerationGhost.run source selected (next reply)
        (RegistrationNativeMldsaGenerationGhost.step source selected query reply before)) := by
  simp only [RegistrationNativeMldsaGenerationGhost.run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((fun reply => (reply, RegistrationNativeMldsaGenerationGhost.step source selected query reply before)) <$>
      ((Spec (handleSource source)).query query : OracleComp (Spec (handleSource source)) _) >>= fun middle =>
      (simulateQ (RegistrationNativeMldsaGenerationGhost.handler source selected) (next middle.1)).run middle.2) = _
  rw [bind_map_left]

/-- Each family coordinate is exactly the single tracker on the same source program and optional replies. -/
theorem coordinate (index : Fin cap) (work : OracleComp (Spec (handleSource source)) V) (before : Family cap) :
    (fun result => (result.1, result.2 index)) <$> run source work before =
      RegistrationNativeMldsaGenerationGhost.run source index.val work (before index) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [run, RegistrationNativeMldsaGenerationGhost.run, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [run_bind, single_bind, map_bind]
      exact bind_congr (fun reply => ih reply _)

/-- Erasing all finite ghost metadata leaves the literal original free source execution. -/
theorem erase (work : OracleComp (Spec (handleSource source)) V) (before : Family cap) :
    Prod.fst <$> run source work before = work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [run, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [run_bind, map_bind]
      simp_rw [ih]

open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
abbrev State (cap n : Nat) (KemSK : Type) :=
  RegistrationNativeExperiment.State n KemSK (handleSource source) × (Family cap × Pool source)

def coordinateState (index : Fin cap) (before : State source cap n KemSK) : RegistrationNativeMldsaGhostNative.State source n KemSK :=
  (before.1, (before.2.1 index, before.2.2))

def nativeState (before : State source cap n KemSK) : RegistrationNativeMldsaTableStop.State (n := n) (KemSK := KemSK) source :=
  (before.1, before.2.2)

noncomputable def callback (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source)) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State source cap n KemSK) ProbComp) := fun query before =>
  (fun result => (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))) <$>
    RegistrationNativeMldsaTableProgram.evaluate source
      (run source ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query).run before.1)
        before.2.1) before.2.2

private theorem map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = (fun pair => (f pair.1, pair.2)) <$> work before := StateT.run_map f work before

/-- Each native family coordinate executes the literal original single-ordinal tracked callback on the same true-count private table. -/
theorem callback_coordinate (index : Fin cap) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK) :
    (fun result => (result.1, coordinateState source index result.2)) <$>
      (callback source setup checks wire route representation created credential query).run before =
      (RegistrationNativeMldsaGhostNative.callback source index.val setup checks wire route representation created credential query).run
        (coordinateState source index before) := by
  have same := congrArg (fun program => RegistrationNativeMldsaTableProgram.evaluate source program before.2.2)
    (coordinate source index ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query).run before.1) before.2.1)
  simp only [RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, StateT.run_map] at same
  have arranged := congrArg (fun distribution => (fun result => (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))) <$> distribution) same
  simpa only [callback, StateT.run, Functor.map_map, coordinateState,
    RegistrationNativeMldsaGhostNative.callback, RegistrationNativeMldsaTableProgram.runState,
    RegistrationNativeMldsaGhostState.track, RegistrationNativeMldsaGhostState.arrange,
    RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, map_apply] using arranged

/-- The joint finite family erases to the actual complete original native callback, without resetting any private source state. -/
theorem callback_erase (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK) :
    (fun result => (result.1, nativeState source result.2)) <$>
      (callback source setup checks wire route representation created credential query).run before =
      (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential query).run
        (nativeState source before) := by
  have same := congrArg (fun program => RegistrationNativeMldsaTableProgram.evaluate source program before.2.2)
    (erase source ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query).run before.1) before.2.1)
  simp only [RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, StateT.run_map] at same
  have arranged := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution) same
  simpa only [callback, StateT.run, Functor.map_map, nativeState, RegistrationNativeMldsaTableStop.callback,
    RegistrationNativeMldsaTableProgram.runState, RegistrationNativeMldsaTableProgram.evaluate] using arranged

/-- All actual finite selected-row invariants are retained simultaneously by one complete native callback. -/
theorem callback_rows (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK)
    (rows : ∀ index : Fin cap, RegistrationNativeMldsaGhostRows.Safe source index.val (before.2.1 index, before.2.2))
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before)) :
    ∀ index : Fin cap, RegistrationNativeMldsaGhostRows.Safe source index.val (result.2.2.1 index, result.2.2.2) := by
  intro index
  apply RegistrationNativeMldsaGhostNative.rows source index.val setup checks wire route representation created credential query
    (coordinateState source index before) (rows index) (result.1, coordinateState source index result.2)
  rw [← callback_coordinate source index setup checks wire route representation created credential query before, support_map]
  exact ⟨result, supported, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily.coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily.coordinate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily.callback_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily.callback_coordinate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily.callback_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily.callback_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily.callback_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily.callback_rows
