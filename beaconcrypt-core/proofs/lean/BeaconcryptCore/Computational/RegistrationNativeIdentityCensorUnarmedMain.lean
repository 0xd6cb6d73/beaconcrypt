-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealQuiet

/-! Before the public selected bundle is armed, the complete actual Main/P computation retains its original source marginal. The physical cache and chronological input journal are preserved and no signing occurrence is selected privately. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorPrefix (Unarmed)
variable {n : Nat} {KemSK Platform A : Type} {mlSource : RegistrationNativeMldsa.Source}

/-- The full unarmed source execution erases only private censor metadata; all source queries, replies, generated rows and physical cache/journal remain literal. -/
theorem source (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (prior : Unarmed before.1.2) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (interpret joint selected placeholder censored work).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret joint work).run
        (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  have law := RegistrationNativeIdentityCensorOperationalPrefix.source joint selected placeholder censored
    (work.run before.1.1) (before.1.2, before.2) prior
  rw [QueryImpl.Stateful.simulateQ_link_run, Functor.map_map] at law
  change (fun result : ((A × (RegistrationNativeIdentityMain.State n KemSK mlSource × Platform)) × RegistrationNativeIdentityCensorCompiler.Mode) × RegistrationNativeIdentityCensorSource.State =>
      (result.1.1, (result.2.pool, result.2.hash))) <$>
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2 = _ at law
  have result := congrArg (fun distribution =>
    (fun value : (A × (RegistrationNativeIdentityMain.State n KemSK mlSource × Platform)) × RegistrationNativePlatformIdentityCtxSource.State =>
      (value.1.1, (value.1.2, value.2))) <$> distribution) law
  simpa only [interpret, RegistrationNativePlatformIdentityCtxMain.interpret, StateT.run,
    bind_pure_comp, Functor.map_map, RegistrationNativeIdentityCensorActualHashSource.project,
    RegistrationNativeIdentityCensorOperationalPrefix.project, Prod.map_def, id_eq] using result

/-- Unarmed actual Main computation has identical complete real/private-censored replies and state, without a stored-log projection. -/
theorem paired (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (prior : Unarmed before.1.2) :
    (interpret joint selected placeholder false work).run before =
      (interpret joint selected placeholder true work).run before := by
  have same := congrArg (fun distribution => (fun result =>
      (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$> distribution)
    (RegistrationNativeIdentityCensorQuietSource.unarmed joint selected placeholder (work.run before.1.1) before.1.2 prior before.2)
  simpa only [interpret, StateT.run, RegistrationNativeIdentityCensorMldsaOutgoingSource.run, bind_pure_comp] using same

/-- A callback away from the fixed public bundle ordinal cannot arm the selected-signature proxy. -/
theorem enter (position : Nat) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (mode : RegistrationNativeIdentityCensorCompiler.Mode)
    (none : mode.target = Option.none)
    (different : ∀ index, query = .inr (.bundle index) → mode.bundles ≠ position) :
    Unarmed (RegistrationNativeIdentityCensorCompiler.enter position query mode) := by
  rcases query with query | query
  · exact ⟨rfl, none, rfl⟩
  · cases query <;> try exact ⟨rfl, none, rfl⟩
    rename_i index
    change (mode.bundles == position) = false ∧ mode.target = Option.none ∧ (false : Bool) = false
    exact ⟨by simpa only [beq_eq_false_iff_ne] using different index rfl, none, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain.paired

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain.enter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain.enter
