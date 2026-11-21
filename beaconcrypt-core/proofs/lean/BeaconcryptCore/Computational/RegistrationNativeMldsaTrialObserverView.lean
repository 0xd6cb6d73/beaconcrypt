-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver
import BeaconcryptCore.Computational.RegistrationNativeMldsaMainView
import BeaconcryptCore.Computational.RegistrationNativeMldsaMap

/-! The actual online trial observer ignores private ML secret representations and the explicitly erased source accounting fields. It retains the same actual public pin/phase/packet/history/cache operands. These are checked observation equations, not assumptions of whole-game equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView
open RegistrationNativeMldsaTrialObserver (trial observe)
open RegistrationNativeMldsaMap (Map nativeState)
open RegistrationNativeMldsaEuf (PublicKey)
variable {n : Nat} {KemSK : Type} {left right : RegistrationNativeMldsa.Source}

/-- Public-key-preserving private credential restoration does not change the actual reached trial. -/
theorem trial_key (mapping : Map left right) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK left) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
    trial query (nativeState mapping before) reply = trial query before reply := by
  cases query with
  | inl coin => rfl
  | inr query => cases query with
    | finish index packet =>
        cases packet with
        | none => rfl
        | some packet =>
            cases reply with
            | fail error | div => rfl
            | ok option => cases option with
              | none => rfl
              | some application =>
                  simp only [trial, nativeState, RegistrationNativeMldsaMap.owners_lookup]
                  cases before.beacons[index]? <;> rfl
    | _ => rfl

/-- The complete online selector factors through the literal public-key-preserving credential map. -/
theorem observe_key (mapping : Map left right) (verify : MldsaTranscriptAuth.Verify) (publicKey : PublicKey)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : RegistrationNativeExperiment.State n KemSK left) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
    observe verify publicKey query (nativeState mapping before) reply (nativeState mapping after) =
      observe verify publicKey query before reply after := by
  rw [observe, trial_key]
  rfl

/-- Private accounting erasure retains the exact trial and its same-cut signing prefix. -/
theorem trial_count (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK left) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
    trial query (RegistrationNativeMldsaMainView.project before) reply = trial query before reply := by
  cases query with
  | inl coin => rfl
  | inr query => cases query with
    | accept packet => rfl
    | finish index packet => rfl
    | _ => rfl

/-- The complete online selector does not inspect any omitted uniform/native/Env accounting input. -/
theorem observe_count (verify : MldsaTranscriptAuth.Verify) (publicKey : PublicKey)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : RegistrationNativeExperiment.State n KemSK left) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
    observe verify publicKey query (RegistrationNativeMldsaMainView.project before) reply
        (RegistrationNativeMldsaMainView.project after) = observe verify publicKey query before reply after := by
  rw [observe, trial_count]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView.trial_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView.trial_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView.observe_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView.observe_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView.trial_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView.trial_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView.observe_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView.observe_count
