-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceInlining

/-! The unchecked native key service keeps the original native descriptor flags and records every valid demand lacking its actual preparation flag. Preparation, off-protected scheduling and the protected108-byte table remain the original operations. A clean query agrees exactly with the existing flag-enforcing service; no whole-game equality or source validity is assumed. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRetainedService (Flags)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationNativeKeyCompiler (KeySpec)
abbrev Spec := RegistrationNativeRetainedService.Spec
abbrev State := Flags × Bool
attribute [local irreducible] PqxdhServerAuthKeySchedule.fromRoot

def bad (input : Message → Option Pqxdh.Bytes) : Spec.Domain → Flags → Bool
  | .inr (.demand message), before => (input message).isSome && !before message
  | _, _ => false

def plain (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl Spec (StateT Flags (OracleComp KeySpec))
  | .inl coin => StateT.lift (RegistrationNativeKeyCompiler.coins coin)
  | .inr (.prepare message) => fun before =>
      pure ((input message).map (fun _ => message), Function.update before message (input message).isSome)
  | .inr (.demand message) => fun before =>
      match input message with
      | none => pure (none, before)
      | some bytes => if inside bytes then
          (fun output => (some output, before)) <$> (KeySpec.query (.inr bytes) : OracleComp KeySpec _)
        else pure (some (PqxdhServerAuthKeySchedule.fromRoot source
          (RegistrationNativeRelatedRoot.nativeRoot source bytes)), before)

def unchecked (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl Spec (StateT State (OracleComp KeySpec)) := fun query before =>
  (fun result => (result.1, (result.2, before.2 || bad input query before.1))) <$>
    (plain source input inside query).run before.1

/-- A locally clean unchecked query has the exact original flag-enforcing output and updated native flags. -/
theorem query_plain (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : Spec.Domain) (before : Flags) (good : bad input query before = false) :
    (plain source input inside query).run before =
      (RegistrationNativeG3KeyService.direct source input inside query).run before := by
  cases query with
  | inl coin => rfl
  | inr command => cases command with
    | prepare message => rfl
    | demand message =>
        cases formed : input message with
        | none => cases prepared : before message <;>
            simp only [plain, RegistrationNativeG3KeyService.direct, StateT.run, formed, prepared,
              Bool.false_eq_true, ite_false, ite_true]
        | some bytes =>
            have prepared : before message = true := by
              cases active : before message <;> simp_all only [bad, Option.isSome_some,
                Bool.not_false, Bool.not_true, Bool.true_and, Bool.true_eq_false]
            simp only [plain, RegistrationNativeG3KeyService.direct, StateT.run, formed, prepared, ite_true]

/-- Adding only the private audit preserves the same query whenever its actual pre-query preparation audit is false. -/
theorem query_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : Spec.Domain) (before : Flags) (marked : Bool) (good : bad input query before = false) :
    (unchecked source input inside query).run (before, marked) =
      (fun result => (result.1, (result.2, marked))) <$>
        (RegistrationNativeG3KeyService.direct source input inside query).run before := by
  change (fun result => (result.1, (result.2, marked || bad input query before))) <$>
    (plain source input inside query).run before = _
  rw [good, Bool.or_false, query_plain source input inside query before good]

/-- The actual unchecked callback records its valid-but-unprepared demand before any table reply and never clears an earlier marker. -/
theorem query_flag (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : Spec.Domain) (before : State) (result : Spec.Range query × State)
    (supported : result ∈ support ((unchecked source input inside query).run before)) :
    result.2.2 = (before.2 || bad input query before.1) := by
  simp only [unchecked, StateT.run, support_map] at supported
  obtain ⟨reached, _possible, rfl⟩ := supported
  rfl

end BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked.query_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked.query_plain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked.query_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked.query_flag
