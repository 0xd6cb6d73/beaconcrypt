-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback

/-! The actual fixed-width Init source serializer's failure flag and complete shared platform poststate do not depend on the hidden signature bytes. Its capacity is always1490. This is only a concrete writer frame, not a protocol publication-security assumption or a full client-history replacement theorem. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView
open BeaconcryptCore.Refinement
open AdapterRegistrationWriterRequestMonad
open RegistrationSerializerReachableSource
variable {E Platform : Type}

noncomputable def writer (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : OtherBranches) (view : registration.InitView) :
    StateT Platform ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ (RegistrationSourceWriterBody.platform reserve
      (@beaconcrypt_parse.extraction_encode_init (operations other))
      (@beaconcrypt_parse.extraction_encode_response (operations other)))
    (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := Program E)
      (RegistrationNativeSourceEncoders.initSyntax view)).run

def flag : RustM (core.option.Option (alloc.vec.Vec U8)) → Bool
  | .ok (.Some _) => true
  | _ => false

/-- Actual source allocation, failure result and full external poststate are independent of every value in the fixed-width signed Init view. -/
theorem flag_source (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : OtherBranches) (view : registration.InitView) (before : Platform) :
    Prod.map flag id <$> (writer reserve other view).run before =
      (fun result => ((match result.1 with | .Ok _ => true | .Err _ => false), result.2)) <$> (reserve 1490#usize).run before := by
  rw [writer, RegistrationNativeSourceWriterReadback.init_source]
  simp only [StateT.run_map, Functor.map_map, Prod.map, id_eq]
  congr 1
  funext result
  cases result.1 <;> rfl

/-- Replacing an unpublished signature or unsigned fields preserves the actual complete failure-flag/platform distribution at the concrete source writer boundary. -/
theorem flag_independent (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : OtherBranches) (first second : registration.InitView) (before : Platform) :
    Prod.map flag id <$> (writer reserve other first).run before =
      Prod.map flag id <$> (writer reserve other second).run before := by
  rw [flag_source, flag_source]

/-- A failed concrete source Init writer returned no bytes because that same reached reservation failed; no serializer/adversary security conclusion is assumed. -/
theorem failure (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : OtherBranches) (view : registration.InitView) (before after : Platform) :
    (.ok .None, after) ∈ support ((writer reserve other view).run before) ↔
      ∃ error, (.Err error, after) ∈ support ((reserve 1490#usize).run before) := by
  rw [writer, RegistrationNativeSourceWriterReadback.init_source, StateT.run_map, support_map]
  constructor
  · rintro ⟨⟨allocation, final⟩, called, same⟩
    cases allocation with
    | Err error =>
      have finalEq : final = after := congrArg Prod.snd same
      exact ⟨error, finalEq ▸ called⟩
    | Ok value => cases congrArg Prod.fst same
  · rintro ⟨error, called⟩
    exact ⟨(.Err error, after), called, rfl⟩

/-- Every same-platform failed write has the identical failed outcome for any replacement signed view at this actual source boundary. -/
theorem failure_independent (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : OtherBranches) (first second : registration.InitView) (before after : Platform) :
    (.ok .None, after) ∈ support ((writer reserve other first).run before) ↔
      (.ok .None, after) ∈ support ((writer reserve other second).run before) := by
  rw [failure, failure]

end BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView.flag_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView.flag_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView.flag_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView.flag_independent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView.failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView.failure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView.failure_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView.failure_independent
