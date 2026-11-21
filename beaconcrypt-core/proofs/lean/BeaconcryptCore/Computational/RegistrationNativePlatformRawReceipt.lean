-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild
import BeaconcryptCore.Refinement.AdapterRecordRawBytes

/-! The actual source first-record raw writer returns exactly the original three chunks after its stateful public reservation. The private native World, KDF state and signing receipts remain verbatim; the reached write marker and external allocation poststate are retained. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRawReceipt
open BeaconcryptCore.Refinement
open RegistrationServerRootCompiler (Local)
variable {n : Nat} {E Platform : Type}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem write_raw
    (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → m (RustM (Usize × Slice U8)))
    (first second third : Slice U8) :
    RegistrationNativePlatformSourceCompletion.writeWith (AdapterRecordRawBytes.helper allocation serializer)
      (.Raw (Std.Array.make 3#usize [first, second, third])) =
        AdapterRecordRawBytes.raw allocation serializer first second third := by
  have same : AdapterRecordNativeWriter.borrow = (id : RustM (Option (alloc.vec.Vec U8)) → RustM (Option (alloc.vec.Vec U8))) :=
    funext AdapterRecordNativeWriter.borrow_exact
  simp only [RegistrationNativePlatformSourceCompletion.writeWith, same, id_map]
  rfl

omit [Monad m] [LawfulMonad m] in
/-- Actual successful source raw output retains its full public allocator poststate and literal native-state footprint. -/
theorem successful
    (allocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (parts : Std.Array (Slice U8) 3#usize) (output : Slice U8)
    (before after : Local n) (previous next : Platform)
    (supported : ((.ok (some output), after), next) ∈ support
      (((RegistrationNativePlatformSourceBuild.write (AdapterRecordRawBytes.helper allocation serializer) (.Raw parts)).run before).run previous)) :
    output.val = parts.val.flatMap Subtype.val ∧
      after = { before with recordRequests := before.recordRequests ++
        [RegistrationWorldAgreement.recordCall (.write (.Raw parts))] } := by
  obtain ⟨first, second, third, values⟩ := List.length_eq_three.mp parts.property
  have partsEq : parts = Std.Array.make 3#usize [first, second, third] := Subtype.ext values
  rw [partsEq, RegistrationNativePlatformSourceBuild.write_joint, write_raw, support_map] at supported
  obtain ⟨⟨result, platform⟩, called, equal⟩ := supported
  have equalParts := Prod.mk.inj equal
  obtain ⟨same, stateEq⟩ := Prod.mk.inj equalParts.1
  have platformEq := equalParts.2
  cases same
  cases platformEq
  have bytes := AdapterRecordRawBytes.raw_success allocation serializer first second third output previous platform called
  refine ⟨?_, ?_⟩
  · simpa only [values, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] using bytes
  · simpa only [partsEq] using stateEq.symm

end BeaconcryptCore.Computational.RegistrationNativePlatformRawReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRawReceipt.write_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRawReceipt.write_raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRawReceipt.successful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRawReceipt.successful
