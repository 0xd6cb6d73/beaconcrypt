-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
import BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView

/-! The chosen runtime Init writer is the very same original source operations used by the failed-publication censor. Its literal public1490 reservation and entire mutable platform state are retained; no arbitrary writer privacy or codec law is a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorConcreteWriter
open BeaconcryptCore.Refinement
variable {Platform E : Type}

def encode (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E)) (view : registration.InitView) :
    StateT Platform ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ (RegistrationNativePlatformConcreteSource.writer reserve)
    (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
      (RegistrationNativePlatformWriter.initPacket view)).run

/-- Literal concrete source binding, including the actual serializer branch dictionary and public allocation action. -/
theorem source (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E)) (view : registration.InitView) :
    encode reserve view = RegistrationNativeSourceWriterFailureView.writer reserve RegistrationNativeConcreteCodec.serializerBranches view := rfl

/-- Every failed write has the same actual failed result and complete P poststate for canonical or placeholder fields. -/
theorem failure (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (first second : registration.InitView) (before after : Platform) :
    (.ok .None, after) ∈ support ((encode reserve first).run before) ↔
      (.ok .None, after) ∈ support ((encode reserve second).run before) := by
  rw [source, source]
  exact RegistrationNativeSourceWriterFailureView.failure_independent reserve RegistrationNativeConcreteCodec.serializerBranches first second before after

/-- Concrete public success flags and platform states depend only on that one actual reservation, including every failed prefix. -/
theorem flag (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (first second : registration.InitView) (before : Platform) :
    Prod.map RegistrationNativeSourceWriterFailureView.flag id <$> (encode reserve first).run before =
      Prod.map RegistrationNativeSourceWriterFailureView.flag id <$> (encode reserve second).run before := by
  rw [source, source]
  exact RegistrationNativeSourceWriterFailureView.flag_independent reserve RegistrationNativeConcreteCodec.serializerBranches first second before

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorConcreteWriter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorConcreteWriter.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorConcreteWriter.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorConcreteWriter.failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorConcreteWriter.failure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorConcreteWriter.flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorConcreteWriter.flag
