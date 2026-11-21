-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter

/-! Source writer primitives receive their literal public packet, vector and serializer-buffer requests and own an external platform state. Lifting this interface leaves every private native coordinate inaccessible and unchanged, while retaining all allocator/writer poststates. Uniform primitive draws do not expose or change that platform state. This supplies a restricted operational interface for later hybrid composition, rather than an assumed security or whole-profile equivalence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter
open BeaconcryptCore.Refinement
variable {E Native Platform Value : Type}
abbrev M (Platform : Type) := StateT Platform ProbComp

def coins : QueryImpl unifSpec (M Platform) := fun query => StateT.lift (unifSpec.query query)

theorem coins_joint (query : unifSpec.Domain) (before : Platform) :
    (coins query).run before = (fun value => (value, before)) <$>
      (unifSpec.query query : ProbComp (unifSpec.Range query)) := by
  exact StateT.run_lift _ _

theorem lift_joint (work : M Platform Value) (before : Native) :
    (StateT.lift work : StateT Native (M Platform) Value).run before =
      (fun value => (value, before)) <$> work := by
  exact StateT.run_lift _ _

def init
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M Platform))
    (view : registration.InitView) :
    StateT Native (M Platform) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  StateT.lift (simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeInit
    (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
    (RegistrationNativePlatformWriter.initPacket view)).run)

def response
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M Platform))
    (view : registration.SignedResponseView) :
    StateT Native (M Platform) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  StateT.lift (simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeResponse
    (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
    (RegistrationNativePlatformWriter.responsePacket view)).run)

theorem init_joint
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M Platform))
    (view : registration.InitView) (current : Native) (before : Platform) :
    ((init writer view).run current).run before =
      (fun result => ((result.1, current), result.2)) <$>
        (simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeInit
          (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
          (RegistrationNativePlatformWriter.initPacket view)).run).run before := by
  simp only [init, StateT.run_lift, bind_pure_comp, StateT.run_map]

theorem response_joint
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M Platform))
    (view : registration.SignedResponseView) (current : Native) (before : Platform) :
    ((response writer view).run current).run before =
      (fun result => ((result.1, current), result.2)) <$>
        (simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeResponse
          (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
          (RegistrationNativePlatformWriter.responsePacket view)).run).run before := by
  simp only [response, StateT.run_lift, bind_pure_comp, StateT.run_map]
/-- The source-derived Init writer preserves all private native fields on every reached outcome, including allocation/serializer failure. -/
theorem init_native
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M Platform))
    (view : registration.InitView) (current : Native) (before : Platform)
    (result : (RustM (core.option.Option (alloc.vec.Vec U8)) × Native) × Platform)
    (supported : result ∈ support (((init writer view).run current).run before)) :
    result.1.2 = current := by
  rw [init_joint] at supported
  obtain ⟨inner, _possible, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  rfl
theorem response_native
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M Platform))
    (view : registration.SignedResponseView) (current : Native) (before : Platform)
    (result : (RustM (core.option.Option (alloc.vec.Vec U8)) × Native) × Platform)
    (supported : result ∈ support (((response writer view).run current).run before)) :
    result.1.2 = current := by
  rw [response_joint] at supported
  obtain ⟨inner, _possible, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.coins_joint' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.coins_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.lift_joint' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.lift_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.init_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.init_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.response_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.response_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.init_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.init_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.response_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter.response_native
