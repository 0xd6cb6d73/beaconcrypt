-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerSourceLens
import BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual Server completion Local stack lifts through the existing complete Native field, retaining Server control/pin/replay/session metadata, owners, KEM pool and parsed-attempt counter. Its lawful interpretation preserves source failures and returned mutable buffers; it introduces no second memory model. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerLocalLens
open AdapterPublicWrapperRustT (RustT)
open BeaconcryptCore.Computational
variable {n : Nat} {KemSK A B : Type} {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "LocalM" => StateT (RegistrationServerRootCompiler.Local n) m
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m

def putLocal (before : RegistrationNativeExperiment.State n KemSK mlSource) (current : RegistrationServerRootCompiler.Local n) :
    RegistrationNativeExperiment.State n KemSK mlSource := {before with server := {before.server with world := current}}

def localState (work : LocalM A) : NativeM A :=
  RegistrationNativePlatformExperiment.server (RegistrationNativePlatformServerSdk.world work)

theorem local_run (work : LocalM A) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (localState work).run before = (fun result => (result.1, putLocal before result.2)) <$> work.run before.server.world := by
  simp only [localState, RegistrationNativePlatformExperiment.server, RegistrationNativePlatformServerSdk.world,
    StateT.run, Functor.map_map]
  rfl

theorem local_pure (value : A) :
    localState (n := n) (KemSK := KemSK) (mlSource := mlSource) (pure value : LocalM A) = pure value := by
  apply StateT.ext
  intro before
  rw [local_run, StateT.run_pure, StateT.run_pure, map_pure]
  rfl

theorem local_bind (work : LocalM A) (next : A → LocalM B) :
    localState (KemSK := KemSK) (mlSource := mlSource) (work >>= next) =
      (localState work >>= fun value => localState (next value)) := by
  apply StateT.ext
  intro before
  rw [local_run, StateT.run_bind, StateT.run_bind]
  simp only [local_run, map_bind, bind_map_left]
  rfl

theorem local_lift (work : m A) :
    localState (n := n) (KemSK := KemSK) (mlSource := mlSource) (StateT.lift work) = (StateT.lift work : NativeM A) := by
  apply StateT.ext
  intro before
  rw [local_run, StateT.run_lift, StateT.run_lift]
  simp only [map_bind, map_pure]
  rfl

noncomputable def transform (work : RustT LocalM A) : RustT NativeM A := ⟨localState work.run⟩

theorem transform_pure (value : A) : transform (n := n) (KemSK := KemSK) (mlSource := mlSource) (pure value : RustT LocalM A) = pure value := by
  apply RustT.ext
  exact local_pure (RustM.ok value)

theorem transform_liftRust (result : RustM A) :
    transform (n := n) (KemSK := KemSK) (mlSource := mlSource) (AdapterRecordRequestMonad.liftRust result : RustT LocalM A) =
      AdapterRecordRequestMonad.liftRust result := by
  apply RustT.ext
  exact local_pure result

theorem transform_bind (work : RustT LocalM A) (next : A → RustT LocalM B) :
    transform (KemSK := KemSK) (mlSource := mlSource) (work >>= next) = (transform work >>= fun value => transform (next value)) := by
  apply RustT.ext
  change localState ((work >>= next).run) = _
  rw [RustT.run_bind, local_bind]
  change (localState work.run >>= fun result => localState (match result with
    | .ok value => (next value).run
    | .fail error => pure (.fail error)
    | .div => pure .div)) = _
  rw [RustT.run_bind]
  apply bind_congr
  intro result
  cases result <;> simp only [local_pure, transform]

@[instance_reducible] noncomputable def translation : AdapterPublicAgreementMonadMap.Transformation LocalM NativeM where
  transform := transform
  lawful := Cslib.IsMonadHom.mk' transform_pure transform_bind
  lift := transform_liftRust

end BeaconcryptCore.Refinement.AdapterPublicServerLocalLens
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.local_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.local_run
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.local_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.local_pure
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.local_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.local_bind
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.local_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.local_lift
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.transform_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.transform_pure
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.transform_liftRust' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.transform_liftRust
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.transform_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLocalLens.transform_bind
