-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer

/-! The actual repeated source pin helper ignores erased private accounting inputs while retaining the complete external platform state and literal hash-effect charge. Its input public key/binding and shared hash cache remain unchanged by the view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPinView
open RegistrationNativeKemCounterIndependence (Stable pure_stable bind_stable program_stable)
open RegistrationNativeMldsaWorldView (project idempotent)
variable {n : Nat} {Platform : Type}

/-- Pure configured pin selection retains its value and full operational World under the accounting projection. -/
theorem native (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    Stable project (RegistrationNativeServerPinRecompute.native (n := n) binding publicKey) := by
  intro before
  rw [RegistrationNativeServerPinRecompute.native_run, RegistrationNativeServerPinRecompute.native_run]
  simp only [map_pure, Prod.map, id_eq, idempotent]

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The actual pure source SDK pin call preserves accounting-input independence on packed Server/platform state. -/
theorem pin (coins : QueryImpl unifSpec (StateT Platform ProbComp)) :
    Stable (Prod.map RegistrationNativeMldsaCountServer.serverProject id)
      (RegistrationNativePlatformPackedState.pack (RegistrationNativePlatformSourceBuild.pin (n := n) coins)) := by
  rintro ⟨before, previous⟩
  have law := native (n := n) before.pin.binding before.pin.public_key before.world.world.1
  have interpreted := congrArg (fun work => simulateQ coins work) law
  simp only [simulateQ_map] at interpreted
  let restored (world : PqxdhRecordLiftWorld.State n) : RegistrationServerFrontendCompiler.State n :=
    { (RegistrationNativeMldsaCountServer.serverProject before) with world :=
      { (RegistrationNativeMldsaCountServer.serverProject before).world with world := (world, before.world.world.2) } }
  have same := congrArg (fun action => (fun result : (RegistrationNativeServerPinRecompute.PinReply × PqxdhRecordLiftWorld.State n) × Platform =>
    (result.1.1, (restored result.1.2, result.2))) <$> action.run previous) interpreted
  simpa only [RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformSourceBuild.pin,
    StateT.run, map_apply, Functor.map_map, Prod.map, id_eq, restored,
    RegistrationNativeMldsaCountServer.serverProject, RegistrationNativeMldsaCountServer.localProject] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformPinView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPinView.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPinView.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPinView.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPinView.pin
