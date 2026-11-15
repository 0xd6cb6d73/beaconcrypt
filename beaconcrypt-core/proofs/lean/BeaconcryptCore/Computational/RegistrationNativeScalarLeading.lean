-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarSource

/-! The optional constructor prefix uses only ordinary World effects. Its literal effect program retains all pre-scalar failure branches and source callback order, allowing an independent private scalar draw to move past it. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarLeading
open RegistrationNativeBeaconFrontend (Prepared)
variable {n : Nat} {KemSK Value : Type}

noncomputable def program (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    OracleComp (PqxdhRecordLiftInterface.EnvEffects n) (RustM (Option (Prepared source))) := do
  match registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok pin => do
    let identity ← simulateQ RegistrationWorldCoinCompiler.envCoin PqxdhJointIdentity.sampleSeed
    pure (.ok (some ⟨pin, identity, RegistrationNativePublicOwners.dummy⟩))

private theorem sample_program {source : RegistrationNativeMldsa.Source} (draw : ProbComp Value) :
    simulateQ (RegistrationNativeBeaconFrontend.effect (n := n) (KemSK := KemSK)
      (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State))
      (simulateQ RegistrationWorldCoinCompiler.envCoin draw) = RegistrationNativeBeaconFrontend.sample draw := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeBeaconFrontend.effect (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := RegistrationServerRoleBackend.State) ∘ₛ RegistrationWorldCoinCompiler.envCoin =
      (fun query => RegistrationNativeBeaconFrontend.effect (.inl query)) := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationWorldCoinCompiler.envCoin, simulateQ_spec_query]
  rw [same]
  rfl

/-- Every actual pre-scalar constructor branch is the literal shared-World effect program, with no private KEM or root interaction. -/
theorem leading (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativeScalarPreparation.leading (n := n) (KemSK := KemSK)
      (Auxiliary := RegistrationServerRoleBackend.State) source edPin mlPin keyId =
      simulateQ RegistrationNativeBeaconFrontend.effect (program source edPin mlPin keyId) := by
  unfold RegistrationNativeScalarPreparation.leading program
  cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | fail error | div => simp only [simulateQ_pure]
  | ok pin => simp only [simulateQ_bind, sample_program, simulateQ_pure]

end BeaconcryptCore.Computational.RegistrationNativeScalarLeading

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarLeading.leading' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarLeading.leading
