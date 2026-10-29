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
  let generated ← simulateQ RegistrationWorldCoinCompiler.envCoin (RegistrationNativeMldsa.generate source)
  match generated with
  | none => pure (.ok none)
  | some credentials =>
    match registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok pending => match pending.request with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok request => do
        let digest ← (PqxdhRecordLiftInterface.EnvEffects n).query (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))
        match pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
        | .fail error => pure (.fail error)
        | .div => pure .div
        | .ok .None => pure (.ok none)
        | .ok (.Some pin) => do
          let identity ← simulateQ RegistrationWorldCoinCompiler.envCoin PqxdhJointIdentity.sampleSeed
          pure (.ok (some ⟨credentials, pin, identity, RegistrationNativePublicOwners.dummy⟩))

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
  simp only [RegistrationNativeScalarPreparation.leading, program, simulateQ_bind, sample_program]
  apply congrArg (fun continuation => (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK)
    (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State)
    (RegistrationNativeMldsa.generate source) >>= continuation))
  funext generated
  cases generated with
  | none => simp only [simulateQ_pure]
  | some credentials =>
      cases initial : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error => simp only [simulateQ_pure]
      | div => simp only [simulateQ_pure]
      | ok pending =>
          cases requested : pending.request with
          | fail error => simp only [requested, simulateQ_pure]
          | div => simp only [requested, simulateQ_pure]
          | ok request =>
              simp only [requested, simulateQ_bind, simulateQ_spec_query]
              apply congrArg (fun continuation => (RegistrationNativeBeaconFrontend.hash (n := n) (KemSK := KemSK)
                (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State) request >>= continuation))
              funext digest
              cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
              | fail error => simp only [simulateQ_pure]
              | div => simp only [simulateQ_pure]
              | ok outcome =>
                  cases outcome with
                  | none => simp only [simulateQ_pure]
                  | some pin => simp only [simulateQ_bind, sample_program, simulateQ_pure]

end BeaconcryptCore.Computational.RegistrationNativeScalarLeading

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarLeading.leading' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarLeading.leading
