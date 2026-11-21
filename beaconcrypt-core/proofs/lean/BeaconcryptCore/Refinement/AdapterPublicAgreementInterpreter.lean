-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementFields
import BeaconcryptCore.Computational.RegistrationAgreementSourceFuel
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The original agreement request interpreter retains the source RNG, converted zeroizing identity and actual ephemeral private object. Its leaves are the proved source callbacks, not a contract for the whole executor. Rust failures stop the continuation and retain every already reached effect in the arbitrary base monad. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open AdapterPublicAgreementFields (Array32 LocalIdentity KeyPair Keys)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]

structure Capture (R : Type) where
  rng : R
  localIdentity : core.option.Option LocalIdentity
  ephemeral : core.option.Option KeyPair

noncomputable def handler {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys) :
    QueryImpl Spec (StateT (Capture R) (RustT m))
  | .convertPublic key => StateT.lift (AdapterPublicAgreementFields.convertPublic key)
  | .convertSecret _ => do
    let stored ← StateT.lift (AdapterPublicAgreementFields.convertSecret keys.identity_secret)
    modify fun before => { before with localIdentity := stored }
    StateT.lift (liftRust (core.option.Option.is_some stored))
  | .generate _ => do
    let before ← get
    let (reply, stored, nextRng) ← StateT.lift (AdapterPublicAgreementFields.generate generator before.rng)
    set { before with rng := nextRng, ephemeral := stored }
    pure reply
  | .encapsulate key => do
    let before ← get
    let (reply, nextRng) ← StateT.lift (AdapterPublicAgreementFields.encapsulate generator key before.rng)
    set { before with rng := nextRng }
    pure reply
  | .decapsulate ciphertext => StateT.lift (AdapterPublicAgreementFields.decapsulate ciphertext keys.beacon_kem)
  | .dh request => do
    let before ← get
    StateT.lift (AdapterPublicAgreementFields.dh generator keys before.localIdentity before.ephemeral request)
  | .root request => StateT.lift (AdapterPublicAgreementFields.root request)

noncomputable def next {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (phase : agreement.AgreementEffect) : StateT (Capture R) (RustT m) agreement.AgreementEffect := do
  let result ← simulateQ (handler generator keys) (step phase)
  StateT.lift (liftRust result)

noncomputable def control {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (state : AdapterPublicAgreementFields.State R) : RustT m (AdapterPublicAgreementFields.Exit R) := do
  let (phase, rng, localIdentity, ephemeral) := state
  let (after, captured) ← (next generator keys phase).run ⟨rng, localIdentity, ephemeral⟩
  pure (if rank phase = 0 then .done (after, captured.rng)
    else .cont (after, captured.rng, captured.localIdentity, captured.ephemeral))

omit material primitive [LawfulMonad m] crypto in
private theorem lift_ok {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl

noncomputable section

theorem body {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (state : AdapterPublicAgreementFields.State R) :
    AdapterPublicAgreementFields.body (m := m) generator keys state = control (m := m) generator keys state := by
  rcases state with ⟨phase, rng, localIdentity, ephemeral⟩
  cases phase with
  | Rejected aborted | ServerComplete completed | BeaconComplete completed =>
    simp only [AdapterPublicAgreementFields.body, control, next, step, rank,
      simulateQ_pure,   StateT.run_lift,
      pure_bind, lift_ok, bind_pure_comp, map_pure, ↓reduceIte]
  | ConvertPublic pending =>
    have nonterminal : rank (.ConvertPublic pending) ≠ 0 := by simp [rank]
    obtain ⟨key, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_key_total pending
    simp only [AdapterPublicAgreementFields.body, control, next, step, requested, continueWith,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, handler,
      StateT.run_bind,  StateT.run_lift, pure_bind,
      lift_ok, ite_eq_right nonterminal, bind_assoc]
    apply bind_congr
    intro reply
    rfl
  | ConvertSecret pending =>
    have nonterminal : rank (.ConvertSecret pending) ≠ 0 := by simp [rank]
    obtain ⟨role, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_role_total pending
    simp only [AdapterPublicAgreementFields.body, control, next, step, requested, continueWith,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, handler,
      StateT.run_bind,  StateT.run_lift, StateT.run_modify,
      pure_bind,  ite_eq_right nonterminal, bind_assoc]
    apply bind_congr
    intro stored
    apply bind_congr
    intro success
    rfl
  | GenerateEphemeral pending =>
    have nonterminal : rank (.GenerateEphemeral pending) ≠ 0 := by simp [rank]
    obtain ⟨role, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_role_total pending
    simp only [AdapterPublicAgreementFields.body, control, next, step, requested, continueWith,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, handler,
      StateT.run_bind,  StateT.run_lift, StateT.run_get, StateT.run_set,
      pure_bind,  ite_eq_right nonterminal, bind_assoc]
  | Encapsulate pending =>
    have nonterminal : rank (.Encapsulate pending) ≠ 0 := by simp [rank]
    obtain ⟨key, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_key_total pending
    simp only [AdapterPublicAgreementFields.body, control, next, step, requested, continueWith,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, handler,
      StateT.run_bind,  StateT.run_lift, StateT.run_get, StateT.run_set,
      pure_bind, lift_ok, ite_eq_right nonterminal, bind_assoc]
  | Decapsulate pending =>
    have nonterminal : rank (.Decapsulate pending) ≠ 0 := by simp [rank]
    obtain ⟨ciphertext, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_ciphertext_total pending
    simp only [AdapterPublicAgreementFields.body, control, next, step, requested, continueWith,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, handler,
      StateT.run_bind,  StateT.run_lift, pure_bind,
      lift_ok, ite_eq_right nonterminal, bind_assoc]
    apply bind_congr
    intro reply
    rfl
  | Dh pending =>
    have nonterminal : rank (.Dh pending) ≠ 0 := by
      cases position : pending.position <;> simp [rank, position]
    obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.dh_request_total pending
    simp only [AdapterPublicAgreementFields.body, control, next, step, requested, continueWith,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, handler,
      StateT.run_bind,  StateT.run_lift, StateT.run_get, pure_bind, lift_ok, ite_eq_right nonterminal, bind_assoc]
    apply bind_congr
    intro reply
    rfl
  | RootKdf pending =>
    have nonterminal : rank (.RootKdf pending) ≠ 0 := by simp [rank]
    obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_request_total pending
    simp only [AdapterPublicAgreementFields.body, control, next, step, requested, continueWith,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, handler,
      StateT.run_bind,  StateT.run_lift, pure_bind,
      lift_ok, ite_eq_right nonterminal, bind_assoc]
    apply bind_congr
    intro reply
    rfl
noncomputable def runLoop {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (fuel : Nat) (phase : agreement.AgreementEffect) (before : Capture R) : RustT m (agreement.AgreementEffect × R) := do
  let (result, after) ← (simulateQ (handler generator keys) (RegistrationAgreementSourceFuel.loop fuel phase)).run before
  let completed ← liftRust result
  pure (completed, after.rng)

theorem loop {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (fuel : Nat) (phase : agreement.AgreementEffect) (before : Capture R) :
    AdapterPublicWrapperLiftFunction.loopFuel fuel (control (m := m) generator keys)
      (phase, before.rng, before.localIdentity, before.ephemeral) =
      runLoop generator keys fuel phase before := by
  induction fuel generalizing phase before with
  | zero =>
    apply RustT.ext
    simp only [AdapterPublicWrapperLiftFunction.loopFuel, runLoop, RegistrationAgreementSourceFuel.loop,
      simulateQ_pure, StateT.run_pure, RustT.run_bind, RustT.run_pure,
      RustT.run_liftRust, pure_bind]
  | succ fuel ih =>
    by_cases zero : rank phase = 0
    · have terminal := RegistrationAgreementSourceFuel.zero_terminal phase zero
      cases terminal <;>
        simp only [AdapterPublicWrapperLiftFunction.loopFuel, control, next,
          runLoop, RegistrationAgreementSourceFuel.loop, rank, step, simulateQ_pure,
           StateT.run_pure, StateT.run_lift, lift_ok, pure_bind, ↓reduceIte]
    · simp only [AdapterPublicWrapperLiftFunction.loopFuel, control, next, runLoop,
        RegistrationAgreementSourceFuel.loop, ite_eq_right zero,
        simulateQ_bind, StateT.run_bind, StateT.run_lift,
        bind_assoc]
      apply bind_congr
      rintro ⟨result, after⟩
      cases result with
      | fail error =>
        apply RustT.ext
        simp only [continueWith, simulateQ_pure, StateT.run_pure,
          RustT.run_bind, RustT.run_pure, RustT.run_liftRust, pure_bind]
      | div =>
        apply RustT.ext
        simp only [continueWith, simulateQ_pure, StateT.run_pure,
          RustT.run_bind, RustT.run_pure, RustT.run_liftRust, pure_bind]
      | ok completed =>
        simp only [lift_ok, pure_bind, continueWith]
        exact ih completed after

noncomputable def runDrive {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (phase : agreement.AgreementEffect) (rng : R) : RustT m (agreement.AgreementEffect × R) := do
  let (result, after) ← (simulateQ (handler generator keys) (drive 9 phase)).run ⟨rng, .None, .None⟩
  let completed ← liftRust result
  pure (completed, after.rng)

theorem execute_source {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (phase : agreement.AgreementEffect) (rng : R) :
    beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT m) generator phase keys rng =
      runLoop generator keys (rank phase + 1) phase ⟨rng, .None, .None⟩ := by
  unfold beaconcrypt_public_request.pqxdh.execute_agreement
    beaconcrypt_public_request.pqxdh.execute_agreement_loop
  have same : (fun state : AdapterPublicAgreementFields.State R =>
      beaconcrypt_public_request.pqxdh.execute_agreement_loop.body (m := RustT m) generator
        keys.identity_secret keys.beacon_prekey keys.beacon_one_time keys.beacon_kem
        state.1 state.2.1 state.2.2.1 state.2.2.2) = control (m := m) generator keys := by
    funext state
    exact (AdapterPublicAgreementFields.body_source generator keys state).trans (body generator keys state)
  rw [same]
  exact loop generator keys _ phase ⟨rng, .None, .None⟩

theorem execute_nine {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (phase : agreement.AgreementEffect) (rng : R) (bounded : rank phase ≤ 9) :
    beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT m) generator phase keys rng =
      runDrive generator keys phase rng := by
  rw [execute_source]
  unfold runLoop runDrive
  rw [RegistrationAgreementSourceFuel.nine phase bounded]

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter.body

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter.loop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter.loop

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter.execute_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter.execute_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter.execute_nine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter.execute_nine
