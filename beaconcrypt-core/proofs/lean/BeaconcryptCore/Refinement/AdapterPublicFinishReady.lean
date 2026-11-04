-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleBody
import BeaconcryptCore.Refinement.AdapterPublicWrapperCopy
/-! The actual extracted Beacon first-open body factors into its precise KDF, mutable commitment-hash, comparison, AEAD and application-copy/install continuation. Its source loop uses the actual remaining-KDF rank. All Rust failures, divergence, optional primitive replies, transcript writeback, assigned identifier and complete returned object fields remain literal monadic results. No primitive or whole-loop correspondence premise is used in the body equality. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishReady
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
open BeaconcryptCore.Computational
universe u v w
private theorem call_apply {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := m) source arg = call (m := m) (source arg) := rfl
private theorem call_result {m : Type → Type} [LiftRust m] {A : Type} (source : RustM A) :
    call (m := m) source = liftRust source := rfl
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl

variable [material : PublicWrapperPlatform.Material]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [children : ChildOperations (RustT m)]
abbrev Result := core.option.Option (alloc.vec.Vec U8) × U64 × beaconcrypt_public_wrapper.beacon.BeaconState

def resume (identifier : U64) (action : RustM (core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted)) :
    RustT m (ControlFlow registration.BeaconInitialOpen Result) := do
  let result ← liftRust action
  match result with
  | .Ok next => pure (.cont next)
  | .Err control => pure (.done (.None, identifier, .Aborted control))

def step (identifier : U64) (effect : registration.BeaconInitialOpen) :
    RustT m (ControlFlow registration.BeaconInitialOpen Result) := do
  match effect with
  | .KdfRequested pending =>
      let request ← liftRust pending.request
      let response ← children.ratchetHkdf request
      resume identifier (pending.resume (.Some response))
  | .CommitmentRequested pending =>
      let (transcript, back) ← liftRust pending.transcript_mut
      let (computed, after) ← children.commitmentHash transcript
      let pending := back after
      match computed with
      | .none => resume identifier (pending.resume false)
      | .some digest =>
          let supplied ← liftRust pending.supplied_commitment
          let matched ← children.compare (Array.to_slice digest) (Array.to_slice supplied)
          resume identifier (pending.resume matched)
  | .AeadRequested pending =>
      let request ← liftRust pending.request
      let plaintext ← children.openRequest request
      let borrowed ← liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) plaintext)
      let result ← liftRust (pending.finish borrowed)
      match result with
      | .Err control => pure (.done (.None, identifier, .Aborted control))
      | .Ok completed =>
          let installed ← liftRust (AdapterPublicWrapperCopy.install completed)
          pure (.done installed)

omit material children in
private theorem manager (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_request.ratchet.RatchetManager.from_kernel (m := RustT m) kernel =
      liftRust (beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel kernel) := by
  simp only [beaconcrypt_public_request.ratchet.RatchetManager.from_kernel,
    beaconcrypt_public_request.ratchet.RatchetKernelSlot.new, call_apply, call_result,
    lift_ok, pure_bind, beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel,
    beaconcrypt_public_wrapper.ratchet.RatchetKernelSlot.new, bind_tc_ok]

omit children in
private theorem install (completed : registration.CompletedBeacon) : (do
    let (control, binding, kernel, application) ← liftRust (registration.CompletedBeacon.into_parts completed)
    let plaintext ← liftRust (alloc.slice.Slice.to_vec core.U8.Insts.CoreCloneClone application)
    let identifier ← liftRust (PublicWrapperPlatform.assignedKeyId binding)
    let manager ← beaconcrypt_public_request.ratchet.RatchetManager.from_kernel (m := RustT m) kernel
    pure (some plaintext, identifier, beaconcrypt_public_wrapper.beacon.BeaconState.Established control binding manager)) =
    (liftRust (AdapterPublicWrapperCopy.install completed) : RustT m Result) := by
  rw [AdapterPublicWrapperCopy.install_exact]
  simp only [registration.CompletedBeacon.into_parts, lift_ok, pure_bind, alloc.slice.Slice.to_vec,
    AdapterPublicWrapperCopy.bytes, PublicWrapperPlatform.assignedKeyId, manager,
    beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel,
    beaconcrypt_public_wrapper.ratchet.RatchetKernelSlot.new, bind_tc_ok]

theorem body_source (identifier : U64) (effect : registration.BeaconInitialOpen) :
    beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body
      (m := RustT m) identifier effect = step (m := m) identifier effect := by
  cases effect with
  | KdfRequested pending =>
      simp only [beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body,
        step, resume, call_apply, call_result, lift_ok]
      rfl
  | CommitmentRequested pending =>
      simp only [beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body,
        step, resume, call_apply, call_result, lift_ok]
      apply bind_congr
      intro transcript
      rcases transcript with ⟨transcript, back⟩
      apply bind_congr
      intro computed
      rcases computed with ⟨computed, after⟩
      cases computed with
      | none => rfl
      | some digest =>
          simp only [Aeneas.Std.lift, lift_ok, pure_bind]
          rfl
  | AeadRequested pending =>
      simp only [beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body,
        step, call_apply, call_result, lift_ok]
      apply bind_congr
      intro request
      apply bind_congr
      intro plaintext
      apply bind_congr
      intro borrowed
      apply bind_congr
      intro result
      cases result with
      | Err control => rfl
      | Ok completed =>
          simp only
          rw [← install]
          simp only [bind_assoc, pure_bind]

theorem loop_source (effect : registration.BeaconInitialOpen) (identifier : U64) :
    beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop
      (m := RustT m) effect identifier =
      AdapterPublicWrapperLiftFunction.loopFuel (RegistrationBeaconRecordExecutor.rank effect + 1) (step identifier) effect := by
  unfold beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop
  simp only [body_source]
end BeaconcryptCore.Refinement.AdapterPublicFinishReady

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishReady.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishReady.body_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishReady.loop_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishReady.loop_source
