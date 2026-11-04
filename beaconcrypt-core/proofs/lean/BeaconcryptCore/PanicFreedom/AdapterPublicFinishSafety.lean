-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationLoops

/-! Native first-record completion returns normally and installs only a populated ratchet slot. All rejected KDF, commitment and AEAD continuations return a non-established object. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.PanicFreedom.AdapterPublicFinishSafety
open Refinement AdapterNormal AdapterPublicRegistrationLoops
open beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations]
variable [authentication : beaconcrypt.auth.Operations] [recordOps : beaconcrypt.ratchet.Operations]
omit platform primitive crypto localOps authentication

abbrev Result := AdapterPublicFinishSourceLoop.Result

def ValidFinishedState (state : beacon.BeaconState) : Prop :=
  match state with
  | .Established _ _ manager => ∃ kernel, manager.refined.kernel = some kernel
  | _ => True

def BodyInvariant (decision : ControlFlow registration.BeaconInitialOpen Result) : Prop :=
  match decision with
  | .cont _ => True
  | .done result => ValidFinishedState result.2.2

local macro "normalize_leaves" : tactic => `(tactic|
  simp! only [
    registration.BeaconRecordCommitment.transcript_mut,
    registration.CompletedBeacon.into_parts,
    beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel,
    beaconcrypt_public_wrapper.ratchet.RatchetKernelSlot.new,
    PublicWrapperPlatform.assignedKeyId,
    alloc.slice.Slice.to_vec, AdapterPublicWrapperCopy.bytes,
    beaconcrypt_crypto.utils.memcmp,
    lift, beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes,
    beaconcrypt_crypto.crypto_sign.PublicKey.as_bytes,
    beaconcrypt_crypto.crypto_sign.sign,
    beaconcrypt_crypto.crypto_sign.ed25519_pk_to_curve25519,
    beaconcrypt_crypto.crypto_sign.ed25519_sk_to_curve25519,
    beaconcrypt_crypto.crypto_kx.PublicKey.as_bytes,
    beaconcrypt_crypto.crypto_kx.SecretKey.as_bytes,
    beaconcrypt_crypto.crypto_scalarmult.scalarmult,
    beaconcrypt_crypto.crypto_kx.KeyPair.generate_with_rng,
    beaconcrypt_crypto.crypto_kem.mlkem768.PublicKey.from_bytes,
    beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext.from_bytes,
    beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext.as_bytes,
    beaconcrypt_crypto.crypto_kem.mlkem768.SharedSecret.as_bytes,
    beaconcrypt_crypto.crypto_kem.mlkem768.encapsulate_with_rng,
    beaconcrypt_crypto.crypto_kem.mlkem768.decapsulate,
    beaconcrypt_crypto.crypto_kdf.hkdf.sha512.extract,
    beaconcrypt_crypto.crypto_kdf.hkdf.sha512.expand,
    beaconcrypt.auth.execute_hash, beaconcrypt.auth.verify_requested,
    beaconcrypt.ratchet.execute_commitment_hash, beaconcrypt.ratchet.execute_open_request,
    beaconcrypt.ratchet.ratchet_hkdf,
    zeroize.Zeroizing.new, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
    core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
    alloc.vec.Vec.as_slice, rust_primitives.sequence.seq_to_slice,
    core.result.Result.ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    core.option.Option.map, core.option.Option.and_then, core.option.Option.as_ref, core.option.Option.is_some,
    zeroize.P.Insts.CoreOpsFunctionFnOnceTupleZZeroizing,
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832,
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832,
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832,
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832,
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832,
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832,
    beacon.Beacon.identity_pk, beacon.Beacon.identity_sk,
    PqxdhRefinement.array_eq_abs, AdapterOptionDeref.byte_vector,
    bind_tc_ok])

local macro "finish_steps" contracts:term : tactic => `(tactic|
  repeat'
    try normalize_leaves
    first
      | with_reducible apply ensures_bind_at
      | with_reducible exact ($contracts).kdf _
      | with_reducible exact ($contracts).hash _
      | with_reducible exact ($contracts).aead _
      | with_reducible exact ($contracts).compare _ _
      | with_reducible exact RegistrationPublication.BeaconRecordKdf_request_total _
      | with_reducible exact RegistrationPublication.BeaconRecordKdf_resume_total _ _
      | with_reducible exact RegistrationPublication.BeaconRecordCommitment_transcript_mut_total _
      | with_reducible exact RegistrationPublication.BeaconRecordCommitment_supplied_commitment_total _
      | with_reducible exact RegistrationPublication.BeaconRecordCommitment_resume_total _ _
      | with_reducible exact RegistrationPublication.BeaconRecordAead_request_total _
      | with_reducible exact RegistrationPublication.BeaconRecordAead_finish_total _ _
      | with_reducible exact RegistrationTrivial.CompletedBeacon_into_parts_total _
      | with_reducible exact AdapterStandard.result_ok_total _
      | with_reducible exact AdapterStandard.option_branch_total _
      | (with_reducible apply AdapterStandard.option_residual_of_branch; assumption)
      | with_reducible exact AdapterStandard.option_ref_total _
      | with_reducible exact AdapterStandard.option_is_some_total _
      | with_reducible exact AdapterStandard.pair_pure_total _ _
      | with_reducible exact RecordEffects.RecordReceiveKdf_resume_total _ _
      | with_reducible exact RecordEffects.RecordReceiveCommitment_resume_total _ _
      | with_reducible exact RegistrationPublication.normalize_beacon_open_total _ _
      | with_reducible apply normal_bind_at
      | with_reducible exact normal_ok _
      | with_reducible apply ensures_ok
      | exact True.intro
      | (solve | exact ⟨_, rfl⟩)
      | (solve | simp_all [BodyInvariant, ValidFinishedState])
      | (rintro (⟨first, second, third⟩ : _ × _ × _))
      | (rintro (⟨first, second⟩ : _ × _))
      | (intro value)
      | (split)
      | (split at *))

theorem finish_body_preserves (contracts : AdapterRecordReceive.Contracts) (identifier : U64)
    (effect : registration.BeaconInitialOpen) :
    Ensures (beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body identifier effect)
      BodyInvariant := by
  cases effect <;> unfold beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body
  all_goals normalize_leaves
  all_goals finish_steps contracts
  all_goals exact True.intro

omit material platform primitive crypto localOps authentication recordOps in
private theorem loop_preserving {S A : Type} (body : S → RustM (ControlFlow S A))
    (rank : S → Nat) (invariant : A → Prop)
    (bodySafe : ∀ state, Ensures (body state) (fun decision => match decision with
      | .cont _ => True
      | .done result => invariant result))
    (progress : ∀ state next, body state = ok (.cont next) → rank next < rank state)
    (state : S) : Ensures (loop body state) invariant := by
  induction bound : rank state using Nat.strong_induction_on generalizing state with
  | h bound ih =>
    obtain ⟨decision, returned, valid⟩ := bodySafe state
    rw [loop.eq_def, returned]
    cases decision with
    | done result => exact ⟨result, rfl, valid⟩
    | cont next => exact ih (rank next) (by simpa only [bound] using progress state next returned) next rfl

theorem finish_body_total (contracts : AdapterRecordReceive.Contracts) (identifier : U64)
    (effect : registration.BeaconInitialOpen) :
    ∃ result, beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body
      identifier effect = ok result :=
  ensures_normal (finish_body_preserves contracts identifier effect)

theorem finish_loop_preserves (contracts : AdapterRecordReceive.Contracts)
    (effect : registration.BeaconInitialOpen) (identifier : U64) :
    ∃ result, beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop
      effect identifier = ok result ∧ ValidFinishedState result.2.2 := by
  exact loop_preserving _ BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.rank _
    (fun state => by
      obtain ⟨decision, returned, valid⟩ := finish_body_preserves contracts identifier state
      exact ⟨decision, returned, by cases decision <;> exact valid⟩)
    (AdapterPublicFinishSourceLoop.body_progress identifier) effect

theorem finish_loop_total (contracts : AdapterRecordReceive.Contracts)
    (effect : registration.BeaconInitialOpen) (identifier : U64) :
    ∃ result, beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop
      effect identifier = ok result :=
  ensures_normal (finish_loop_preserves contracts effect identifier)

end BeaconcryptCore.PanicFreedom.AdapterPublicFinishSafety
