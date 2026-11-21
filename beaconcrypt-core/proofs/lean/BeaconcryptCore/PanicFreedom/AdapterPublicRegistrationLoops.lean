-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterNormal
import BeaconcryptCore.PanicFreedom.AdapterStandard
import BeaconcryptCore.PanicFreedom.RegistrationSigning
import BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
import BeaconcryptCore.PanicFreedom.RegistrationPublication
import BeaconcryptCore.PanicFreedom.KeyAgreement
import BeaconcryptCore.Refinement.AdapterOptionDeref
import BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop
import BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop
import BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop

/-! Native safety of the three public registration loops and their actual callbacks. The termination ranks are the existing source-derived ranks, with ordinary dependency errors and protocol rejections retained. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationLoops
open Refinement AdapterNormal
open beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations]
variable [authentication : beaconcrypt.auth.Operations]

/-! These contracts contain only the leaves used by each source cohort. RNG contracts select one dictionary and cover every state of that dictionary, including ordinary entropy errors. No conclusion about an arbitrary RNG callback is assumed. -/
structure InitContracts : Prop where
  hash : ∀ request, Normal (authentication.hash request)
  edPublicBytes : ∀ key, Normal (crypto.edPublicBytes key)
  edSign : ∀ message key, Normal (crypto.edSign message key)

structure AgreementContracts : Prop where
  parse : ∀ input, Normal (primitive.parse input)
  kxPublicBytes : ∀ key, Normal (crypto.kxPublicBytes key)
  kxSecretBytes : ∀ key, Normal (crypto.kxSecretBytes key)
  convertPublic : ∀ key, Normal (crypto.convertPublic key)
  convertSecret : ∀ key, Normal (crypto.convertSecret key)
  scalarMult : ∀ secret key, Normal (crypto.scalarMult secret key)
  kemPublicFromBytes : ∀ bytes, Normal (crypto.kemPublicFromBytes bytes)
  kemCipherFromBytes : ∀ bytes, Normal (crypto.kemCipherFromBytes bytes)
  kemCipherBytes : ∀ value, Normal (crypto.kemCipherBytes value)
  kemSharedBytes : ∀ value, Normal (crypto.kemSharedBytes value)
  decapsulate : ∀ ciphertext key, Normal (crypto.decapsulate ciphertext key)
  extract : ∀ salt input, Normal (crypto.extract salt input)
  expand : ∀ length info key, Normal (crypto.expand length info key)

structure GenerationContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop where
  kxGenerate : ∀ rng, Normal (crypto.kxGenerate generator rng)

structure EncapsulationContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop where
  encapsulate : ∀ key rng, Normal (crypto.encapsulate generator key rng)

structure AgreementRngContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop extends GenerationContracts generator, EncapsulationContracts generator

local macro "normalize_leaves" : tactic => `(tactic|
  simp! only [
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

local macro "safety_steps" contracts:term : tactic => `(tactic|
  repeat'
    try simp only [bind_tc_ok]
    first
      | with_reducible apply normal_bind_at
      | (solve | simp_all)
      | with_reducible exact ($contracts).parse _
      | with_reducible exact ($contracts).kxPublicBytes _
      | with_reducible exact ($contracts).kxSecretBytes _
      | with_reducible exact ($contracts).convertPublic _
      | with_reducible exact ($contracts).convertSecret _
      | with_reducible exact ($contracts).scalarMult _ _
      | with_reducible exact ($contracts).kemPublicFromBytes _
      | with_reducible exact ($contracts).kemCipherFromBytes _
      | with_reducible exact ($contracts).kemCipherBytes _
      | with_reducible exact ($contracts).kemSharedBytes _
      | with_reducible exact ($contracts).decapsulate _ _
      | with_reducible exact ($contracts).extract _ _
      | with_reducible exact ($contracts).expand _ _ _
      | with_reducible exact KeyAgreement.root_kdf_request_total _
      | with_reducible exact KeyAgreement.encapsulation_key_total _
      | with_reducible exact KeyAgreement.decapsulation_ciphertext_total _
      | with_reducible exact KeyAgreement.public_conversion_key_total _
      | with_reducible exact KeyAgreement.public_conversion_resume_total _ _
      | with_reducible exact KeyAgreement.secret_conversion_resume_total _ _
      | with_reducible exact KeyAgreement.ephemeral_resume_total _ _
      | with_reducible exact KeyAgreement.encapsulation_resume_total _ _
      | with_reducible exact KeyAgreement.decapsulation_resume_total _ _
      | with_reducible exact KeyAgreement.dh_request_total _
      | with_reducible exact KeyAgreement.dh_resume_total _ _
      | with_reducible exact KeyAgreement.root_kdf_resume_total _ _
      | with_reducible exact RegistrationSigning.ed_request_total _
      | with_reducible exact RegistrationSigning.ed_resume_total _ _
      | with_reducible exact RegistrationTrivial.BeaconInitHash_request_total _
      | with_reducible exact RegistrationSigningContinuations.BeaconInitHash_resume_total _ _
      | with_reducible exact RegistrationInputs.copied_slice_total _ _
      | with_reducible exact AdapterStandard.result_ok_total _
      | with_reducible exact AdapterStandard.option_branch_total _
      | (with_reducible apply AdapterStandard.option_residual_of_branch; assumption)
      | with_reducible exact AdapterStandard.option_ref_total _
      | with_reducible exact AdapterStandard.option_is_some_total _
      | with_reducible exact normal_ok _
      | (intro value)
      | (split)
      | (split at *)
      | apply normal_bind_at)

section AgreementClosures
omit platform localOps authentication

theorem agreement_root_closure_total (contracts : AgreementContracts)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (capture : pqxdh.execute_agreement.closure_8 R E) (argument : Unit) :
    ∃ result, pqxdh.execute_agreement.closure_8.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call
      generator capture argument = ok result := by
  unfold pqxdh.execute_agreement.closure_8.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call
  normalize_leaves
  safety_steps contracts

theorem agreement_closure_7_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_7 R Clause0_Clause0_Error)
  (tupled_args : beaconcrypt_crypto.crypto_kx.SecretKey) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args = ok result := by
  unfold beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once
  normalize_leaves
  safety_steps contracts

theorem agreement_closure_6_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_6 R Clause0_Clause0_Error)
  (tupled_args : beaconcrypt_crypto.crypto_kx.SecretKey) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args = ok result := by
  unfold beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once
  normalize_leaves
  safety_steps contracts

theorem agreement_closure_5_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_5 R Clause0_Clause0_Error)
  (tupled_args : beaconcrypt_crypto.crypto_kx.KeyPair) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args = ok result := by
  unfold beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832.call_once
  normalize_leaves
  safety_steps contracts

theorem agreement_closure_4_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_4 R Clause0_Clause0_Error)
  (tupled_args : zeroize.Zeroizing (Array Std.U8 32#usize)) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args = ok result := by
  unfold beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832.call_once
  normalize_leaves
  safety_steps contracts

theorem agreement_closure_3_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_3 R Clause0_Clause0_Error) (adapter_unit_argument : Unit) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_3.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c adapter_unit_argument = ok result := by
  rcases c with ⟨captured, retained⟩
  unfold beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_3.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call
  normalize_leaves
  safety_steps contracts

theorem agreement_closure_2_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (random : EncapsulationContracts rand_coreTryCryptoRngInst)
  (c : pqxdh.execute_agreement.closure_2 R Clause0_Clause0_Error) (adapter_unit_argument : Unit) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_2.Insts.CoreOpsFunctionFnMutTupleOptionPairArrayU81088ArrayU832.call_mut (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst c adapter_unit_argument = ok result := by
  rcases c with ⟨captured, retained⟩
  unfold beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_2.Insts.CoreOpsFunctionFnMutTupleOptionPairArrayU81088ArrayU832.call_mut
  normalize_leaves
  safety_steps contracts
  all_goals exact random.encapsulate _ _

theorem agreement_closure_1_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (_c : pqxdh.execute_agreement.closure_1 R Clause0_Clause0_Error)
  (tupled_args : beaconcrypt_crypto.crypto_kx.KeyPair) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst _c tupled_args = ok result := by
  unfold beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832.call_once
  normalize_leaves
  safety_steps contracts

theorem agreement_closure_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (_c : pqxdh.execute_agreement.closure R Clause0_Clause0_Error)
  (tupled_args : beaconcrypt_crypto.crypto_sign.PublicKey) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst _c tupled_args = ok result := by
  unfold beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832.call_once
  normalize_leaves
  safety_steps contracts

end AgreementClosures

omit platform localOps in
theorem init_ready_body_total (contracts : InitContracts)
    (beacon1 : beacon.Beacon) (effect : registration.BeaconInitEffect) :
    ∃ result, beacon._proof_beacon_init_ready_loop.body beacon1 effect = ok result := by
  cases effect <;> unfold beacon._proof_beacon_init_ready_loop.body
  all_goals normalize_leaves
  all_goals
    repeat'
      first
        | with_reducible exact contracts.hash _
        | with_reducible exact contracts.edPublicBytes _
        | with_reducible exact contracts.edSign _ _
        | safety_steps contracts

omit platform localOps in
theorem init_ready_loop_total (contracts : InitContracts)
    (effect : registration.BeaconInitEffect) (beacon1 : beacon.Beacon) :
    ∃ result, beacon._proof_beacon_init_ready_loop effect beacon1 = ok result := by
  exact normal_loop _ AdapterPublicInitSourceLoop.rank (init_ready_body_total contracts beacon1)
    (AdapterPublicInitSourceLoop.body_progress beacon1) effect

omit platform localOps in
theorem init_ready_total (contracts : InitContracts)
    (beacon1 : beacon.Beacon) (effect : registration.BeaconInitEffect) :
    ∃ result, beacon._proof_beacon_init_ready beacon1 effect = ok result :=
  init_ready_loop_total contracts effect beacon1

end BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationLoops
