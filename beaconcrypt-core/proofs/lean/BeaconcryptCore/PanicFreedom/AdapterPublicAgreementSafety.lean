-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationLoops

/-! Native agreement safety composes individual conversion, DH, KEM and KDF normal-return contracts with the existing source-derived strictly decreasing phase rank. Every ordinary dependency error remains covered. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.PanicFreedom.AdapterPublicAgreementSafety
open Refinement AdapterNormal AdapterPublicRegistrationLoops
open beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations]
variable [authentication : beaconcrypt.auth.Operations] [recordOps : beaconcrypt.ratchet.Operations]
omit platform localOps authentication recordOps

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
    core.option.Option.as_ref, core.option.Option.is_some,
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

local macro "agreement_safety_steps" contracts:term " with " random:term : tactic => `(tactic|
  repeat'
    try normalize_leaves
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
      | with_reducible exact ($random).encapsulate _ _
      | with_reducible exact ($contracts).decapsulate _ _
      | with_reducible exact ($contracts).extract _ _
      | with_reducible exact ($contracts).expand _ _ _
      | with_reducible exact ($random).kxGenerate _
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
      | with_reducible exact RegistrationTrivial.BeaconFingerprint_request_total _
      | with_reducible exact RegistrationTrivial.BeaconInitHash_request_total _
      | with_reducible exact RegistrationTrivial.BeaconMldsaSigning_request_total _
      | with_reducible exact RegistrationSigningContinuations.BeaconFingerprint_resume_total _ _
      | with_reducible exact RegistrationSigningContinuations.BeaconInitHash_resume_total _ _
      | with_reducible exact RegistrationSigningContinuations.BeaconMldsaSigning_resume_total _ _
      | with_reducible exact RegistrationInputs.copied_slice_total _ _
      | with_reducible exact AdapterStandard.result_ok_total _
      | with_reducible exact AdapterStandard.option_branch_total _
      | (with_reducible apply AdapterStandard.option_residual_of_branch; assumption)
      | with_reducible exact AdapterStandard.option_ref_total _
      | with_reducible exact AdapterStandard.option_is_some_total _
      | with_reducible exact agreement_closure_total ($contracts) _ _ _
      | with_reducible exact agreement_closure_1_total ($contracts) _ _ _
      | with_reducible exact agreement_closure_2_total ($contracts) _ ($random).toEncapsulationContracts _ _
      | with_reducible exact agreement_closure_3_total ($contracts) _ _ _
      | with_reducible exact agreement_closure_4_total ($contracts) _ _ _
      | with_reducible exact agreement_closure_5_total ($contracts) _ _ _
      | with_reducible exact agreement_closure_6_total ($contracts) _ _ _
      | with_reducible exact agreement_closure_7_total ($contracts) _ _ _
      | with_reducible exact agreement_root_closure_total ($contracts) _ _ _
      | with_reducible apply AdapterStandard.option_map_total
      | with_reducible apply AdapterStandard.option_and_then_total
      | with_reducible exact AdapterStandard.pair_pure_total _ _
      | with_reducible exact normal_ok _
      | (rintro (⟨first, second, third⟩ : _ × _ × _))
      | (rintro (⟨first, second⟩ : _ × _))
      | (intro value)
      | (split)
      | (split at *)
      | apply normal_bind_at)

theorem agreement_body_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (random : AgreementRngContracts rand_coreTryCryptoRngInst)
  (sk : beaconcrypt_crypto.crypto_sign.SecretKey)
  (o : core.option.Option beaconcrypt_crypto.crypto_kx.SecretKey)
  (o1 : core.option.Option beaconcrypt_crypto.crypto_kx.SecretKey)
  (o2 : core.option.Option beaconcrypt_crypto.crypto_kem.mlkem768.SecretKey)
  (effect : beaconcrypt_core.agreement.AgreementEffect) (rng : R)
  (local_identity : core.option.Option (zeroize.Zeroizing (Array Std.U8
  32#usize)))
  (server_ephemeral : core.option.Option beaconcrypt_crypto.crypto_kx.KeyPair) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop.body (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst sk o o1 o2 effect rng local_identity server_ephemeral = ok result := by
  cases effect <;> unfold beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop.body
  all_goals normalize_leaves
  all_goals agreement_safety_steps contracts with random
  case Encapsulate.later.later =>
    rename_i pending reply capture back called next resumed
    cases back capture
    exact ⟨_, rfl⟩

theorem execute_agreement_loop_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (random : AgreementRngContracts rand_coreTryCryptoRngInst)
  (effect : beaconcrypt_core.agreement.AgreementEffect)
  (sk : beaconcrypt_crypto.crypto_sign.SecretKey)
  (o : core.option.Option beaconcrypt_crypto.crypto_kx.SecretKey)
  (o1 : core.option.Option beaconcrypt_crypto.crypto_kx.SecretKey)
  (o2 : core.option.Option beaconcrypt_crypto.crypto_kem.mlkem768.SecretKey)
  (rng : R)
  (local_identity : core.option.Option (zeroize.Zeroizing (Array Std.U8
  32#usize)))
  (server_ephemeral : core.option.Option beaconcrypt_crypto.crypto_kx.KeyPair) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst effect sk o o1 o2 rng local_identity server_ephemeral = ok result := by
  exact normal_loop _
    (fun state : AdapterPublicAgreementSourceLoop.State R =>
      BeaconcryptCore.Computational.RegistrationAgreementExecutor.rank state.1)
    (fun state => agreement_body_total contracts rand_coreTryCryptoRngInst random sk o o1 o2
      state.1 state.2.1 state.2.2.1 state.2.2.2)
    (AdapterPublicAgreementSourceLoop.body_progress rand_coreTryCryptoRngInst ⟨sk, o, o1, o2⟩)
    (effect, rng, local_identity, server_ephemeral)

theorem execute_agreement_total (contracts : AgreementContracts) {R : Type} {Clause0_Clause0_Error : Type} (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (random : AgreementRngContracts rand_coreTryCryptoRngInst)
  (effect : beaconcrypt_core.agreement.AgreementEffect)
  (keys : pqxdh.RegistrationKeys) (rng : R) :
    ∃ result, beaconcrypt_public_wrapper.pqxdh.execute_agreement (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst effect keys rng = ok result :=
  execute_agreement_loop_total contracts rand_coreTryCryptoRngInst random effect
    keys.identity_secret keys.beacon_prekey keys.beacon_one_time keys.beacon_kem rng .None .None

theorem execute_beacon_agreement_total (contracts : AgreementContracts)
    (random : AgreementRngContracts pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError)
    (effect : agreement.AgreementEffect) (keys : pqxdh.RegistrationKeys) :
    ∃ result, pqxdh.execute_beacon_agreement effect keys = ok result := by
  obtain ⟨⟨result, rng⟩, returned⟩ := execute_agreement_total contracts
    pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError random effect keys ()
  exact ⟨result, by simp only [pqxdh.execute_beacon_agreement, returned, bind_tc_ok]; rfl⟩

end BeaconcryptCore.PanicFreedom.AdapterPublicAgreementSafety
