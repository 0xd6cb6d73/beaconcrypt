-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterNormal
import BeaconcryptCore.PanicFreedom.AdapterStandard
import BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage

/-! Direct RustM safety for the actual Beacon agreement entry. Covered phases exclude generation and encapsulation. Every actual native continuation decreases the existing source rank, retaining coverage without interpreting a request tree. The unused entropy operations may fail or diverge. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.PanicFreedom.AdapterBeaconAgreementSafety
open Refinement AdapterNormal beaconcrypt_public_wrapper
open BeaconcryptCore.Computational
open BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage (Covered)
variable [material : PublicWrapperPlatform.Material]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]

structure Contracts : Prop where
  parse : ∀ input, Normal (primitive.parse input)
  kxSecretBytes : ∀ key, Normal (crypto.kxSecretBytes key)
  convertPublic : ∀ key, Normal (crypto.convertPublic key)
  convertSecret : ∀ key, Normal (crypto.convertSecret key)
  scalarMult : ∀ secret key, Normal (crypto.scalarMult secret key)
  kemCipherFromBytes : ∀ bytes, Normal (crypto.kemCipherFromBytes bytes)
  kemSharedBytes : ∀ value, Normal (crypto.kemSharedBytes value)
  decapsulate : ∀ ciphertext key, Normal (crypto.decapsulate ciphertext key)
  extract : ∀ salt input, Normal (crypto.extract salt input)
  expand : ∀ length info key, Normal (crypto.expand length info key)

local macro "normalize_beacon_leaves" : tactic => `(tactic|
  simp! only [
    lift, beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes,
    beaconcrypt_crypto.crypto_sign.ed25519_pk_to_curve25519,
    beaconcrypt_crypto.crypto_sign.ed25519_sk_to_curve25519,
    beaconcrypt_crypto.crypto_kx.SecretKey.as_bytes,
    beaconcrypt_crypto.crypto_scalarmult.scalarmult,
    beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext.from_bytes,
    beaconcrypt_crypto.crypto_kem.mlkem768.SharedSecret.as_bytes,
    beaconcrypt_crypto.crypto_kem.mlkem768.decapsulate,
    beaconcrypt_crypto.crypto_kdf.hkdf.sha512.extract,
    beaconcrypt_crypto.crypto_kdf.hkdf.sha512.expand,
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
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832,
    pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832.call_once,
    pqxdh.execute_agreement.closure_3.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call,
    pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832.call_once,
    pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832.call_once,
    pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once,
    pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once,
    pqxdh.execute_agreement.closure_8.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call,
    bind_tc_ok])

local macro "beacon_safety_steps" contracts:term : tactic => `(tactic|
  repeat'
    try normalize_beacon_leaves
    first
      | with_reducible apply normal_bind_at
      | (solve | simp_all)
      | with_reducible exact ($contracts).parse _
      | with_reducible exact ($contracts).kxSecretBytes _
      | with_reducible exact ($contracts).convertPublic _
      | with_reducible exact ($contracts).convertSecret _
      | with_reducible exact ($contracts).scalarMult _ _
      | with_reducible exact ($contracts).kemCipherFromBytes _
      | with_reducible exact ($contracts).kemSharedBytes _
      | with_reducible exact ($contracts).decapsulate _ _
      | with_reducible exact ($contracts).extract _ _
      | with_reducible exact ($contracts).expand _ _ _
      | with_reducible exact KeyAgreement.root_kdf_request_total _
      | with_reducible exact KeyAgreement.decapsulation_ciphertext_total _
      | with_reducible exact KeyAgreement.public_conversion_key_total _
      | with_reducible exact KeyAgreement.public_conversion_resume_total _ _
      | with_reducible exact KeyAgreement.secret_conversion_resume_total _ _
      | with_reducible exact KeyAgreement.decapsulation_resume_total _ _
      | with_reducible exact KeyAgreement.dh_request_total _
      | with_reducible exact KeyAgreement.dh_resume_total _ _
      | with_reducible exact KeyAgreement.root_kdf_resume_total _ _
      | with_reducible exact RegistrationInputs.copied_slice_total _ _
      | with_reducible exact AdapterStandard.result_ok_total _
      | with_reducible exact AdapterStandard.option_branch_total _
      | (with_reducible apply AdapterStandard.option_residual_of_branch; assumption)
      | with_reducible exact AdapterStandard.option_ref_total _
      | with_reducible exact AdapterStandard.option_is_some_total _
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

theorem body_total (contracts : Contracts) {R E : Type}
    (generator : rand_core.TryCryptoRng R E) (keys : pqxdh.RegistrationKeys)
    (state : AdapterPublicAgreementSourceLoop.State R) (covered : Covered state.1) :
    Normal (AdapterPublicAgreementSourceLoop.body generator keys state) := by
  rcases state with ⟨effect, rng, localIdentity, serverEphemeral⟩
  cases effect with
  | GenerateEphemeral pending =>
    have bound := covered.1
    simp only [RegistrationAgreementExecutor.rank] at bound
    omega
  | Encapsulate pending => exact False.elim (covered.2 pending rfl)
  | Rejected _ | ServerComplete _ | BeaconComplete _
  | ConvertPublic _ | ConvertSecret _ | Decapsulate _ | Dh _ | RootKdf _ =>
    unfold AdapterPublicAgreementSourceLoop.body pqxdh.execute_agreement_loop.body
    normalize_beacon_leaves
    beacon_safety_steps contracts

theorem body_preserves {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : pqxdh.RegistrationKeys) (before after : AdapterPublicAgreementSourceLoop.State R)
    (covered : Covered before.1)
    (actual : AdapterPublicAgreementSourceLoop.body generator keys before = ok (.cont after)) :
    Covered after.1 := by
  apply RegistrationAgreementBeaconCoverage.under_eight
  exact Nat.lt_of_lt_of_le
    (AdapterPublicAgreementSourceLoop.body_progress generator keys before after actual) covered.1

theorem loop_total (contracts : Contracts) {R E : Type}
    (generator : rand_core.TryCryptoRng R E) (keys : pqxdh.RegistrationKeys)
    (state : AdapterPublicAgreementSourceLoop.State R) (covered : Covered state.1) :
    Normal (loop (AdapterPublicAgreementSourceLoop.body generator keys) state) := by
  induction bound : RegistrationAgreementExecutor.rank state.1 using Nat.strong_induction_on generalizing state with
  | h bound ih =>
    obtain ⟨decision, returned⟩ := body_total contracts generator keys state covered
    rw [loop.eq_def, returned]
    cases decision with
    | done result => exact normal_ok result
    | cont next =>
      have smaller := AdapterPublicAgreementSourceLoop.body_progress generator keys state next returned
      exact ih (RegistrationAgreementExecutor.rank next.1) (by simpa only [bound] using smaller)
        next (body_preserves generator keys state next covered returned) rfl

theorem execute_agreement_covered_total (contracts : Contracts) {R E : Type}
    (generator : rand_core.TryCryptoRng R E) (effect : agreement.AgreementEffect)
    (keys : pqxdh.RegistrationKeys) (rng : R) (covered : Covered effect) :
    Normal (pqxdh.execute_agreement generator effect keys rng) :=
  loop_total contracts generator keys (effect, rng, none, none) covered

theorem execute_beacon_agreement_covered_total (contracts : Contracts)
    (effect : agreement.AgreementEffect) (keys : pqxdh.RegistrationKeys) (covered : Covered effect) :
    Normal (pqxdh.execute_beacon_agreement effect keys) := by
  obtain ⟨⟨result, rng⟩, returned⟩ := execute_agreement_covered_total contracts
    pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError effect keys () covered
  exact ⟨result, by simp only [pqxdh.execute_beacon_agreement, returned, bind_tc_ok]; rfl⟩

/-- Coverage follows from the actual core entry result, including core rejection. -/
theorem execute_beacon_agreement_entry_total (contracts : Contracts)
    (authenticated : registration.AuthenticatedResponse) (initial : agreement.AgreementEffect)
    (keys : pqxdh.RegistrationKeys)
    (started : agreement.begin_beacon_agreement authenticated = ok initial) :
    Normal (pqxdh.execute_beacon_agreement initial keys) :=
  execute_beacon_agreement_covered_total contracts initial keys
    (RegistrationAgreementBeaconCoverage.beacon_entry authenticated initial started)

end BeaconcryptCore.PanicFreedom.AdapterBeaconAgreementSafety
