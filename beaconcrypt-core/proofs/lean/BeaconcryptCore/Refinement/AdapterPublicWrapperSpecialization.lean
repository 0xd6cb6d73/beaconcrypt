-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction
import BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop
import BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop
import BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop
/-! Every effectful selected source declaration, including callback dictionaries, specializes to its original extracted RustM body. The three finite request loops equal the source loops by the actual decreasing source ranks. Source control, failure branches, callback captures, mutable returns and child call order are retained; no wrapper equality is a premise. Joint stateful interpretation uses the generic checked body separately. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
open beaconcrypt_public_wrapper
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
noncomputable section
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization
variable [model0 : BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [model1 : BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [model2 : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [model3 : BeaconcryptCore.Refinement.PublicWrapperPlatform.Allocator]
variable [model4 : BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations]
variable [model5 : BeaconcryptCore.Refinement.PublicWrapperPlatform.CryptoOperations]
variable [model6 : BeaconcryptCore.Refinement.PublicWrapperPlatform.ContainerOperations]
variable [model7 : BeaconcryptCore.Refinement.PublicWrapperPlatform.Codecs]
variable [model8 : BeaconcryptCore.Refinement.RegistrationWriterPrimitive.Operations]
variable [model9 : BeaconcryptCore.Refinement.AdapterWirePrimitive.Operations]
variable [model10 : beaconcrypt.ratchet.Operations] [model11 : beaconcrypt.auth.Operations]
set_option backward.isDefEq.respectTransparency false
omit model1 model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem beacon_identity_public_source
  (self : beacon.Beacon) :
    beaconcrypt_public_request.beacon.Beacon.identity_pk (m := RustM) self =
    beaconcrypt_public_wrapper.beacon.Beacon.identity_pk self := by
  rfl

omit model1 model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem beacon_identity_secret_source
  (self : beacon.Beacon) :
    beaconcrypt_public_request.beacon.Beacon.identity_sk (m := RustM) self =
    beaconcrypt_public_wrapper.beacon.Beacon.identity_sk self := by
  rfl

omit model1 model3 model4 model6 model7 in
theorem init_body_source
  (beacon1 : beacon.Beacon)
  (effect : beaconcrypt_core.registration.BeaconInitEffect) :
    beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop.body (m := RustM) beacon1 effect =
    beaconcrypt_public_wrapper.beacon._proof_beacon_init_ready_loop.body beacon1 effect := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 in
private theorem init_fuel (beacon1 : beacon.Beacon) (fuel : Nat)
    (effect : beaconcrypt_core.registration.BeaconInitEffect) :
    AdapterPublicWrapperLiftFunction.loopFuel (m := RustM) fuel
      (fun next => beaconcrypt_public_wrapper.beacon._proof_beacon_init_ready_loop.body beacon1 next) effect =
    AdapterPublicInitSourceLoop.drive beacon1 fuel effect := by
  induction fuel generalizing effect with
  | zero => rfl
  | succ fuel ih =>
      rw [AdapterPublicWrapperLiftFunction.loopFuel, AdapterPublicInitSourceLoop.drive]
      simp only [AdapterPublicInitSourceLoop.body]
      cases actual : beaconcrypt_public_wrapper.beacon._proof_beacon_init_ready_loop.body beacon1 effect with
      | fail error | div => rfl
      | ok decision => cases decision with
        | done value => rfl
        | cont next => exact ih next


omit model1 model3 model4 model6 model7 in
theorem init_loop_source
  (effect : beaconcrypt_core.registration.BeaconInitEffect)
  (beacon1 : beacon.Beacon) :
    beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop (m := RustM) effect beacon1 =
    beaconcrypt_public_wrapper.beacon._proof_beacon_init_ready_loop effect beacon1 := by
  unfold beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop
  simp only [init_body_source]
  exact (init_fuel beacon1 _ effect).trans (AdapterPublicInitSourceLoop.loop_specializes beacon1 _ effect (by omega))

omit model1 model3 model4 model6 model7 in
theorem init_ready_source
  (beacon1 : beacon.Beacon)
  (effect : beaconcrypt_core.registration.BeaconInitEffect) :
    beaconcrypt_public_request.beacon._proof_beacon_init_ready (m := RustM) beacon1 effect =
    beaconcrypt_public_wrapper.beacon._proof_beacon_init_ready beacon1 effect := by
  unfold beaconcrypt_public_request.beacon._proof_beacon_init_ready beaconcrypt_public_wrapper.beacon._proof_beacon_init_ready
  rw [init_loop_source]

omit model1 model3 model4 model6 model7 in
theorem registration_bundle_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (self : beacon.Beacon)
  (rng : R) :
    beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst self rng =
    beaconcrypt_public_wrapper.beacon.Beacon.get_registration_bundle_with_rng (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst self rng := by
  simp only [beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng, beaconcrypt_public_wrapper.beacon.Beacon.get_registration_bundle_with_rng, init_ready_source]
  rfl

omit model0 model1 model2 model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem ratchet_slot_source
  (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_request.ratchet.RatchetKernelSlot.new (m := RustM) kernel =
    beaconcrypt_public_wrapper.ratchet.RatchetKernelSlot.new kernel := by
  rfl

omit model0 model1 model2 model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem ratchet_manager_source
  (refined : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_request.ratchet.RatchetManager.from_kernel (m := RustM) refined =
    beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel refined := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem root_kdf_call_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_8 R Clause0_Clause0_Error)
  (unitArg : Unit) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_8.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c unitArg =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_8.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c unitArg := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem onetime_dh_call_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_7 R Clause0_Clause0_Error)
  (tupled_args : beaconcrypt_crypto.crypto_kx.SecretKey) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem onetime_dh_dictionary_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error) :
    (beaconcrypt_public_request.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832 (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst).toRust =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832 (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem prekey_dh_call_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_6 R Clause0_Clause0_Error)
  (tupled_args : beaconcrypt_crypto.crypto_kx.SecretKey) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem prekey_dh_dictionary_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error) :
    (beaconcrypt_public_request.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832 (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst).toRust =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832 (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem ephemeral_dh_call_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_5 R Clause0_Clause0_Error)
  (tupled_args : beaconcrypt_crypto.crypto_kx.KeyPair) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832.call_once (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem ephemeral_dh_dictionary_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error) :
    (beaconcrypt_public_request.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832 (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst).toRust =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832 (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem identity_dh_call_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_4 R Clause0_Clause0_Error)
  (tupled_args : zeroize.Zeroizing (Array Std.U8 32#usize)) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832.call_once (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c tupled_args := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem identity_dh_dictionary_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error) :
    (beaconcrypt_public_request.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832 (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst).toRust =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832 (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem decapsulation_call_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_3 R Clause0_Clause0_Error)
  (unitArg : Unit) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_3.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c unitArg =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_3.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst c unitArg := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem encapsulation_call_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (c : pqxdh.execute_agreement.closure_2 R Clause0_Clause0_Error)
  (unitArg : Unit) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_2.Insts.CoreOpsFunctionFnMutTupleOptionPairArrayU81088ArrayU832.call_mut (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst c unitArg =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_2.Insts.CoreOpsFunctionFnMutTupleOptionPairArrayU81088ArrayU832.call_mut (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst c unitArg := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem ephemeral_public_call_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (_c : pqxdh.execute_agreement.closure_1 R Clause0_Clause0_Error)
  (tupled_args : beaconcrypt_crypto.crypto_kx.KeyPair) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832.call_once (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst _c tupled_args =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst _c tupled_args := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem ephemeral_public_dictionary_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error) :
    (beaconcrypt_public_request.pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832 (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst).toRust =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832 (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem public_conversion_call_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (_rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (_c : pqxdh.execute_agreement.closure R Clause0_Clause0_Error)
  (tupled_args : beaconcrypt_crypto.crypto_sign.PublicKey) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832.call_once (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst _c tupled_args =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832.call_once (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) _rand_coreTryCryptoRngInst _c tupled_args := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem public_conversion_dictionary_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error) :
    (beaconcrypt_public_request.pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832 (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst).toRust =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832 (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst := by
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem agreement_body_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (sk : beaconcrypt_crypto.crypto_sign.SecretKey)
  (o : core.option.Option beaconcrypt_crypto.crypto_kx.SecretKey)
  (o1 : core.option.Option beaconcrypt_crypto.crypto_kx.SecretKey)
  (o2 : core.option.Option beaconcrypt_crypto.crypto_kem.mlkem768.SecretKey)
  (effect : beaconcrypt_core.agreement.AgreementEffect)
  (rng : R)
  (local_identity : core.option.Option (zeroize.Zeroizing (Array Std.U8
  32#usize)))
  (server_ephemeral : core.option.Option beaconcrypt_crypto.crypto_kx.KeyPair) :
    beaconcrypt_public_request.pqxdh.execute_agreement_loop.body (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst sk o o1 o2 effect rng local_identity server_ephemeral =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop.body (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst sk o o1 o2 effect rng local_identity server_ephemeral := by
  simp only [beaconcrypt_public_request.pqxdh.execute_agreement_loop.body, AdapterPublicWrapperRequestMonad.Option.map_toRust, AdapterPublicWrapperRequestMonad.Option.and_then_toRust, onetime_dh_dictionary_source, prekey_dh_dictionary_source, ephemeral_dh_dictionary_source, identity_dh_dictionary_source, ephemeral_public_dictionary_source, public_conversion_dictionary_source]
  rfl

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
private theorem agreement_fuel {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : pqxdh.RegistrationKeys) (fuel : Nat) (state : AdapterPublicAgreementSourceLoop.State R) :
    AdapterPublicWrapperLiftFunction.loopFuel (m := RustM) fuel
      (fun next => beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop.body generator
        keys.identity_secret keys.beacon_prekey keys.beacon_one_time keys.beacon_kem
        next.1 next.2.1 next.2.2.1 next.2.2.2) state =
    AdapterPublicAgreementSourceLoop.drive generator keys fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rcases state with ⟨phase, coins, localIdentity, ephemeral⟩
      rw [AdapterPublicWrapperLiftFunction.loopFuel, AdapterPublicAgreementSourceLoop.drive]
      simp only [AdapterPublicAgreementSourceLoop.body]
      cases actual : beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop.body generator
        keys.identity_secret keys.beacon_prekey keys.beacon_one_time keys.beacon_kem
        phase coins localIdentity ephemeral with
      | fail error | div => rfl
      | ok decision => cases decision with
        | done value => rfl
        | cont next => exact ih next


omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem agreement_loop_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (effect : beaconcrypt_core.agreement.AgreementEffect)
  (sk : beaconcrypt_crypto.crypto_sign.SecretKey)
  (o : core.option.Option beaconcrypt_crypto.crypto_kx.SecretKey)
  (o1 : core.option.Option beaconcrypt_crypto.crypto_kx.SecretKey)
  (o2 : core.option.Option beaconcrypt_crypto.crypto_kem.mlkem768.SecretKey)
  (rng : R)
  (local_identity : core.option.Option (zeroize.Zeroizing (Array Std.U8
  32#usize)))
  (server_ephemeral : core.option.Option beaconcrypt_crypto.crypto_kx.KeyPair) :
    beaconcrypt_public_request.pqxdh.execute_agreement_loop (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst effect sk o o1 o2 rng local_identity server_ephemeral =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst effect sk o o1 o2 rng local_identity server_ephemeral := by
  unfold beaconcrypt_public_request.pqxdh.execute_agreement_loop
  simp only [agreement_body_source]
  change AdapterPublicWrapperLiftFunction.loopFuel _ (fun next => beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop.body rand_coreTryCryptoRngInst sk o o1 o2 next.1 next.2.1 next.2.2.1 next.2.2.2) (effect, rng, local_identity, server_ephemeral) = _
  exact (agreement_fuel rand_coreTryCryptoRngInst ⟨sk, o, o1, o2⟩ _ (effect, rng, local_identity, server_ephemeral)).trans
    (AdapterPublicAgreementSourceLoop.loop_specializes rand_coreTryCryptoRngInst ⟨sk, o, o1, o2⟩ _ _ (Nat.lt_succ_self _))

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem agreement_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (effect : beaconcrypt_core.agreement.AgreementEffect)
  (keys : pqxdh.RegistrationKeys)
  (rng : R) :
    beaconcrypt_public_request.pqxdh.execute_agreement (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst effect keys rng =
    beaconcrypt_public_wrapper.pqxdh.execute_agreement (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst effect keys rng := by
  unfold beaconcrypt_public_request.pqxdh.execute_agreement beaconcrypt_public_wrapper.pqxdh.execute_agreement
  rw [agreement_loop_source]

omit model1 model3 model4 model6 model7 model8 model9 model10 model11 in
theorem beacon_agreement_source
  (effect : beaconcrypt_core.agreement.AgreementEffect)
  (keys : pqxdh.RegistrationKeys) :
    beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m := RustM) effect keys =
    beaconcrypt_public_wrapper.pqxdh.execute_beacon_agreement effect keys := by
  unfold beaconcrypt_public_request.pqxdh.execute_beacon_agreement beaconcrypt_public_wrapper.pqxdh.execute_beacon_agreement
  rw [agreement_source]
  rfl

omit model0 model1 model2 model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem response_conversion_dictionary_source
   :
    (beaconcrypt_public_request.beacon.ProviderBeaconBeacon.finish_registration.closure.Insts.CoreOpsFunctionFnOnceTuplekexresponseOptionResponsePacket (m := RustM) ).toRust =
    beaconcrypt_public_wrapper.beacon.ProviderBeaconBeacon.finish_registration.closure.Insts.CoreOpsFunctionFnOnceTuplekexresponseOptionResponsePacket  := by
  rfl

omit model1 model3 model4 model5 model6 model7 in
theorem finish_body_source
  (i : Std.U64)
  (effect : beaconcrypt_core.registration.BeaconInitialOpen) :
    beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body (m := RustM) i effect =
    beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body i effect := by
  rfl

omit model1 model2 model3 model4 model5 model6 model7 model8 model9 model11 in
private theorem finish_fuel (identifier : U64) (fuel : Nat)
    (effect : beaconcrypt_core.registration.BeaconInitialOpen) :
    AdapterPublicWrapperLiftFunction.loopFuel (m := RustM) fuel
      (fun next => beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body identifier next) effect =
    AdapterPublicFinishSourceLoop.drive fuel identifier effect := by
  induction fuel generalizing effect with
  | zero => rfl
  | succ fuel ih =>
      rw [AdapterPublicWrapperLiftFunction.loopFuel, AdapterPublicFinishSourceLoop.drive]
      simp only [AdapterPublicFinishSourceLoop.body]
      cases actual : beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body identifier effect with
      | fail error | div => rfl
      | ok decision => cases decision with
        | done value => rfl
        | cont next => exact ih next

omit model1 model3 model4 model5 model6 model7 in
theorem finish_loop_source
  (effect : beaconcrypt_core.registration.BeaconInitialOpen)
  (i : Std.U64) :
    beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop (m := RustM) effect i =
    beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop effect i := by
  unfold beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop
  simp only [finish_body_source]
  exact (finish_fuel i _ effect).trans (AdapterPublicFinishSourceLoop.loop_specializes _ i effect (by omega))

omit model3 model6 in
theorem finish_registration_source
  (self : beacon.Beacon)
  (bytes : Slice Std.U8) :
    beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration (m := RustM) self bytes =
    beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes := by
  simp only [beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration, beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration, AdapterPublicWrapperRequestMonad.Option.and_then_toRust, response_conversion_dictionary_source, beacon_agreement_source, finish_loop_source]
  rfl

omit model0 model1 model2 model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem response_length_source
  (application_len : Std.Usize)
  (assigned_key_id : Std.U64) :
    beaconcrypt_public_request.server.registration_response_len (m := RustM) application_len assigned_key_id =
    beaconcrypt_public_wrapper.server.registration_response_len application_len assigned_key_id := by
  rfl

omit model3 model5 model6 model7 model8 model9 model10 model11 in
theorem server_mldsa_public_key_source
  (self : server.Server) :
    beaconcrypt_public_request.server.Server.mldsa_public_key (m := RustM) self =
    beaconcrypt_public_wrapper.server.Server.mldsa_public_key self := by
  rfl

omit model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem server_identity_public_source
  (self : server.Server) :
    beaconcrypt_public_request.server.Server.identity_pk (m := RustM) self =
    beaconcrypt_public_wrapper.server.Server.identity_pk self := by
  rfl

omit model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem server_identifier_source
  (self : server.Server) :
    beaconcrypt_public_request.server.Server.identity_key_kid (m := RustM) self =
    beaconcrypt_public_wrapper.server.Server.identity_key_kid self := by
  rfl

omit model3 model6 model7 model8 model9 model10 model11 in
theorem server_pin_source
  (self : server.Server) :
    beaconcrypt_public_request.server.Server.authentication_pin (m := RustM) self =
    beaconcrypt_public_wrapper.server.Server.authentication_pin self := by
  rfl

omit model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem server_identity_secret_source
  (self : server.Server) :
    beaconcrypt_public_request.server.Server.identity_sk (m := RustM) self =
    beaconcrypt_public_wrapper.server.Server.identity_sk self := by
  rfl

omit model3 model6 in
theorem authenticate_lookup_source
  (self : server.Server)
  (buffer : Slice Std.U8) :
    beaconcrypt_public_request.server.Server.authenticate_registration_lookup (m := RustM) self buffer =
    beaconcrypt_public_wrapper.server.Server.authenticate_registration_lookup self buffer := by
  rfl

omit model7 model8 model9 model10 model11 in
theorem accept_registration_source
  {R : Type}
  {Clause0_Clause0_Error : Type}
  (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error)
  (self : server.Server)
  (lookup : beaconcrypt_core.peer.RegistrationLookup)
  (rng : R) :
    beaconcrypt_public_request.server.Server.get_shared_secret_from_lookup_with_rng (m := RustM) (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst self lookup rng =
    beaconcrypt_public_wrapper.server.Server.get_shared_secret_from_lookup_with_rng (R := R) (Clause0_Clause0_Error := Clause0_Clause0_Error) rand_coreTryCryptoRngInst self lookup rng := by
  simp only [beaconcrypt_public_request.server.Server.get_shared_secret_from_lookup_with_rng, beaconcrypt_public_wrapper.server.Server.get_shared_secret_from_lookup_with_rng, agreement_source]
  rfl

omit model0 model1 model2 model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem map_peer_ratchet_source
  (peer : beaconcrypt_core.peer.Peer
  beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_request.shared.map_peer_ratchet (m := RustM) peer =
    beaconcrypt_public_wrapper.shared.map_peer_ratchet peer := by
  rfl

omit model0 model1 model2 model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem established_remote_source
  {PkType : Type}
  (_SignaturePkInst : shared.SignaturePk PkType)
  (pk : PkType)
  (peer : beaconcrypt_core.peer.Peer
  beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_request.shared.EstablishedRemote.from_peer (m := RustM) (PkType := PkType) _SignaturePkInst pk peer =
    beaconcrypt_public_wrapper.shared.EstablishedRemote.from_peer (PkType := PkType) _SignaturePkInst pk peer := by
  rfl

omit model0 model1 model2 model3 model4 model5 model6 model7 model8 model9 model10 model11 in
theorem response_frame_dictionary_source
   :
    (beaconcrypt_public_request.server.ProviderServerServer.build_registration_response.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairVecU8ArrayU816PairSharedSliceU8ArrayU816 (m := RustM) ).toRust =
    beaconcrypt_public_wrapper.server.ProviderServerServer.build_registration_response.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairVecU8ArrayU816PairSharedSliceU8ArrayU816  := by
  rfl

omit model7 in
theorem build_registration_response_source
  (self : server.Server)
  (reg_out : server.RegistrationOutput)
  (data : core.option.Option (Slice Std.U8)) :
    beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response (m := RustM) self reg_out data =
    beaconcrypt_public_wrapper.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self reg_out data := by
  simp only [beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response, beaconcrypt_public_wrapper.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response, AdapterPublicWrapperRequestMonad.Option.map_toRust, response_frame_dictionary_source]
  rfl

end BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization


/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.beacon_identity_public_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.beacon_identity_public_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.beacon_identity_secret_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.beacon_identity_secret_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.init_body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.init_body_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.init_loop_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.init_loop_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.init_ready_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.init_ready_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.registration_bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.registration_bundle_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ratchet_slot_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ratchet_slot_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ratchet_manager_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ratchet_manager_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.root_kdf_call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.root_kdf_call_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.onetime_dh_call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.onetime_dh_call_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.onetime_dh_dictionary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.onetime_dh_dictionary_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.prekey_dh_call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.prekey_dh_call_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.prekey_dh_dictionary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.prekey_dh_dictionary_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ephemeral_dh_call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ephemeral_dh_call_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ephemeral_dh_dictionary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ephemeral_dh_dictionary_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.identity_dh_call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.identity_dh_call_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.identity_dh_dictionary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.identity_dh_dictionary_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.decapsulation_call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.decapsulation_call_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.encapsulation_call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.encapsulation_call_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ephemeral_public_call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ephemeral_public_call_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ephemeral_public_dictionary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.ephemeral_public_dictionary_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.public_conversion_call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.public_conversion_call_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.public_conversion_dictionary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.public_conversion_dictionary_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.agreement_body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.agreement_body_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.agreement_loop_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.agreement_loop_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.agreement_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.beacon_agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.beacon_agreement_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.response_conversion_dictionary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.response_conversion_dictionary_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.finish_body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.finish_body_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.finish_loop_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.finish_loop_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.finish_registration_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.finish_registration_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.response_length_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.response_length_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.server_mldsa_public_key_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.server_mldsa_public_key_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.server_identity_public_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.server_identity_public_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.server_identifier_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.server_identifier_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.server_pin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.server_pin_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.server_identity_secret_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.server_identity_secret_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.authenticate_lookup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.authenticate_lookup_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.accept_registration_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.accept_registration_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.map_peer_ratchet_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.map_peer_ratchet_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.established_remote_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.established_remote_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.response_frame_dictionary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.response_frame_dictionary_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.build_registration_response_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization.build_registration_response_source
