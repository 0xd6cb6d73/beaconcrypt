-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
/-! Narrow selected primitive functional contracts for source private-key getters, converted identity objects and X25519. The X25519 target is the existing fixed source computation, including its all-zero rejection. Every contract names one actual primitive field; the source body and complete executor equalities are separately proved without such contracts. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 LocalIdentity KeyPair)
open BeaconcryptCore.Computational
open PqxdhRootTableInitialization (rootArray)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

def optionalResult {A : Type} (failure : primitive.Error) (reply : core.option.Option A) : core.result.Result A primitive.Error :=
  match reply with
  | .None => .Err failure
  | .Some value => .Ok value

def scalarReply (functional : Pqxdh.Crypto) (secret publicKey : Array32) : core.option.Option Array32 :=
  RegistrationAgreementRoot.nativeOption ((PqxdhJointGapDh.sourceScalarDh functional
    (PqxdhPhase2GapDhSource.peer secret) (PqxdhPhase2GapDhSource.peer publicKey)).map rootArray)

structure KeyGetters (view : AdapterPublicWrapperState.MaterialView source KemSK) where
  secret : ∀ key, crypto.kxSecretBytes key = pure (rootArray (view.kxSecret key))
  publicKey : ∀ key, crypto.kxPublicBytes key = pure (view.kxPublic key)

structure IdentityConversion (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (converted : PqxdhJointIdentity.IdentitySeed → Array32) where
  operation : ∀ key, crypto.convertSecret key = pure (.Ok (converted (view.edSecret key)))

structure Scalar (functional : Pqxdh.Crypto) where
  failure : Array32 → Array32 → primitive.Error
  operation : ∀ secret publicKey, crypto.scalarMult secret.to_slice publicKey.to_slice =
    pure (optionalResult (failure secret publicKey) (scalarReply functional secret publicKey))

theorem scalar (functional : Pqxdh.Crypto) (contract : Scalar (m := m) functional) (secret publicKey : Array32) :
    AdapterPublicAgreementPrimitiveFields.scalar (m := m) secret publicKey = pure (scalarReply functional secret publicKey) := by
  rw [AdapterPublicAgreementPrimitiveFields.scalar, contract.operation, pure_bind]
  cases scalarReply functional secret publicKey <;> rfl

theorem converted_identity (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (converted : PqxdhJointIdentity.IdentitySeed → Array32)
    (contract : IdentityConversion (m := m) view converted) (key : beaconcrypt_crypto.crypto_sign.SecretKey) :
    AdapterPublicAgreementFields.convertSecret (m := m) key =
      pure (.Some (⟨converted (view.edSecret key)⟩ : LocalIdentity)) := by
  rw [AdapterPublicAgreementPrimitiveFields.secret_conversion, contract.operation, pure_bind]

noncomputable section

theorem local_dh {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (functional : Pqxdh.Crypto) (contract : Scalar (m := m) functional) (secret : LocalIdentity) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832.call_once
      (m := RustT m) generator publicKey secret = pure (scalarReply functional secret.value publicKey) := by
  rw [AdapterPublicAgreementPrimitiveFields.local_scalar]
  exact scalar functional contract secret.value publicKey

theorem ephemeral_dh {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (getters : KeyGetters (m := m) view)
    (functional : Pqxdh.Crypto) (contract : Scalar (m := m) functional) (key : KeyPair) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832.call_once
      (m := RustT m) generator publicKey key =
      pure (scalarReply functional (rootArray (view.kxSecret key.secret_key)) publicKey) := by
  rw [AdapterPublicAgreementPrimitiveFields.ephemeral_scalar, getters.secret, pure_bind]
  exact scalar functional contract _ _

theorem prekey_dh {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (getters : KeyGetters (m := m) view)
    (functional : Pqxdh.Crypto) (contract : Scalar (m := m) functional)
    (key : beaconcrypt_crypto.crypto_kx.SecretKey) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once
      (m := RustT m) generator publicKey key =
      pure (scalarReply functional (rootArray (view.kxSecret key)) publicKey) := by
  rw [AdapterPublicAgreementPrimitiveFields.prekey_scalar, getters.secret, pure_bind]
  exact scalar functional contract _ _

theorem one_time_dh {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (getters : KeyGetters (m := m) view)
    (functional : Pqxdh.Crypto) (contract : Scalar (m := m) functional)
    (key : beaconcrypt_crypto.crypto_kx.SecretKey) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once
      (m := RustT m) generator publicKey key =
      pure (scalarReply functional (rootArray (view.kxSecret key)) publicKey) := by
  rw [AdapterPublicAgreementPrimitiveFields.one_time_scalar, getters.secret, pure_bind]
  exact scalar functional contract _ _
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.scalar

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.converted_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.converted_identity

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.local_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.local_dh

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.ephemeral_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.ephemeral_dh

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.prekey_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.prekey_dh

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.one_time_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional.one_time_dh
