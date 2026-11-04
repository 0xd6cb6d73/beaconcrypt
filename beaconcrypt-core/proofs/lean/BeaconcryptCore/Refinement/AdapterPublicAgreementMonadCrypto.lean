-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap
import BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! A lawful effect interpretation maps the source crypto dictionary field by field. The actual source callbacks commute with this map, including every invalid reply, enclosing Rust failure, returned RNG and private object. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementMonadMap
open AdapterPublicAgreementFields (Array32 CipherArray KemArray Keys LocalIdentity KeyPair)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {left right : Type → Type} [Monad left] [LawfulMonad left] [Monad right] [LawfulMonad right]
variable [Transformation left right]
local notation "Mapped" => RustT (right)

@[instance_reducible] def operations (original : CryptoOperations (RustT left)) : CryptoOperations Mapped where
  kxSecretBytes key := mapped (original.kxSecretBytes key)
  convertPublic key := mapped (original.convertPublic key)
  convertSecret key := mapped (original.convertSecret key)
  scalarMult secret publicKey := mapped (original.scalarMult secret publicKey)
  kemPublicFromBytes bytes := mapped (original.kemPublicFromBytes bytes)
  kemCipherFromBytes bytes := mapped (original.kemCipherFromBytes bytes)
  kemCipherBytes key := mapped (original.kemCipherBytes key)
  kemSharedBytes key := mapped (original.kemSharedBytes key)
  encapsulate generator key rng := mapped (original.encapsulate generator key rng)
  decapsulate ciphertext secret := mapped (original.decapsulate ciphertext secret)
  extract salt input := mapped (original.extract salt input)
  expand width info prk := mapped (original.expand width info prk)
  edPublicBytes key := mapped (original.edPublicBytes key)
  edSign message key := mapped (original.edSign message key)
  kxPublicBytes key := mapped (original.kxPublicBytes key)
  kemPublicBytes key := mapped (original.kemPublicBytes key)
  kxGenerate generator rng := mapped (original.kxGenerate generator rng)

variable [original : CryptoOperations (RustT left)]
noncomputable section

omit [LawfulMonad left] [LawfulMonad right] in
theorem convertPublic (input : Array32) :
    letI : CryptoOperations Mapped := operations original
    AdapterPublicAgreementFields.convertPublic (m := right) input =
      mapped (AdapterPublicAgreementFields.convertPublic (m := left) input) := by
  let : CryptoOperations Mapped := operations original
  simp only [AdapterPublicAgreementFields.convertPublic, mapped_bind, mapped_liftRust]
  apply bind_congr
  intro parsed
  cases parsed with
  | Err error => exact (mapped_pure _).symm
  | Ok key => simp only [mapped_bind, mapped_liftRust]; rfl

theorem convertSecret (key : material.EdSecretKey) :
    letI : CryptoOperations Mapped := operations original
    AdapterPublicAgreementFields.convertSecret (m := right) key =
      mapped (AdapterPublicAgreementFields.convertSecret (m := left) key) := by
  let : CryptoOperations Mapped := operations original
  rw [AdapterPublicAgreementPrimitiveFields.secret_conversion,
    AdapterPublicAgreementPrimitiveFields.secret_conversion, mapped_bind]
  apply bind_congr
  intro reply
  exact (mapped_pure _).symm

omit [LawfulMonad left] [LawfulMonad right] in
theorem scalar (secret publicKey : Array32) :
    letI : CryptoOperations Mapped := operations original
    AdapterPublicAgreementPrimitiveFields.scalar (m := right) secret publicKey =
      mapped (AdapterPublicAgreementPrimitiveFields.scalar (m := left) secret publicKey) := by
  let : CryptoOperations Mapped := operations original
  simp only [AdapterPublicAgreementPrimitiveFields.scalar, mapped_bind, mapped_liftRust]
  rfl

theorem generate {R E : Type} (generator : rand_core.TryCryptoRng R E) (rng : R) :
    letI : CryptoOperations Mapped := operations original
    AdapterPublicAgreementFields.generate (m := right) generator rng =
      mapped (AdapterPublicAgreementFields.generate (m := left) generator rng) := by
  let : CryptoOperations Mapped := operations original
  rw [AdapterPublicAgreementPrimitiveFields.generation, AdapterPublicAgreementPrimitiveFields.generation, mapped_bind]
  apply bind_congr
  rintro ⟨reply, nextRng⟩
  cases reply with
  | Err error => exact (mapped_pure _).symm
  | Ok key => simp only [mapped_bind, mapped_pure]; rfl

omit [LawfulMonad left] [LawfulMonad right] in
theorem encapsulate {R E : Type} (generator : rand_core.TryCryptoRng R E) (input : core.option.Option KemArray) (rng : R) :
    letI : CryptoOperations Mapped := operations original
    AdapterPublicAgreementFields.encapsulate (m := right) generator input rng =
      mapped (AdapterPublicAgreementFields.encapsulate (m := left) generator input rng) := by
  let : CryptoOperations Mapped := operations original
  cases input with
  | none => exact (mapped_pure _).symm
  | some bytes =>
    simp only [AdapterPublicAgreementFields.encapsulate, mapped_bind]
    apply bind_congr
    intro parsed
    cases parsed with
    | Err error => exact (mapped_pure _).symm
    | Ok key =>
      rw [mapped_bind]
      apply bind_congr
      rintro ⟨reply, nextRng⟩
      cases reply with
      | Err error => exact (mapped_pure _).symm
      | Ok pair =>
        rcases pair with ⟨ciphertext, shared⟩
        simp only [mapped_bind, mapped_pure]
        rfl

omit [LawfulMonad left] [LawfulMonad right] in
theorem decapsulate (input : core.option.Option CipherArray) (secret : core.option.Option material.KemSecretKey) :
    letI : CryptoOperations Mapped := operations original
    AdapterPublicAgreementFields.decapsulate (m := right) input secret =
      mapped (AdapterPublicAgreementFields.decapsulate (m := left) input secret) := by
  let : CryptoOperations Mapped := operations original
  cases input with
  | none => exact (mapped_pure _).symm
  | some bytes =>
    simp only [AdapterPublicAgreementFields.decapsulate, mapped_bind]
    apply bind_congr
    intro parsed
    cases parsed with
    | Err error => exact (mapped_pure _).symm
    | Ok key => cases secret with
      | none => exact (mapped_pure _).symm
      | some secret =>
        rw [mapped_bind]
        apply bind_congr
        intro reply
        cases reply with
        | Err error => exact (mapped_pure _).symm
        | Ok shared => simp only [mapped_bind, mapped_pure]; rfl

omit [LawfulMonad left] [LawfulMonad right] in
theorem root (request : agreement.RootKdfRequest) :
    letI : CryptoOperations Mapped := operations original
    AdapterPublicAgreementFields.root (m := right) request =
      mapped (AdapterPublicAgreementFields.root (m := left) request) := by
  let : CryptoOperations Mapped := operations original
  simp only [AdapterPublicAgreementFields.root, mapped_bind]
  apply bind_congr
  intro extracted
  cases extracted with
  | Err error => exact (mapped_pure _).symm
  | Ok prk =>
    rw [mapped_bind]
    apply bind_congr
    intro expanded
    cases expanded with
    | Err error => exact (mapped_pure _).symm
    | Ok output => simp only [mapped_bind, mapped_liftRust]
omit material primitive original in
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : RustT m A) = pure value := rfl

theorem dh {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (localIdentity : core.option.Option LocalIdentity) (ephemeral : core.option.Option KeyPair)
    (request : agreement.DhRequest) :
    letI : CryptoOperations Mapped := operations original
    AdapterPublicAgreementFields.dh (m := right) generator keys localIdentity ephemeral request =
      mapped (AdapterPublicAgreementFields.dh (m := left) generator keys localIdentity ephemeral request) := by
  let : CryptoOperations Mapped := operations original
  rcases request with ⟨role, publicKey⟩
  cases role with
  | LocalIdentity =>
    cases localIdentity with
    | none => simp only [AdapterPublicAgreementFields.dh, core.option.Option.as_ref,
        AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind, mapped_pure]
    | some key =>
      simp only [AdapterPublicAgreementFields.dh, core.option.Option.as_ref,
        AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind]
      rw [AdapterPublicAgreementPrimitiveFields.local_scalar, AdapterPublicAgreementPrimitiveFields.local_scalar]
      exact scalar key.value publicKey
  | ServerEphemeral =>
    cases ephemeral with
    | none => simp only [AdapterPublicAgreementFields.dh, core.option.Option.as_ref,
        AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind, mapped_pure]
    | some key =>
      simp only [AdapterPublicAgreementFields.dh, core.option.Option.as_ref,
        AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind]
      rw [AdapterPublicAgreementPrimitiveFields.ephemeral_scalar, AdapterPublicAgreementPrimitiveFields.ephemeral_scalar, mapped_bind]
      apply bind_congr
      intro bytes
      exact scalar bytes publicKey
  | BeaconPrekey =>
    cases present : keys.beacon_prekey with
    | none => simp only [AdapterPublicAgreementFields.dh, present,
        AdapterPublicWrapperRequestMonad.Option.and_then, mapped_pure]
    | some key =>
      simp only [AdapterPublicAgreementFields.dh, present, AdapterPublicWrapperRequestMonad.Option.and_then]
      rw [AdapterPublicAgreementPrimitiveFields.prekey_scalar, AdapterPublicAgreementPrimitiveFields.prekey_scalar, mapped_bind]
      apply bind_congr
      intro bytes
      exact scalar bytes publicKey
  | BeaconOneTime =>
    cases present : keys.beacon_one_time with
    | none => simp only [AdapterPublicAgreementFields.dh, present,
        AdapterPublicWrapperRequestMonad.Option.and_then, mapped_pure]
    | some key =>
      simp only [AdapterPublicAgreementFields.dh, present, AdapterPublicWrapperRequestMonad.Option.and_then]
      rw [AdapterPublicAgreementPrimitiveFields.one_time_scalar, AdapterPublicAgreementPrimitiveFields.one_time_scalar, mapped_bind]
      apply bind_congr
      intro bytes
      exact scalar bytes publicKey

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto


/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.convertPublic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.convertPublic

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.convertSecret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.convertSecret

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.scalar

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.generate

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.encapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.encapsulate

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.decapsulate

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.dh

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto.root
