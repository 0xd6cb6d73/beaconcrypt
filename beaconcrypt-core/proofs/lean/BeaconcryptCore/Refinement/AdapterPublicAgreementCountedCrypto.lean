-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust
import BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The source cryptographic dictionary is counted field by field. The actual agreement callback functions commute with that interpretation, including every invalid primitive reply, enclosing Rust failure, updated RNG and private object. No aggregate source callback law is a premise. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementCountedRust
open AdapterPublicAgreementFields (Array32 CipherArray KemArray Keys LocalIdentity KeyPair)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {n : Nat}
local notation "Counted" => RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp)

@[instance_reducible] def operations (original : CryptoOperations (RustT ProbComp)) : CryptoOperations Counted where
  kxSecretBytes key := counted (original.kxSecretBytes key)
  convertPublic key := counted (original.convertPublic key)
  convertSecret key := counted (original.convertSecret key)
  scalarMult secret publicKey := counted (original.scalarMult secret publicKey)
  kemPublicFromBytes bytes := counted (original.kemPublicFromBytes bytes)
  kemCipherFromBytes bytes := counted (original.kemCipherFromBytes bytes)
  kemCipherBytes key := counted (original.kemCipherBytes key)
  kemSharedBytes key := counted (original.kemSharedBytes key)
  encapsulate generator key rng := counted (original.encapsulate generator key rng)
  decapsulate ciphertext secret := counted (original.decapsulate ciphertext secret)
  extract salt input := counted (original.extract salt input)
  expand width info prk := counted (original.expand width info prk)
  edPublicBytes key := counted (original.edPublicBytes key)
  edSign message key := counted (original.edSign message key)
  kxPublicBytes key := counted (original.kxPublicBytes key)
  kemPublicBytes key := counted (original.kemPublicBytes key)
  kxGenerate generator rng := counted (original.kxGenerate generator rng)

variable [original : CryptoOperations (RustT ProbComp)]
noncomputable section

theorem convertPublic (input : Array32) :
    letI : CryptoOperations Counted := operations original
    AdapterPublicAgreementFields.convertPublic (m := StateT (PqxdhRecordLiftWorld.State n) ProbComp) input =
      counted (AdapterPublicAgreementFields.convertPublic (m := ProbComp) input) := by
  let : CryptoOperations Counted := operations original
  simp only [AdapterPublicAgreementFields.convertPublic, counted_bind, counted_liftRust]
  apply bind_congr
  intro parsed
  cases parsed with
  | Err error => exact (counted_pure _).symm
  | Ok key => simp only [counted_bind, counted_liftRust]; rfl

theorem convertSecret (key : material.EdSecretKey) :
    letI : CryptoOperations Counted := operations original
    AdapterPublicAgreementFields.convertSecret (m := StateT (PqxdhRecordLiftWorld.State n) ProbComp) key =
      counted (AdapterPublicAgreementFields.convertSecret (m := ProbComp) key) := by
  let : CryptoOperations Counted := operations original
  rw [AdapterPublicAgreementPrimitiveFields.secret_conversion,
    AdapterPublicAgreementPrimitiveFields.secret_conversion, counted_bind]
  apply bind_congr
  intro reply
  exact (counted_pure _).symm

theorem scalar (secret publicKey : Array32) :
    letI : CryptoOperations Counted := operations original
    AdapterPublicAgreementPrimitiveFields.scalar (m := StateT (PqxdhRecordLiftWorld.State n) ProbComp) secret publicKey =
      counted (AdapterPublicAgreementPrimitiveFields.scalar (m := ProbComp) secret publicKey) := by
  let : CryptoOperations Counted := operations original
  simp only [AdapterPublicAgreementPrimitiveFields.scalar, counted_bind, counted_liftRust]
  rfl

theorem generate {R E : Type} (generator : rand_core.TryCryptoRng R E) (rng : R) :
    letI : CryptoOperations Counted := operations original
    AdapterPublicAgreementFields.generate (m := StateT (PqxdhRecordLiftWorld.State n) ProbComp) generator rng =
      counted (AdapterPublicAgreementFields.generate (m := ProbComp) generator rng) := by
  let : CryptoOperations Counted := operations original
  rw [AdapterPublicAgreementPrimitiveFields.generation, AdapterPublicAgreementPrimitiveFields.generation, counted_bind]
  apply bind_congr
  rintro ⟨reply, nextRng⟩
  cases reply with
  | Err error => exact (counted_pure _).symm
  | Ok key => simp only [counted_bind, counted_pure]; rfl

theorem encapsulate {R E : Type} (generator : rand_core.TryCryptoRng R E) (input : core.option.Option KemArray) (rng : R) :
    letI : CryptoOperations Counted := operations original
    AdapterPublicAgreementFields.encapsulate (m := StateT (PqxdhRecordLiftWorld.State n) ProbComp) generator input rng =
      counted (AdapterPublicAgreementFields.encapsulate (m := ProbComp) generator input rng) := by
  let : CryptoOperations Counted := operations original
  cases input with
  | none => exact (counted_pure _).symm
  | some bytes =>
    simp only [AdapterPublicAgreementFields.encapsulate, counted_bind]
    apply bind_congr
    intro parsed
    cases parsed with
    | Err error => exact (counted_pure _).symm
    | Ok key =>
      rw [counted_bind]
      apply bind_congr
      rintro ⟨reply, nextRng⟩
      cases reply with
      | Err error => exact (counted_pure _).symm
      | Ok pair =>
        rcases pair with ⟨ciphertext, shared⟩
        simp only [counted_bind, counted_pure]
        rfl

theorem decapsulate (input : core.option.Option CipherArray) (secret : core.option.Option material.KemSecretKey) :
    letI : CryptoOperations Counted := operations original
    AdapterPublicAgreementFields.decapsulate (m := StateT (PqxdhRecordLiftWorld.State n) ProbComp) input secret =
      counted (AdapterPublicAgreementFields.decapsulate (m := ProbComp) input secret) := by
  let : CryptoOperations Counted := operations original
  cases input with
  | none => exact (counted_pure _).symm
  | some bytes =>
    simp only [AdapterPublicAgreementFields.decapsulate, counted_bind]
    apply bind_congr
    intro parsed
    cases parsed with
    | Err error => exact (counted_pure _).symm
    | Ok key => cases secret with
      | none => exact (counted_pure _).symm
      | some secret =>
        rw [counted_bind]
        apply bind_congr
        intro reply
        cases reply with
        | Err error => exact (counted_pure _).symm
        | Ok shared => simp only [counted_bind, counted_pure]; rfl

theorem root (request : agreement.RootKdfRequest) :
    letI : CryptoOperations Counted := operations original
    AdapterPublicAgreementFields.root (m := StateT (PqxdhRecordLiftWorld.State n) ProbComp) request =
      counted (AdapterPublicAgreementFields.root (m := ProbComp) request) := by
  let : CryptoOperations Counted := operations original
  simp only [AdapterPublicAgreementFields.root, counted_bind]
  apply bind_congr
  intro extracted
  cases extracted with
  | Err error => exact (counted_pure _).symm
  | Ok prk =>
    rw [counted_bind]
    apply bind_congr
    intro expanded
    cases expanded with
    | Err error => exact (counted_pure _).symm
    | Ok output => simp only [counted_bind, counted_liftRust]
omit material primitive original in
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : RustT m A) = pure value := rfl

theorem dh {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (localIdentity : core.option.Option LocalIdentity) (ephemeral : core.option.Option KeyPair)
    (request : agreement.DhRequest) :
    letI : CryptoOperations Counted := operations original
    AdapterPublicAgreementFields.dh (m := StateT (PqxdhRecordLiftWorld.State n) ProbComp) generator keys localIdentity ephemeral request =
      counted (AdapterPublicAgreementFields.dh (m := ProbComp) generator keys localIdentity ephemeral request) := by
  let : CryptoOperations Counted := operations original
  rcases request with ⟨role, publicKey⟩
  cases role with
  | LocalIdentity =>
    cases localIdentity with
    | none => simp only [AdapterPublicAgreementFields.dh, core.option.Option.as_ref,
        AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind, counted_pure]
    | some key =>
      simp only [AdapterPublicAgreementFields.dh, core.option.Option.as_ref,
        AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind]
      rw [AdapterPublicAgreementPrimitiveFields.local_scalar, AdapterPublicAgreementPrimitiveFields.local_scalar]
      exact scalar key.value publicKey
  | ServerEphemeral =>
    cases ephemeral with
    | none => simp only [AdapterPublicAgreementFields.dh, core.option.Option.as_ref,
        AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind, counted_pure]
    | some key =>
      simp only [AdapterPublicAgreementFields.dh, core.option.Option.as_ref,
        AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind]
      rw [AdapterPublicAgreementPrimitiveFields.ephemeral_scalar, AdapterPublicAgreementPrimitiveFields.ephemeral_scalar, counted_bind]
      apply bind_congr
      intro bytes
      exact scalar bytes publicKey
  | BeaconPrekey =>
    cases present : keys.beacon_prekey with
    | none => simp only [AdapterPublicAgreementFields.dh, present,
        AdapterPublicWrapperRequestMonad.Option.and_then, counted_pure]
    | some key =>
      simp only [AdapterPublicAgreementFields.dh, present, AdapterPublicWrapperRequestMonad.Option.and_then]
      rw [AdapterPublicAgreementPrimitiveFields.prekey_scalar, AdapterPublicAgreementPrimitiveFields.prekey_scalar, counted_bind]
      apply bind_congr
      intro bytes
      exact scalar bytes publicKey
  | BeaconOneTime =>
    cases present : keys.beacon_one_time with
    | none => simp only [AdapterPublicAgreementFields.dh, present,
        AdapterPublicWrapperRequestMonad.Option.and_then, counted_pure]
    | some key =>
      simp only [AdapterPublicAgreementFields.dh, present, AdapterPublicWrapperRequestMonad.Option.and_then]
      rw [AdapterPublicAgreementPrimitiveFields.one_time_scalar, AdapterPublicAgreementPrimitiveFields.one_time_scalar, counted_bind]
      apply bind_congr
      intro bytes
      exact scalar bytes publicKey

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.convertPublic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.convertPublic

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.convertSecret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.convertSecret

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.scalar

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.generate

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.encapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.encapsulate

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.decapsulate

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.root

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto.dh
