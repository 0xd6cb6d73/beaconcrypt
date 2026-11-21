-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceSource

/-! This finite source interpreter checks the actual optional DH input at both preparation and material demand. Successful preparation echoes the queried descriptor. It is used only to prove the operational source correspondence; retaining the prepared-flag receipts and substituting the actual stateful alias service is a separate invariant argument. The candidate occurs in this mathematical interpreter, never in the executing symbolic frontend. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordInterface (LocalSpec)
open RegistrationNativeKeyCompiler (KeySpec)
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {KemSK Value : Type}

abbrev Residual (n : Nat) (KemSK : Type) := RegistrationNativePairedServerService.Common n +
  RegistrationNativeSecretWordInterface.LocalKem KemSK

inductive Audit where
  | prepare (message : RegistrationNativeRelatedFamily.Message)
  | demand (message : RegistrationNativeRelatedFamily.Message)

abbrev AuditSpec := Audit →ₒ Unit
abbrev PlainSpec (n : Nat) (KemSK : Type) := KeySpec + Residual n KemSK
abbrev Spec (n : Nat) (KemSK : Type) := KeySpec + (Residual n KemSK + AuditSpec)

def keys : QueryImpl KeySpec (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inl query)

def audit (event : Audit) : OracleComp (Spec n KemSK) Unit :=
  (Spec n KemSK).query (.inr (.inr event))

def preparation (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) :
    QueryImpl RegistrationNativeSecretWordMessage.PrepareSpec (OracleComp (Spec n KemSK)) :=
  fun message => do
    let _ ← audit (.prepare (RegistrationNativeSecretWordMessage.eval candidate message))
    pure ((input message).map (fun _ => message))

def material (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) (message : Message) :
    OracleComp (Spec n KemSK) (Option (RegistrationNativePairedChoice.Choice n)) := do
  let _ ← audit (.demand (RegistrationNativeSecretWordMessage.eval candidate message))
  match input message with
  | none => pure none
  | some key =>
      (some ∘ RegistrationNativePairedChoice.Choice.known) <$>
        simulateQ keys (RegistrationNativeSecretWordServiceSource.nativeMaterial source inside candidate key)

def implementation (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) :
    QueryImpl (LocalSpec n KemSK) (OracleComp (Spec n KemSK))
  | .inl message => preparation candidate input message
  | .inr (.inl (.inl message)) => material source inside candidate input message
  | .inr (.inl (.inr query)) => (Spec n KemSK).query (.inr (.inl (.inl query)))
  | .inr (.inr query) => (Spec n KemSK).query (.inr (.inl (.inr query)))

def native (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (OracleComp (Spec n KemSK)) :=
  implementation source inside candidate input ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate

/-- The checked material operation cannot run when the actual optional input is absent. -/
theorem material_missing (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) (message : Message) (missing : input message = none) :
    material (n := n) (KemSK := KemSK) source inside candidate input message =
      (audit (.demand (RegistrationNativeSecretWordMessage.eval candidate message)) *> pure none) := by
  simp only [material, missing, seqRight_eq_bind]

/-- The successful echo records no inverse assumption about arbitrary returned descriptor names. -/
theorem preparation_echo (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) (message : Message)
    (key : RegistrationNativeSecretWord.Key) (valid : input message = some key) :
    preparation (n := n) (KemSK := KemSK) candidate input message =
      (audit (.prepare (RegistrationNativeSecretWordMessage.eval candidate message)) *> pure (some message)) := by
  simp only [preparation, valid, Option.map_some, seqRight_eq_bind]

/-- Every actual local environment callback is forwarded literally by the concrete checked interpreter. -/
theorem effect_source (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    simulateQ (native (KemSK := KemSK) source inside candidate input) (RegistrationBeaconReferenceCompiler.effect query) =
      (Spec n KemSK).query (.inr (.inl (.inl (.inr query)))) := by
  unfold native
  rw [QueryImpl.simulateQ_compose, RegistrationNativeSecretWordServerSource.effect_query]
  simp only [RegistrationNativeSecretWordInterface.effect, simulateQ_spec_query, implementation]

def erase : QueryImpl (Spec n KemSK) (OracleComp (PlainSpec n KemSK))
  | .inl query => (PlainSpec n KemSK).query (.inl query)
  | .inr (.inl query) => (PlainSpec n KemSK).query (.inr query)
  | .inr (.inr _) => pure ()

def plainKeys : QueryImpl KeySpec (OracleComp (PlainSpec n KemSK)) :=
  fun query => (PlainSpec n KemSK).query (.inl query)

def plainImplementation (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) :
    QueryImpl (LocalSpec n KemSK) (OracleComp (PlainSpec n KemSK))
  | .inl message => pure ((input message).map (fun _ => message))
  | .inr (.inl (.inl message)) => match input message with
      | none => pure none
      | some key => (some ∘ RegistrationNativePairedChoice.Choice.known) <$>
          simulateQ plainKeys (RegistrationNativeSecretWordServiceSource.nativeMaterial source inside candidate key)
  | .inr (.inl (.inr query)) => (PlainSpec n KemSK).query (.inr (.inl query))
  | .inr (.inr query) => (PlainSpec n KemSK).query (.inr (.inr query))

/-- The internal audit always returns Unit; dropping it recovers the exact previous checked callback semantics. -/
theorem erase_query (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) (query : (LocalSpec n KemSK).Domain) :
    simulateQ erase (implementation source inside candidate input query) =
      plainImplementation source inside candidate input query := by
  rcases query with message | (message | query) | query
  · simp only [implementation, preparation, audit, simulateQ_bind, simulateQ_spec_query, erase,
      pure_bind, simulateQ_pure, plainImplementation]
  · simp only [implementation, material, audit, simulateQ_bind, simulateQ_spec_query, erase, pure_bind,
      plainImplementation]
    cases input message with
    | none => rfl
    | some key =>
        simp only [simulateQ_map, ← QueryImpl.simulateQ_compose]
        rfl
  · simp only [implementation, simulateQ_spec_query, erase, plainImplementation]
  · simp only [implementation, simulateQ_spec_query, erase, plainImplementation]

/-- The audit has no influence on any adaptive continuation or result after its concrete no-op interpretation. -/
theorem erase_program (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) (work : OracleComp (LocalSpec n KemSK) Value) :
    simulateQ erase (simulateQ (implementation source inside candidate input) work) =
      simulateQ (plainImplementation source inside candidate input) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  exact erase_query source inside candidate input query

end BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked.material_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked.material_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked.preparation_echo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked.preparation_echo
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked.effect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked.effect_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked.erase_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked.erase_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked.erase_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked.erase_program
