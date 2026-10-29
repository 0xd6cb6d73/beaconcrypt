-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked

/-! The complete checked query surface keeps routed KEM operations, common World/publication effects and raw records literal. Its native interpretation evaluates only KEM secret replies and private root descriptors. The executable symbolic frontend remains independent of the mathematical candidate parameter used here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontend
open RegistrationNativeSecretWordMessage (Message input)
open RegistrationNativeKeyCompiler (KeySpec)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {KemSK Value : Type}

abbrev Residual (n : Nat) (KemSK : Type) := RegistrationNativePairedServerService.Common n +
  (RegistrationNativeSecretWordKemInterface.Routed KemSK + PqxdhRecordLiftInterface.RecordSpec .O)
abbrev PlainSpec (n : Nat) (KemSK : Type) := KeySpec + Residual n KemSK
abbrev Spec (n : Nat) (KemSK : Type) := KeySpec + (Residual n KemSK + RegistrationNativeSecretWordChecked.AuditSpec)

def erase : QueryImpl (Spec n KemSK) (OracleComp (PlainSpec n KemSK))
  | .inl query => (PlainSpec n KemSK).query (.inl query)
  | .inr (.inl query) => (PlainSpec n KemSK).query (.inr query)
  | .inr (.inr _) => pure ()

def routedLift : QueryImpl (RegistrationNativeSecretWordKemInterface.Routed KemSK) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inr (.inl (.inr (.inl query))))

def localLift (selected : Bool) :
    QueryImpl (RegistrationNativeSecretWordChecked.Spec n KemSK) (OracleComp (Spec n KemSK))
  | .inl query => (Spec n KemSK).query (.inl query)
  | .inr (.inl (.inl query)) => (Spec n KemSK).query (.inr (.inl (.inl query)))
  | .inr (.inl (.inr query)) => simulateQ routedLift (RegistrationNativeSecretWordInterface.route selected query)
  | .inr (.inr event) => (Spec n KemSK).query (.inr (.inr event))

def implementation (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) :
    QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (OracleComp (Spec n KemSK))
  | .inl (.inl message) => simulateQ (localLift false)
      (RegistrationNativeSecretWordChecked.preparation candidate input message)
  | .inl (.inr (.inl (.inl message))) => simulateQ (localLift false)
      (RegistrationNativeSecretWordChecked.material source inside candidate input message)
  | .inl (.inr (.inl (.inr query))) => (Spec n KemSK).query (.inr (.inl (.inl query)))
  | .inl (.inr (.inr query)) => (Spec n KemSK).query (.inr (.inl (.inr (.inl query))))
  | .inr query => (Spec n KemSK).query (.inr (.inl (.inr (.inr query))))

def realization (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
      (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))
  | .inl (.inl message) => Option.map (RegistrationNativeSecretWordMessage.eval candidate) <$>
      (RegistrationNativeSecretWordInterface.Spec n KemSK).query (.inl (.inl (RegistrationNativeSecretWordMessage.literal message)))
  | .inl (.inr (.inl (.inl message))) =>
      (RegistrationNativeSecretWordInterface.Spec n KemSK).query
        (.inl (.inr (.inl (.inl (RegistrationNativeSecretWordMessage.literal message)))))
  | .inl (.inr (.inl (.inr query))) =>
      (RegistrationNativeSecretWordInterface.Spec n KemSK).query (.inl (.inr (.inl (.inr query))))
  | .inl (.inr (.inr query)) => simulateQ RegistrationNativeSecretWordInterface.routedKem
      (RegistrationNativeSecretWordKemInterface.realize candidate query)
  | .inr query => (RegistrationNativeSecretWordInterface.Spec n KemSK).query (.inr query)

def native (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (OracleComp (Spec n KemSK)) :=
  implementation source inside candidate input ∘ₛ realization candidate

/-- Raw records and their original optional replies are forwarded once without touching any private root reference. -/
theorem record (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key)
    (query : PqxdhRecordLiftInterface.RecordQuery) :
    native (n := n) (KemSK := KemSK) source inside candidate input (.inr query) =
      (Spec n KemSK).query (.inr (.inl (.inr (.inr query)))) := by
  simp only [native, QueryImpl.compose, realization, simulateQ_spec_query, implementation]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontend.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontend.record
