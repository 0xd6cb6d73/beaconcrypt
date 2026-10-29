-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerGetter

/-! Successful selected-handle decapsulation of the actual Early ciphertext returns the atom from its genuine birth, including before the exposed getter. A missing current private handle returns failure; its existence is derived from the successful source reply. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerGetter
open PqxdhKemIndCca
open RegistrationNativeSecretWord (Word Key)
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordService (Combined)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

/-- A successful current selected-handle challenge decapsulation necessarily returns the protected atom, without a getter-phase or pool-existence assumption. -/
theorem provider_selected (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (before after : RegistrationNativeSecretWordKemProvider.State KemSK) (word : Word)
    (supported : (some word, after) ∈ support
      ((RegistrationNativeSecretWordKemEarly.early baseImpl kem selected pairs publicKey challenge
        (.inr (.inl (.decapsulate selected challenge)))).run before)) : word = Word.atom := by
  rcases before with ⟨before, marker⟩
  cases marker <;> cases found : before.keys[selected]? <;>
    simp [RegistrationNativeSecretWordKemEarly.early, RegistrationNativeSecretWordKemProvider.ordinary,
      RegistrationNativeSecretWordKemProvider.pool, StateT.run, found] at supported
  all_goals exact supported.1

/-- The actual full current Word interpreter preserves this forward selected-handle atom receipt with all private provider and ordinary states retained. -/
theorem getter_selected (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (before after : RegistrationNativeSecretWordInterpreter.State n KemSK) (word : Word)
    (supported : (some word, after) ∈ support
      ((RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge) outer
        (.inl (.inr (.inr (.inr (.inl (.decapsulate selected challenge))))))).run before)) : word = Word.atom := by
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset outer _ supported
  rw [RegistrationNativeSecretWordInterpreter.kem_run, support_map] at native
  obtain ⟨answer, reached, returned⟩ := native
  have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativeSecretWordService.coins _ reached
  have reply : answer.1 = some word := congrArg Prod.fst returned
  have called : (some word, answer.2) ∈ support
      ((RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
        (.inr (.inl (.decapsulate selected challenge)))).run before.kem) := by
    convert actual using 1
    exact Prod.ext reply.symm rfl
  exact provider_selected setup.baseImpl setup.kem selected pairs publicKey challenge before.kem answer.2 word called
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerGetter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerGetter.provider_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerGetter.provider_selected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerGetter.getter_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerGetter.getter_selected
