-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerGetter
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment

/-! Actual successful incoming preparation carrying an atom uses the selected retained private handle. Combining that receipt with the internally derived roster/pool alignment identifies the local owner position, without conflating public owner indices and private KEM handles as an assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerPreparation
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl)
open RegistrationNativeSecretWordAtomOwnerGetter (withScalar)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeSecretWordTargetSource.implementation
  RegistrationNativeSecretWordInterpreter.handler RegistrationNativeSecretWordBeaconCompiler.collect
  RegistrationNativeSecretWordBeaconCompiler.prefixImpl RegistrationNativeSecretWordBeaconCompiler.ordinaryPrefix
  RegistrationNativeSecretWordAtomOwnerGetter.withScalar RegistrationNativeSecretWordTargetServerExecution.lower
  RegistrationNativeSecretWordTargetServerExecution.localImpl

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "localImplementation" => localImpl (n := n) setup wire route sign input inside provider outer false

/-- A successful actual incoming prepared atom reaches the same owner's private indexed decapsulation at its concrete prefix state. -/
theorem collect_handle (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (before after : Auxiliary n KemSK)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (atom : pending.collected.kem = Word.atom)
    (supported : (some pending, after) ∈ support
      ((lower (withScalar setup localImplementation scalar)
        (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated)).run before)) :
    owner.kemHandle = selected ∧ ∃ ciphertext first second,
      PqxdhPhase2InputBytes.ciphertext ciphertext = challenge ∧
      (some Word.atom, second) ∈ support
        ((lower (withScalar setup localImplementation scalar)
          (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated (.decapsulate ciphertext ()))).run first) ∧
      ∃ pair, first.2.kem.1.keys[owner.kemHandle]? = some pair := by
  have equation : lower (withScalar setup localImplementation scalar)
      (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated) =
      simulateQ (fun query => lower (withScalar setup localImplementation scalar)
        (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated query))
        (RegistrationNativeSecretWordBeaconPrepare.prepare authenticated.pending.control () () () []) := by
    rw [RegistrationNativeSecretWordBeaconCompiler.collect, RegistrationNativeSecretWordTargetServerExecution.lower_program]
  rw [equation] at supported
  have collectedAt := RegistrationNativeSecretWordAtomOwnerCollector.prepare_receipt _
    authenticated.pending.control () () () [] before after pending supported
  obtain ⟨header, first, second, word, _earlier, called, same⟩ :=
    RegistrationNativeSecretWordAtomOwnerCollector.collect_receipt _ () () () [] before after pending.collected collectedAt
  have sameWord : word = Word.atom := same.symm.trans atom
  rw [sameWord] at called
  have actual := RegistrationNativeSecretWordAtomOwnerGetter.getter_atom setup wire route sign input inside
    selected pairs publicKey challenge outer owner oneTime authenticated scalar header.ciphertext first second called
  exact ⟨actual.1, header.ciphertext, first, second, actual.2.1, called, actual.2.2⟩

/-- The selected opaque handle identifies its same actual local owner only after the proved roster alignment is applied. -/
theorem owner_index (owners : RegistrationNativePublicOwners.State source)
    (keys : List (MlKem768PublicKey × KemSK)) (index : Nat) (owner : RegistrationNativePublicOwners.Owner source)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned owners keys)
    (found : owners[index]? = some owner) (selectedHandle : owner.view.kemHandle = selected) : index = selected := by
  obtain ⟨pair, _stored, handle, _public⟩ := RegistrationNativeSecretWordTargetAlignment.owner owners keys aligned index owner found
  exact handle.symm.trans selectedHandle

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerPreparation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerPreparation.collect_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerPreparation.collect_handle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerPreparation.owner_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerPreparation.owner_index
