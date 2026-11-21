-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolPrefix

/-! Final public owner lookup identifies the same reserved private pair under the original create allowance. The complete actual symbolic frontend and original secrecy ledger supply both the roster alignment and the reservation prefix; neither is assumed as an event-simulation condition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem prefix_lookup (pairs keys : List (MlKem768PublicKey × KemSK))
    (prefixed : keys = pairs.take keys.length) (index : Nat) (pair : MlKem768PublicKey × KemSK)
    (found : keys[index]? = some pair) : pairs[index]? = some pair := by
  have earlier := (List.getElem?_eq_some_iff.mp found).1
  rw [prefixed, List.getElem?_take, ite_eq_left earlier] at found
  exact found

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer

/-- Closing the actual symbolic frontend preserves current roster alignment through the same literal original ledger source equation. -/
theorem frontend_aligned (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativeSecretWordMessage.State source) (ownersEmpty : frontend.beacons = [])
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (keysEmpty : before.kem.1.keys = [])
    (result : ((Value × RegistrationNativeLedger.State) × RegistrationNativeSecretWordMessage.State source) ×
      RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ implementation
      (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work frontend)).run before)) :
    RegistrationNativeSecretWordTargetAlignment.Aligned result.1.2.beacons result.2.kem.1.keys := by
  have mapped := Set.mem_image_of_mem
    (fun reached => (reached.1.1.1, (reached.1.1.2, (reached.1.2, reached.2)))) supported
  rw [← support_map] at mapped
  rw [RegistrationNativeSecretWordTargetSource.run_source setup checks wire route sign input inside
    provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work (frontend, before)] at mapped
  exact RegistrationNativeSecretWordTargetAlignmentRun.initialized setup checks wire route sign input inside
    selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work
    (frontend, before) ownersEmpty keysEmpty _ mapped

/-- Every retained final owner has its same indexed reserved pair, even when it was created after the selected accept or finished before the selected getter. -/
theorem born_key (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (frontend : RegistrationNativeSecretWordMessage.State source) (ownersEmpty : frontend.beacons = [])
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (keysEmpty : before.kem.1.keys = [])
    (result : ((Value × RegistrationNativeLedger.State) × RegistrationNativeSecretWordMessage.State source) ×
      RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ implementation
      (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work frontend)).run before))
    (index : Nat) (owner : RegistrationNativePublicOwners.Owner source)
    (found : result.1.2.beacons[index]? = some owner) :
    ∃ pair, pairs[index]? = some pair ∧ owner.view.kemHandle = index ∧ owner.view.kemPublic = pair.1 := by
  have aligned := frontend_aligned setup checks wire route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work frontend ownersEmpty before keysEmpty result supported
  obtain ⟨pair, privateAt, handle, sameKey⟩ := RegistrationNativeSecretWordTargetAlignment.owner
    result.1.2.beacons result.2.kem.1.keys aligned index owner found
  have prefixed := (RegistrationNativeSecretWordTargetPoolPrefix.run_prefix setup wire route sign input inside selected pairs publicKey challenge outer
    checks selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work budget bounded reserved frontend before keysEmpty result supported).1
  exact ⟨pair, prefix_lookup pairs result.2.kem.1.keys prefixed index pair privateAt, handle, sameKey⟩

/-- The same reserved birth receipt holds directly on the original full native ledger and its actual complete poststate. -/
theorem full_born_key (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (before : RegistrationNativeSecretWordTargetSource.State n KemSK source)
    (ownersEmpty : before.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (result : Value × (RegistrationNativeLedger.State × RegistrationNativeSecretWordTargetSource.State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer
        selectedOwner selectedAccept publicPrekey) mode work before))
    (index : Nat) (owner : RegistrationNativePublicOwners.Owner source) (found : result.2.2.1.beacons[index]? = some owner) :
    ∃ pair, pairs[index]? = some pair ∧ owner.view.kemHandle = index ∧ owner.view.kemPublic = pair.1 := by
  rw [← RegistrationNativeSecretWordTargetSource.run_source setup checks wire route sign input inside provider outer
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  exact born_key setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    serverKeyId bounds mode work budget bounded reserved before.1 ownersEmpty before.2 keysEmpty reached called index owner found

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey.frontend_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey.frontend_aligned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey.born_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey.born_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey.full_born_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey.full_born_key
