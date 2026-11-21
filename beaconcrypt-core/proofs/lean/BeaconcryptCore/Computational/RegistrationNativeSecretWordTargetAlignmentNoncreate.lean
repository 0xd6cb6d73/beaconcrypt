-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterSame
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreatePublic

/-! Every concrete nonconstructor callback preserves current owner/private-key alignment. The zero-birth footprint is derived from the actual symbolic controllers and the current pool law is the early provider's literal law, independently of all outer material-table replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentNoncreate
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

/-- Actual nonconstructor typed calls retain every current private pair. -/
theorem typed_keys (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State n KemSK source) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) :
    result.2.2.kem.1.keys = before.2.kem.1.keys := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have free := RegistrationNativeSecretWordTargetNoCreatePublic.handler_bound (n := n) setup checks wire source sign
    selectedOwner selectedAccept publicPrekey query before.1
  rw [ite_eq_right quiet] at free
  have retained := RegistrationNativeSecretWordTargetPoolFrame.program_keys setup wire route sign input inside
    selected pairs publicKey challenge outer _ free before.2 reached called
  cases equal
  exact retained

/-- Actual nonconstructor typed calls retain the complete ordered public KEM metadata. -/
theorem typed_metadata (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State n KemSK source) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) :
    result.2.1.beacons.map key = before.1.beacons.map key := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have original : reached.1 ∈ support
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
        selectedOwner selectedAccept publicPrekey query).run before.1) := by
    apply OracleComp.support_simulateQ_run'_subset implementation _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  cases equal
  exact RegistrationNativeSecretWordTargetRosterSame.typed_same setup checks wire sign
    selectedOwner selectedAccept publicPrekey query quiet before.1 reached.1 original

/-- Nonconstructor preservation follows from the actual private-key and public-roster projections, with no alignment hypothesis on arbitrary handlers. -/
theorem typed_aligned (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State n KemSK source) (prior : Aligned before.1.beacons before.2.kem.1.keys)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) :
    Aligned result.2.1.beacons result.2.2.kem.1.keys := by
  rw [typed_keys setup checks wire route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey query quiet before result supported]
  exact RegistrationNativeSecretWordTargetAlignment.same before.1.beacons result.2.1.beacons before.2.kem.1.keys prior
    (typed_metadata setup checks wire route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey query quiet before result supported)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentNoncreate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentNoncreate.typed_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentNoncreate.typed_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentNoncreate.typed_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentNoncreate.typed_metadata
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentNoncreate.typed_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentNoncreate.typed_aligned
