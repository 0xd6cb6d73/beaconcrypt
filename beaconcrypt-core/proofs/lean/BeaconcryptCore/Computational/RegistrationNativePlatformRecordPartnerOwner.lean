-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerKem
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCollector
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerPreparation

/-! An actual Beacon collector carrying an opaque atom identifies the same indexed private row and challenge ciphertext. Source metadata admission and root preparation cannot replace that collected word. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWordGenericLower (Auxiliary lower lower_run)
variable {n : Nat} {I KemSK Private : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
local notation "localImpl" => implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false

private theorem map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

include contract in
/-- The literal indexed decapsulation in the reached collector prefix identifies its selected existing row and exact challenge. -/
theorem getter_atom (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (before after : Auxiliary Private)
    (supported : (some Word.atom,after) ∈ support
      ((RegistrationNativePlatformLorSourceOwnerCollect.compiler setup implementation owner oneTime authenticated
        (.decapsulate ciphertext ())).run before)) :
    owner.kemHandle=selected ∧ PqxdhPhase2InputBytes.ciphertext ciphertext=challenge ∧
      ∃ pair,(kem before.2).1.keys[owner.kemHandle]?=some pair := by
  simp only [RegistrationNativePlatformLorSourceOwnerCollect.compiler] at supported
  rw [lower_run] at supported
  simp only [RegistrationNativeSecretWordBeaconCompiler.prefixImpl,StateT.run,simulateQ_map,
    RegistrationNativeSecretWordInterface.localKem,simulateQ_spec_query,map_apply,Functor.map_map,support_map] at supported
  obtain ⟨⟨reply,privateState⟩,called,equal⟩ := supported
  have sameReply : reply=some Word.atom := congrArg Prod.fst equal
  rw [sameReply] at called
  simp only [QueryImpl.compose,RegistrationNativeSecretWordInterface.liftLocal,
    RegistrationNativeSecretWordInterface.routedKem,RegistrationNativeSecretWordInterface.route,simulateQ_spec_query] at called
  exact RegistrationNativePlatformRecordPartnerKem.decapsulate setup selected pairs publicKey challenge implementation kem input contract
    owner.kemHandle (PqxdhPhase2InputBytes.ciphertext ciphertext) before.2 privateState called

include contract in
/-- An atom in the actual admitted collection comes from that same owner's genuine private decapsulation, retaining its reached prefix states. -/
theorem collect_handle (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before after : Auxiliary Private)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (atom : pending.collected.kem=Word.atom)
    (supported : (some pending,after) ∈ support
      ((lower localImpl (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated)).run before)) :
    owner.kemHandle=selected ∧ ∃ ciphertext first second,
      PqxdhPhase2InputBytes.ciphertext ciphertext=challenge ∧
      (some Word.atom,second) ∈ support
        ((RegistrationNativePlatformLorSourceOwnerCollect.compiler setup implementation owner oneTime authenticated
          (.decapsulate ciphertext ())).run first) ∧
      ∃ pair,(kem first.2).1.keys[owner.kemHandle]?=some pair := by
  rw [RegistrationNativePlatformLorSourceOwnerCollect.collect_run] at supported
  have collectedAt := RegistrationNativeSecretWordAtomOwnerCollector.prepare_receipt (completedBinding := authenticated.binding)
    (RegistrationNativePlatformLorSourceOwnerCollect.compiler setup implementation owner oneTime authenticated)
    authenticated.control () () () [] before after pending supported
  obtain ⟨header,first,second,word,_earlier,called,same⟩ :=
    RegistrationNativeSecretWordAtomOwnerCollector.collect_receipt _ () () () [] before after pending.collected collectedAt
  have equal : word=Word.atom := same.symm.trans atom
  rw [equal] at called
  have actual := getter_atom setup implementation selected pairs publicKey challenge kem input contract
    owner oneTime authenticated header.ciphertext first second called
  exact ⟨actual.1,header.ciphertext,first,second,actual.2.1,called,actual.2.2⟩

include contract in
/-- A successful actual source preparation with an atom retains the selected handle of its original called owner. -/
theorem prepared_handle (packet : Option registration.ResponsePacket)
    (owner afterOwner : SelectedOwner source) (ready : BeaconReady) (before after : Auxiliary Private)
    (atom : ready.reference.kem=Word.atom)
    (supported : ((.ok (some ready),afterOwner),after) ∈ support
      ((lower localImpl ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet).run owner)).run before)) :
    owner.kemHandle=selected := by
  obtain ⟨pending,oneTime,_aborted,authenticated,middle,_phase,_moved,_checked,agreed⟩ :=
    RegistrationNativePlatformLorSourceOwnerControl.preparation localImpl setup source packet owner afterOwner ready before after supported
  obtain ⟨collected,reached,called,rooted,_env⟩ :=
    RegistrationNativePlatformLorSourceOwnerControl.agreement localImpl setup owner oneTime authenticated ready middle after agreed
  have fields := RegistrationNativePlatformLorSourceOwnerKem.root_fields setup selected pairs publicKey challenge implementation kem input contract
    authenticated collected ready reached.2 after.2 rooted
  have collectedAtom : collected.collected.kem=Word.atom := by
    change (RegistrationNativeSecretWordBeaconRoot.message collected).kem=Word.atom
    rw [←fields.1]
    exact atom
  exact (collect_handle setup implementation selected pairs publicKey challenge kem input contract
    owner oneTime authenticated middle reached collected collectedAtom called).1

omit contract in
/-- The proved current row alignment converts selected private-handle provenance into the original owner's local index. -/
theorem owner_index (owners : RegistrationNativePublicOwners.State source)
    (keys : List (MlKem768PublicKey × KemSK)) (index : Nat) (owner : RegistrationNativePublicOwners.Owner source)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned owners keys)
    (found : owners[index]?=some owner) (selectedHandle : owner.view.kemHandle=selected) : index=selected :=
  RegistrationNativeSecretWordAtomOwnerPreparation.owner_index selected owners keys index owner aligned found selectedHandle

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner.getter_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner.getter_atom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner.collect_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner.collect_handle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner.prepared_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner.prepared_handle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner.owner_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner.owner_index
