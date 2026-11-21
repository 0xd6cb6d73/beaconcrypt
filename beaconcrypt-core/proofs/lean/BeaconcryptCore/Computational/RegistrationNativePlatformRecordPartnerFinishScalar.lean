-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwner
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerRoot
/-! Actual ordinary-owner scalar substitution preserves the collected KEM word and the same indexed private decapsulation under arbitrary persistent source state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWordGenericLower (Auxiliary lower lower_run)
open RegistrationNativeSecretWordInterface (LocalSpec localKem liftLocal)
variable {n : Nat} {I KemSK Private : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
local notation "localImpl" => implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false

noncomputable def scalarLocal (scalar : Option PqxdhJointGapDh.ScalarBytes) : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp) :=
  match scalar with
  | none=>localImpl
  | some scalar=>localImpl ∘ₛ RegistrationNativeSecretWordOwners.ordinary setup scalar

private theorem map_apply {S A B : Type} (change : A → B) (work : StateT S ProbComp A) (before : S) :
    (change <$> work) before=Prod.map change id <$> work before := StateT.run_map _ _ _

include contract in
private theorem plain_echo (message reference : Message) (before after : Private)
    (supported : (some reference,after)∈support ((implementation (.inl (.inl message))).run before)) : reference=message := by
  have echo := (contract.prepare message before (some reference,after) supported).1
  cases formed : input message with
  | none=>simp only [formed,Option.map_none] at echo; cases echo
  | some key=>
      simp only [formed,Option.map_some] at echo
      exact Option.some.inj echo

include contract in
theorem query_kem (scalar : Option PqxdhJointGapDh.ScalarBytes) (message reference : Message)
    (before after : Private)
    (supported : (some reference, after) ∈ support
      (((scalarLocal setup implementation scalar) (.inl message)).run before)) : reference.kem = message.kem := by
  cases scalar with
  | none =>
      have actual : (some reference, after) ∈ support ((implementation (.inl (.inl message))).run before) := by
        simpa only [scalarLocal, QueryImpl.compose, RegistrationNativeSecretWordInterface.liftLocal,
          simulateQ_spec_query] using supported
      exact congrArg Message.kem (plain_echo setup implementation selected pairs publicKey challenge kem input contract message reference before after actual)
  | some scalar =>
      simp only [scalarLocal, QueryImpl.compose, RegistrationNativeSecretWordOwners.ordinary] at supported
      cases formed : RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh scalar message with
      | none => simp only [formed, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
      | some translated =>
          have actual : (some reference, after) ∈ support ((implementation (.inl (.inl translated))).run before) := by
            simpa only [formed, simulateQ_spec_query, QueryImpl.compose,
              RegistrationNativeSecretWordInterface.liftLocal, simulateQ_spec_query] using supported
          exact (congrArg Message.kem (plain_echo setup implementation selected pairs publicKey challenge kem input contract translated reference before after actual)).trans
            (RegistrationNativeSecretWordAtomOwnerRoot.materialize_kem setup scalar message translated formed)

include contract in
/-- A successful actual root client keeps the atom or literal from the same successfully collected input on both owner paths. -/
theorem client_kem (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (ready : BeaconReady) (before after : Private)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (scalarLocal setup implementation scalar)
        (simulateQ RegistrationNativeSecretWordInterface.prepare
          (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run before)) :
    ready.reference.kem = pending.collected.kem := by
  simp only [RegistrationNativeSecretWordBeaconRoot.client, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    RegistrationNativeSecretWordInterface.prepare, StateT.run_map, support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  cases referenceShape : result.1 with
  | none => simp only [referenceShape, Option.map_none] at equal; cases equal
  | some reference =>
      simp only [referenceShape, Option.map_some, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at equal
      obtain ⟨sameReady, _sameState⟩ := equal
      cases sameReady
      apply query_kem setup implementation selected pairs publicKey challenge kem input contract scalar
        (RegistrationNativeSecretWordBeaconRoot.message pending) reference before result.2
      simpa only [← referenceShape, Prod.mk.eta] using reached


private theorem getter_run (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (before : Auxiliary Private) :
    (lower (scalarLocal setup implementation scalar)
      (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated (.decapsulate ciphertext ()))).run before =
      (fun result => (result.1, ({ before.1 with requests := before.1.requests ++ RegistrationWorldAgreement.recorded (.decapsulate (.Some ciphertext)) }, result.2))) <$>
        (implementation (.inl (.inr (.inr (.inr (.inl (.decapsulate owner.kemHandle
          (PqxdhPhase2InputBytes.ciphertext ciphertext)))))))).run before.2 := by
  rw [RegistrationNativeSecretWordGenericLower.lower_run]
  cases scalar <;>
    simp only [RegistrationNativeSecretWordBeaconCompiler.prefixImpl, StateT.run, simulateQ_map, map_apply,
      scalarLocal, QueryImpl.compose, localKem, simulateQ_spec_query,
      RegistrationNativeSecretWordOwners.ordinary, liftLocal, RegistrationNativeSecretWordInterface.route,
      RegistrationNativeSecretWordInterface.routedKem, Functor.map_map, Prod.map_def, id_eq]
  all_goals rfl

include contract in
/-- The actual lowered optional getter retains the same owner's operand and current private-pool witness on both owner paths. -/
theorem getter_atom (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (before after : Auxiliary Private)
    (supported : (some Word.atom, after) ∈ support
      ((lower (scalarLocal setup implementation scalar)
        (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated (.decapsulate ciphertext ()))).run before)) :
    owner.kemHandle = selected ∧ PqxdhPhase2InputBytes.ciphertext ciphertext = challenge ∧
      ∃ pair, (kem before.2).1.keys[owner.kemHandle]? = some pair := by
  rw [getter_run] at supported
  rw [support_map] at supported
  obtain ⟨result, called, returned⟩ := supported
  rcases result with ⟨replyValue, last⟩
  have reply : replyValue = some Word.atom := congrArg Prod.fst returned
  subst replyValue
  exact RegistrationNativePlatformRecordPartnerKem.decapsulate setup selected pairs publicKey challenge implementation kem input contract
    owner.kemHandle (PqxdhPhase2InputBytes.ciphertext ciphertext) before.2 last called


include contract in
/-- The scalar adapter changes no actual collected atom provenance at its original indexed private row. -/
theorem collect_handle (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (before after : Auxiliary Private)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (atom : pending.collected.kem = Word.atom)
    (supported : (some pending, after) ∈ support
      ((lower (scalarLocal setup implementation scalar)
        (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated)).run before)) :
    owner.kemHandle = selected ∧ ∃ ciphertext first second,
      PqxdhPhase2InputBytes.ciphertext ciphertext = challenge ∧
      (some Word.atom, second) ∈ support
        ((lower (scalarLocal setup implementation scalar)
          (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated (.decapsulate ciphertext ()))).run first) ∧
      ∃ pair, (kem first.2).1.keys[owner.kemHandle]? = some pair := by
  have equation : lower (scalarLocal setup implementation scalar)
      (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated) =
      simulateQ (fun query => lower (scalarLocal setup implementation scalar)
        (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated query))
        (RegistrationNativeSecretWordBeaconPrepare.prepare (completedBinding := authenticated.binding) authenticated.control () () () []) := by
    unfold RegistrationNativeSecretWordBeaconCompiler.collect
    exact RegistrationNativePlatformLorIdealStateLift.simulate (scalarLocal setup implementation scalar) _ _
  rw [equation] at supported
  have collectedAt := RegistrationNativeSecretWordAtomOwnerCollector.prepare_receipt (completedBinding := authenticated.binding) _
    authenticated.control () () () [] before after pending supported
  obtain ⟨header, first, second, word, _earlier, called, same⟩ :=
    RegistrationNativeSecretWordAtomOwnerCollector.collect_receipt _ () () () [] before after pending.collected collectedAt
  have sameWord : word = Word.atom := same.symm.trans atom
  rw [sameWord] at called
  have actual := getter_atom setup implementation selected pairs publicKey challenge kem input contract owner oneTime authenticated scalar header.ciphertext first second called
  exact ⟨actual.1, header.ciphertext, first, second, actual.2.1, called, actual.2.2⟩


include contract in
/-- Both actual incoming owner scalar paths retain the selected private handle in every successful atom preparation, with all enclosing failures and environment states preserved. -/
theorem prepared_handle (scalar : Option PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket)
    (owner afterOwner : SelectedOwner source) (ready : BeaconReady) (before after : Auxiliary Private)
    (atom : ready.reference.kem=Word.atom)
    (supported : ((.ok (some ready),afterOwner),after)∈support
      ((lower (scalarLocal setup implementation scalar)
        ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet).run owner)).run before)) :
    owner.kemHandle=selected := by
  obtain ⟨pending,oneTime,_aborted,authenticated,middle,_phase,_moved,_checked,agreed⟩ :=
    RegistrationNativePlatformLorSourceOwnerControl.preparation (scalarLocal setup implementation scalar) setup source packet owner afterOwner ready before after supported
  obtain ⟨collected,reached,called,rooted,_env⟩ := RegistrationNativePlatformLorSourceOwnerControl.agreement
    (scalarLocal setup implementation scalar) setup owner oneTime authenticated ready middle after agreed
  have sameKem := client_kem setup implementation selected pairs publicKey challenge kem input contract scalar authenticated collected ready reached.2 after.2 rooted
  exact (collect_handle setup implementation selected pairs publicKey challenge kem input contract owner oneTime authenticated scalar middle reached
    collected (sameKem.symm.trans atom) called).1

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar.query_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar.query_kem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar.client_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar.client_kem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar.getter_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar.getter_atom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar.collect_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar.collect_handle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar.prepared_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar.prepared_handle
