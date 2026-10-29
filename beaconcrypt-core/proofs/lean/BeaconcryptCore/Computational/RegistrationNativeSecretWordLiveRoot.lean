-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLocalMessage

/-! Successful actual root capabilities retain the precise live descriptor established by their checked preparation callback. Ordinary owners retain the supplied descriptor returned after their local-DH translation. These are operational receipts, including all optional preparation failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRoot
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message PrepareSpec ServerReady BeaconReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (State Provider M)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK Reader E : Type} {base : OracleSpec ι}

noncomputable def preparation (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK) :
    QueryImpl PrepareSpec (M n KemSK) :=
  fun message => handlerChecked setup wire route sign input inside provider (.inl (.inl message))

noncomputable def ordinaryPreparation (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK) :
    QueryImpl PrepareSpec (M n KemSK) := fun message =>
  match RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh localScalar message with
  | none => pure none
  | some supplied => preparation setup wire route sign input inside provider supplied

private theorem server_receipt (implementation : QueryImpl PrepareSpec (M n KemSK))
    (receipt : ∀ message reference before after, (some reference, after) ∈ support ((implementation message).run before) → after.flags reference = true)
    (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input Reader E PqxdhJointIdentity.PeerEncoding)
    (ready : ServerReady) (before after : State n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ implementation (RegistrationNativeSecretWordServerRoot.client binding collected)).run before)) :
    after.flags ready.reference = true := by
  classical
  simp only [RegistrationNativeSecretWordServerRoot.client] at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
  · simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
    obtain ⟨result, reached, equal⟩ := supported
    cases referenceShape : result.1 with
    | none => simp only [referenceShape, Option.map_none] at equal; cases equal
    | some reference =>
        simp only [referenceShape, Option.map_some, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at equal
        obtain ⟨sameReady, sameState⟩ := equal
        subst after
        cases sameReady
        apply receipt _ reference before result.2
        simpa only [← referenceShape, Prod.mk.eta] using reached

private theorem beacon_receipt (implementation : QueryImpl PrepareSpec (M n KemSK))
    (receipt : ∀ message reference before after, (some reference, after) ∈ support ((implementation message).run before) → after.flags reference = true)
    (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (ready : BeaconReady) (before after : State n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ implementation (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)).run before)) :
    after.flags ready.reference = true := by
  simp only [RegistrationNativeSecretWordBeaconRoot.client, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  cases referenceShape : result.1 with
  | none => simp only [referenceShape, Option.map_none] at equal; cases equal
  | some reference =>
      simp only [referenceShape, Option.map_some, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at equal
      obtain ⟨sameReady, sameState⟩ := equal
      subst after
      cases sameReady
      apply receipt _ reference before result.2
      simpa only [← referenceShape, Prod.mk.eta] using reached

private theorem ordinary_receipt (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (message reference : Message) (before after : State n KemSK)
    (supported : (some reference, after) ∈ support
      ((ordinaryPreparation setup localScalar wire route sign input inside provider message).run before)) :
    after.flags reference = true := by
  unfold ordinaryPreparation at supported
  cases formed : RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh localScalar message with
  | none => simp only [formed, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
  | some supplied =>
      simp only [formed] at supported
      exact (RegistrationNativeSecretWordLiveFlags.prepare_receipt setup wire route sign input inside provider supplied reference before after supported).2.1

/-- Every actual successful Server preparation establishes its stored ready descriptor's live flag. -/
theorem server (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input Reader E PqxdhJointIdentity.PeerEncoding)
    (ready : ServerReady) (before after : State n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (preparation setup wire route sign input inside provider)
        (RegistrationNativeSecretWordServerRoot.client binding collected)).run before)) :
    after.flags ready.reference = true :=
  server_receipt _ (fun message reference before after reached =>
    (RegistrationNativeSecretWordLiveFlags.prepare_receipt setup wire route sign input inside provider message reference before after reached).2.1)
    binding collected ready before after supported

/-- Every actual successful selected Beacon preparation establishes its transient ready descriptor's live flag. -/
theorem beacon (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (ready : BeaconReady) (before after : State n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (preparation setup wire route sign input inside provider)
        (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)).run before)) :
    after.flags ready.reference = true :=
  beacon_receipt _ (fun message reference before after reached =>
    (RegistrationNativeSecretWordLiveFlags.prepare_receipt setup wire route sign input inside provider message reference before after reached).2.1)
    authenticated pending ready before after supported

/-- Every ordinary-owner preparation retains the actual supplied returned descriptor and its live flag. -/
theorem ordinary_beacon (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (ready : BeaconReady) (before after : State n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (ordinaryPreparation setup localScalar wire route sign input inside provider)
        (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)).run before)) :
    after.flags ready.reference = true :=
  beacon_receipt _ (ordinary_receipt setup localScalar wire route sign input inside provider)
    authenticated pending ready before after supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRoot
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRoot.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRoot.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRoot.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRoot.beacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRoot.ordinary_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRoot.ordinary_beacon
