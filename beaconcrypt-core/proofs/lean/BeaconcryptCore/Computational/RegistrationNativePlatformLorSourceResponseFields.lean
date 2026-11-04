-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields
import BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport
/-! The actual current moved-token response keeps the same stored Ready ciphertext and configured Server identity in its concrete source-encoded bytes. Every callback, provider and persistent platform poststate is retained on the literal typed/raw/full execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPath (Path)
open RegistrationNativeInterface (Entry)
open PqxdhKemIndCca
open PqxdhDeploymentTranscript (summarize)
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets

abbrev State (source : RegistrationNativeMldsa.Source) (Platform Private : Type) :=
  RegistrationNativePlatformLorStatefulSupport.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller

/-- Private interpretation keeps the same response fields and exact pre-call stored Ready. -/
theorem typed_fields (handle : Nat) (application : Option (Slice U8)) (before after : State source Platform Private)
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId,bytes)),after) ∈ support ((typed (.inr (.build handle application))).run before)) :
    ∃ ready, before.1.1.server.sessions[handle]?=some (some ready) ∧
      RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse ready.agreement.pending.kem_ciphertext bytes ∧
      RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse before.1.1.server.pin.binding.identity_public_key bytes :=
  RegistrationNativePlatformResponseSourceFields.frontend setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
    handle application before.1 after.1 keyId bytes
    (RegistrationNativePlatformLorStatefulSupport.typed_support implementation controller
      (.inr (.build handle application)) before (.ok (some (keyId,bytes)),after) supported)

/-- Every successful original raw response retains those same source fields. -/
theorem raw (handle : Nat) (application : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (before after : State source Platform Private)
    (supported : (some response,after) ∈ support ((RegistrationNativeRawAdapter.handler wire typed (.inr (.build handle application))).run before)) :
    ∃ ready, before.1.1.server.sessions[handle]?=some (some ready) ∧
      RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse ready.agreement.pending.kem_ciphertext response.serialized ∧
      RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse before.1.1.server.pin.binding.identity_public_key response.serialized :=
  typed_fields setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation handle (RegistrationNativeRawAdapter.application application)
    before after response.keyId response.serialized
    (RegistrationNativeTargetRawSuccess.build wire typed handle application response before after supported)

/-- The complete original ledger success binds its response to the same current moved token, not to a reconstructed or later Ready. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (handle : Nat) (application : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (before after : RegistrationNativeLedger.State × State source Platform Private)
    (supported : (some response,after) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
      (.inl (.inr (.build handle application)))).run before)) :
    ∃ ready, before.2.1.1.server.sessions[handle]?=some (some ready) ∧
      RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse ready.agreement.pending.kem_ciphertext response.serialized ∧
      RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse before.2.1.1.server.pin.binding.identity_public_key response.serialized := by
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
  obtain ⟨⟨reply,current⟩,reached,returned⟩ := supported
  have success : reply=some response := congrArg Prod.fst returned
  subst reply
  exact raw setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation handle application response before.2 current reached
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields.typed_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields.typed_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields.full
