import BeaconcryptCore.Computational.RegistrationNativePlatformResponseControlFields
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativeTargetRawSuccess
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
-- SPDX-License-Identifier: 0BSD
/-! The actual current moved-token response keeps the same stored Ready ciphertext and configured Server identity in its concrete source-encoded bytes. Every callback, provider and persistent platform poststate is retained on the literal typed/raw/full execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPath (Path)
open RegistrationNativeInterface (Entry)
open PqxdhKemIndCca
open PqxdhDeploymentTranscript (summarize)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets

open RegistrationNativePlatformSecretWordAliasAlignment (State)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign input inside provider outer controller


/-- The exact current free build returns an encoding of its same stored Ready and configured Server identity. -/
theorem frontend (handle : Nat) (application : Option (Slice U8))
    (before after : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId,bytes)),after) ∈ support ((controller (.inr (.build handle application))).run before)) :
    ∃ ready, before.1.server.sessions[handle]?=some (some ready) ∧
      RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse
        ready.agreement.pending.kem_ciphertext bytes ∧
      RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse
        before.1.server.pin.binding.identity_public_key bytes := by
  simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordFrontend.build,
    StateT.run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have returned : RegistrationNativePlatformPublicFrontend.responseBytes reached.1.1=.ok (some (keyId,bytes)) := congrArg Prod.fst equal
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  cases actual : reached.1.1 with
  | fail error | div => simp [RegistrationNativePlatformPublicFrontend.responseBytes,actual] at returned
  | ok optional => cases optional with
    | none => simp [RegistrationNativePlatformPublicFrontend.responseBytes,actual] at returned
    | some pair =>
      rcases pair with ⟨actualKey,vector⟩
      have fields := RegistrationNativePlatformResponseControlFields.body (n := n) setup.source view failure allocation erased helper sign reservePackets reservePeer
        handle application before.1.server reached.1.2 (before.1.environment.receipts,before.2) reached.2 actualKey vector
        (by simpa only [StateT.run,←actual,Prod.mk.eta] using original)
      simp only [RegistrationNativePlatformPublicFrontend.responseBytes,actual,bind_tc_ok,Option.map_some,
        RustM.ok.injEq,Option.some.injEq,Prod.mk.injEq] at returned
      obtain ⟨_key,bytesEq⟩ := returned
      rw [bytesEq] at fields
      exact fields

/-- Private interpretation keeps the same response fields and exact pre-call stored Ready. -/
theorem typed_fields (handle : Nat) (application : Option (Slice U8)) (before after : State n KemSK source Platform)
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId,bytes)),after) ∈ support ((typed (.inr (.build handle application))).run before)) :
    ∃ ready, before.1.1.server.sessions[handle]?=some (some ready) ∧
      RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse ready.agreement.pending.kem_ciphertext bytes ∧
      RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse before.1.1.server.pin.binding.identity_public_key bytes :=
  frontend setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
    handle application before.1 after.1 keyId bytes
    (RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller
      (.inr (.build handle application)) before (.ok (some (keyId,bytes)),after) supported)

/-- Every successful original raw response retains those same source fields. -/
theorem raw (handle : Nat) (application : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (before after : State n KemSK source Platform)
    (supported : (some response,after) ∈ support ((RegistrationNativeRawAdapter.handler wire typed (.inr (.build handle application))).run before)) :
    ∃ ready, before.1.1.server.sessions[handle]?=some (some ready) ∧
      RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse ready.agreement.pending.kem_ciphertext response.serialized ∧
      RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse before.1.1.server.pin.binding.identity_public_key response.serialized :=
  typed_fields setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets handle (RegistrationNativeRawAdapter.application application)
    before after response.keyId response.serialized
    (RegistrationNativeTargetRawSuccess.build wire typed handle application response before after supported)

/-- The complete original ledger success binds its response to the same current moved token, not to a reconstructed or later Ready. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (handle : Nat) (application : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (before after : RegistrationNativeLedger.State × State n KemSK source Platform)
    (supported : (some response,after) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
      (.inl (.inr (.build handle application)))).run before)) :
    ∃ ready, before.2.1.1.server.sessions[handle]?=some (some ready) ∧
      RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse ready.agreement.pending.kem_ciphertext response.serialized ∧
      RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse before.2.1.1.server.pin.binding.identity_public_key response.serialized := by
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
  obtain ⟨⟨reply,current⟩,reached,returned⟩ := supported
  have success : reply=some response := congrArg Prod.fst returned
  subst reply
  exact raw setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets handle application response before.2 current reached
end BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields.frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields.frontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields.typed_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields.typed_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseSourceFields.full
