import BeaconcryptCore.Computational.RegistrationNativeTargetRawSuccess
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath
/-! The current full Word source consumes the early KEM reservation in exact birth order under its original public create allowance. The current source-derived constructor cap rules out fallback; no final-owner activation or private row association is supplied as a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
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
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativePlatformSecretWordAliasAlignment (State)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller



/-- A successful actual free source build can only use a Ready present at its literal initial one-use take. -/
theorem frontend (handle : Nat) (application : Option (Slice U8)) (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (after : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId,bytes)),after) ∈ support ((controller (.inr (.build handle application))).run before)) :
    ∃ ready, before.1.server.sessions[handle]?=some (some ready) := by
  simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordFrontend.build,
    StateT.run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have returned : RegistrationNativePlatformPublicFrontend.responseBytes reached.1.1=.ok (some (keyId,bytes)) := congrArg Prod.fst equal
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  cases stored : before.1.server.sessions[handle]? with
  | none =>
    simp only [RegistrationNativePlatformSecretWordBuild.body,RegistrationNativePlatformSecretWordBuildControl.build,
      RegistrationNativeSecretWordServerMaterial.take,stored] at original
    cases original
    cases returned
  | some entry => cases entry with
    | none =>
      simp only [RegistrationNativePlatformSecretWordBuild.body,RegistrationNativePlatformSecretWordBuildControl.build,
        RegistrationNativeSecretWordServerMaterial.take,stored] at original
      cases original
      cases returned
    | some ready => exact ⟨ready,rfl⟩

/-- The same interpreted typed success retains that exact pre-call capability lookup. -/
theorem typed_stored (handle : Nat) (application : Option (Slice U8)) (before after : State n KemSK source Platform)
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId,bytes)),after) ∈ support ((typed (.inr (.build handle application))).run before)) :
    ∃ ready, before.1.1.server.sessions[handle]?=some (some ready) :=
  frontend setup checks wire source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    handle application before.1 after.1 keyId bytes
    (RegistrationNativePlatformSecretWordExecution.typed_support setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      route sign input inside provider outer controller (.inr (.build handle application)) before (.ok (some (keyId,bytes)),after) supported)

/-- Successful original raw responses use the same existing Ready even when earlier source allocations fail. -/
theorem raw (handle : Nat) (application : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (before after : State n KemSK source Platform)
    (supported : (some response,after) ∈ support ((RegistrationNativeRawAdapter.handler
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) typed (.inr (.build handle application))).run before)) :
    ∃ ready, before.1.1.server.sessions[handle]?=some (some ready) :=
  typed_stored setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer handle (RegistrationNativeRawAdapter.application application)
    before after response.keyId response.serialized
    (RegistrationNativeTargetRawSuccess.build (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) typed handle application response before after supported)

/-- The complete original ledger success retains the same pre-call session lookup. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (handle : Nat) (application : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (before after : RegistrationNativeLedger.State × State n KemSK source Platform)
    (supported : (some response,after) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds typed (.inl (.inr (.build handle application)))).run before)) :
    ∃ ready, before.2.1.1.server.sessions[handle]?=some (some ready) := by
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
  obtain ⟨⟨reply,current⟩,reached,returned⟩ := supported
  have success : reply=some response := congrArg Prod.fst returned
  subst reply
  exact raw setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer handle application response before.2 current reached

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored.frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored.frontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored.typed_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored.typed_stored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored.full
