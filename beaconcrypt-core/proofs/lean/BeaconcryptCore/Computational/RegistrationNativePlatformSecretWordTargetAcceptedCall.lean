-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetAcceptedCall
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAcceptedCall
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



open RegistrationNativePlatformSecretWordExecution (TracedState drop)
open RegistrationNativeSecretWordTargetCall (Call)
open RegistrationNativeSecretWordTargetPath (Path)
local notation "traceState" => TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK
local notation "traceTyped" => RegistrationNativePlatformSecretWordExecution.traced (n := n) setup
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller

/-- The trace counter is the same actual parsed counter, with full private state retained by pointwise erasure. -/
theorem traced_counter (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : traceState)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × traceState)
    (supported : result ∈ support ((traceTyped query).run before)) :
    result.2.1.1.parsedAccepts = before.1.1.parsedAccepts + (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat := by
  have mapped := Set.mem_image_of_mem (Prod.map id drop) supported
  rw [← support_map, RegistrationNativePlatformSecretWordExecution.traced_source] at mapped
  exact RegistrationNativePlatformSecretWordTargetLedgerCounter.typed_counter setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    query (drop before) (result.1,drop result.2) mapped

/-- The actual original raw run supplies its same parsed accept, absent getter marker, exact prefix and entire callback suffix. -/
theorem accepted_call (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : traceState)
    (initialCounter : before.1.1.parsedAccepts = 0) (initialMarker : before.2.2.kem.2 = none)
    (result : A × (RegistrationNativeLedger.State × traceState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped mode work before))
    (session : Nat)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) result.2.1.transcript session selectedAccept) :
    ∃ call : Call traceState traceTyped (fun current => current.1.1.parsedAccepts)
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) selectedAccept result.2.1.transcript session,
      call.first.2.2.kem.2 = none ∧
      ∃ first last : RegistrationNativeLedger.State × traceState,
        call.first = first.2 ∧ call.last = last.2 ∧
        Path (RegistrationNativeFullCompiler.handler setup.source.crypto
          (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped)
          (RegistrationNativeLedger.empty,before) call.pre first ∧
        (some session,last) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto
          (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped
          (.inl (.inr (.accept call.raw)))).run first) ∧
        Path (RegistrationNativeFullCompiler.handler setup.source.crypto
          (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped)
          last call.post result.2 := by
  have actual := (RegistrationNativePlatformSecretWordTargetPath.run setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller
    serverKeyId bounds mode work before result supported).1
  obtain ⟨call,first,last,firstEq,lastEq,prior,called,suffix⟩ :=
    RegistrationNativeRegistrationTargetAcceptedCall.accepted_call setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) traceTyped (fun current => current.1.1.parsedAccepts)
      (traced_counter setup checks wire source route sign input inside selected pairs publicKey challenge outer
        selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
      serverKeyId bounds before initialCounter result.2 actual session selectedAccept accepted
  have plain := RegistrationNativePlatformSecretWordTargetPath.path setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller
    serverKeyId bounds prior
  have phase := RegistrationNativeSecretWordTargetPath.preserves _
    (fun current => RegistrationNativePlatformSecretWordTargetPhase.Holds selectedAccept current.2)
    (fun query current next valid reached => RegistrationNativePlatformSecretWordTargetPhase.full_step_keeps
      setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      serverKeyId bounds query current next valid reached) plain (fun _ => initialMarker)
  have ordinal : first.2.1.1.parsedAccepts = selectedAccept := by
    rw [←firstEq]
    exact call.selected
  have absent : call.first.2.2.kem.2 = none := by
    rw [firstEq]
    exact phase (Nat.le_of_eq ordinal)
  exact ⟨call,absent,first,last,firstEq,lastEq,prior,called,suffix⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAcceptedCall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAcceptedCall.traced_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAcceptedCall.traced_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAcceptedCall.accepted_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAcceptedCall.accepted_call
