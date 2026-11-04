-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceHistory
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand
/-! The actual complete corrected Word client derives every protected literal recovery receipt from its own same-run demand, with empty initial one-use sessions. The internally proved new-source preparation invariant supplies all flags. No caller preparation, success or chronological-log law is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasServiceClient
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

open RegistrationNativePlatformSecretWordAliasClient (Result)
open RegistrationNativeSecretWordRecoveryCompiler (closed literals)
open RegistrationNativeSecretWordFrontendTrace (Event)
open RegistrationNativeSuffixKeyPrf (Secret)

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (route : RawCtxServerRouting.SenderDecoder) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

variable (empty : before.1.server.sessions = []) (candidate : Secret)
    (result : Result source n KemSK A Platform × RegistrationNativeSecretWordRecoveryCompiler.State)
local notation "actual" => RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  route input inside provider serverKeyId bounds mode work before ordinary kem
local notation "bare" => RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  serverKeyId bounds mode work before
variable (supported : result ∈ support (RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
  (RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider
    serverKeyId bounds mode work before ordinary kem)))
include supported empty setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route provider serverKeyId bounds mode work ordinary kem

/-- Every valid protected literal demand in the actual new source chronology is logged by its own concrete key request. -/
theorem demands_logged :
    RegistrationNativeSecretWordAliasServiceHistory.Holds input inside candidate result.1.1.2 result.2.2 := by
  apply RegistrationNativeSecretWordAliasServiceHistory.program setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    route sign input inside provider candidate bare
    (RegistrationNativeSecretWordInterpreter.initial ordinary kem) RegistrationNativeSecretWordFrontendTrace.initial (∅, [])
  · intro message key member
    cases member
  · exact RegistrationNativeSecretWordPreparedTransfer.program setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      route sign input inside provider _ _
      (RegistrationNativePlatformSecretWordLiveSafety.run setup wire route sign input inside provider checks source selectedOwner selectedAccept
        publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before empty ordinary kem)
  · exact supported

/-- A literal at an actual successful or failed installation has its earlier same-run demand and appears in the final recovery log. -/
theorem install_logged (role : PqxdhRecordLiftInterface.Role) (message : Message) (key : Key)
    (member : Event.install role message ∈ result.1.1.2.events ∨ Event.installAttempt role message ∈ result.1.1.2.events)
    (realized : input message = some key) (protectedInput : inside key.head = true)
    (literal : key.word = .literal candidate) : candidate ∈ result.2.2 := by
  have possible : result.1 ∈ support actual := by
    apply OracleComp.support_simulateQ_run'_subset (RawCtxSelectedQueryTrace.recorded (closed setup.source candidate) literals) _ (∅, [])
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have observed : result.1.1 ∈ support (RegistrationNativeSecretWordFrontendTrace.program bare) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeSecretWordInterpreter.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider)
      _ (RegistrationNativeSecretWordInterpreter.initial ordinary kem)
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst possible
  have trace := RegistrationNativeSecretWordAtomTraceDemand.program bare RegistrationNativeSecretWordFrontendTrace.initial
    (by simp [RegistrationNativeSecretWordAtomTraceDemand.Holds, RegistrationNativeSecretWordFrontendTrace.initial]) result.1.1 observed
  have demanded : Event.demand message ∈ result.1.1.2.events := by
    rcases member with installed | attempted
    · exact trace.2 (.install role message) installed message (List.mem_singleton_self _)
    · exact trace.2 (.installAttempt role message) attempted message (List.mem_singleton_self _)
  exact demands_logged setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer route input inside provider serverKeyId bounds mode work before ordinary kem empty candidate result supported
    message key demanded realized protectedInput literal

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasServiceClient

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasServiceClient.demands_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasServiceClient.demands_logged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasServiceClient.install_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasServiceClient.install_logged
