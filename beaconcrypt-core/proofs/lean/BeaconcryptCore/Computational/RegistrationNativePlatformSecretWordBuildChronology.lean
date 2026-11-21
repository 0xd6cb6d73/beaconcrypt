import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuild
import BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildChronology
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



open RegistrationNativeSecretWordTargetPath (Path)
open RegistrationNativeInterface (Entry)
open RegistrationNativeSecretWordMessage (ServerReady)
variable (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "fullImpl" => RegistrationNativeFullCompiler.handler setup.source.crypto
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State n KemSK source Platform

omit primitive in
private theorem build_mem (transcript : List PqxdhDeploymentInterface.Entry) (handle : Nat)
    (response : PqxdhServerRegistrationPublication.Response)
    (found : PqxdhDeploymentTranscript.buildOf transcript handle = some response) :
    ∃ payload, (⟨.inl (.inr (.build handle payload)), some response⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases value
  · cases command with
    | build index payload =>
        cases reply with
        | none => cases value
        | some encoded =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact ⟨payload, member⟩
            · cases value
    | _ => cases value
  · cases value

omit primitive in
private theorem native_build (entry : Entry) (handle : Nat) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (same : entry.erase = (⟨.inl (.inr (.build handle payload)), some response⟩ : PqxdhDeploymentInterface.Entry)) :
    entry = (⟨.inl (.inr (.build handle payload)), some response⟩ : Entry) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

omit primitive in
/-- The first successful original build is an actual successful native entry with exactly those response bytes. -/
theorem original_build (entries : List Entry) (handle : Nat)
    (response : PqxdhServerRegistrationPublication.Response)
    (found : PqxdhDeploymentTranscript.buildOf (entries.map Entry.erase) handle = some response) :
    ∃ payload, (⟨.inl (.inr (.build handle payload)), some response⟩ : Entry) ∈ entries := by
  obtain ⟨payload, member⟩ := build_mem (entries.map Entry.erase) handle response found
  obtain ⟨native, nativeMember, erased⟩ := List.mem_map.mp member
  exact ⟨payload, native_build native handle payload response erased ▸ nativeMember⟩

private theorem no_earlier {before after : FullState} {entries : List Entry}
    (path : Path fullImpl before entries after) (handle : Nat)
    (fresh : handle = after.2.1.1.server.sessions.length) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (member : (⟨.inl (.inr (.build handle payload)), some response⟩ : Entry) ∈ entries) : False := by
  obtain ⟨left, right, recorded⟩ := List.mem_iff_append.mp member
  obtain ⟨first, last, _prior, called, later⟩ := RegistrationNativeSecretWordTargetPath.split fullImpl path left _ right recorded
  obtain ⟨ready, found⟩ := RegistrationNativePlatformSecretWordBuildStored.full setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds handle payload response first last called
  have step := RegistrationNativePlatformSecretWordSessionSlotsSource.full setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds (.inl (.inr (.build handle payload))) first (some response, last) called
  have suffix := RegistrationNativePlatformSecretWordSessionSlotsSource.path setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds later
  have below := (List.getElem?_eq_some_iff.mp found).1
  have size := step.1.trans suffix.1
  omega

/-- The successful original response uses the exact Ready retained by its earlier same-path accept. -/
theorem response {before first last after : FullState} {pre post : List Entry}
    (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (handle : Nat)
    (decoded : RegistrationNativeWire.readInit (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) raw = some packet)
    (prior : Path fullImpl before pre first)
    (called : (some handle, last) ∈ support ((fullImpl (.inl (.inr (.accept raw)))).run first))
    (later : Path fullImpl last post after) (ready : ServerReady)
    (stored : last.2.1.1.server.sessions[handle]? = some (some ready))
    (payload : Option Pqxdh.Bytes) (published : PqxdhServerRegistrationPublication.Response)
    (member : (⟨.inl (.inr (.build handle payload)), some published⟩ : Entry) ∈
      pre ++ ⟨.inl (.inr (.accept raw)), some handle⟩ :: post) :
    ∃ (buildFirst buildLast : FullState) (left right : List Entry),
      post = left ++ ⟨.inl (.inr (.build handle payload)), some published⟩ :: right ∧
      Path fullImpl last left buildFirst ∧
      (some published, buildLast) ∈ support ((fullImpl (.inl (.inr (.build handle payload)))).run buildFirst) ∧
      Path fullImpl buildLast right after ∧
      buildFirst.2.1.1.server.sessions[handle]? = some (some ready) := by
  have fresh := RegistrationNativePlatformSecretWordAcceptFresh.full setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds raw packet handle decoded first last called
  rw [List.mem_append, List.mem_cons] at member
  rcases member with earlier | equal | subsequent
  · exact (no_earlier setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds prior handle fresh payload published earlier).elim
  · cases equal
  · obtain ⟨left, right, recorded⟩ := List.mem_iff_append.mp subsequent
    obtain ⟨buildFirst, buildLast, beforeBuild, built, afterBuild⟩ :=
      RegistrationNativeSecretWordTargetPath.split fullImpl later left _ right recorded
    obtain ⟨actual, selectedReady⟩ := RegistrationNativePlatformSecretWordBuildStored.full setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds handle payload published buildFirst buildLast built
    have slots := RegistrationNativePlatformSecretWordSessionSlotsSource.path setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds beforeBuild
    have equal := slots.2 handle (List.getElem?_eq_some_iff.mp stored).1 actual selectedReady
    have same : actual = ready := Option.some.inj (Option.some.inj (equal.symm.trans stored))
    subst actual
    exact ⟨buildFirst, buildLast, left, right, recorded, beforeBuild, built, afterBuild, selectedReady⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildChronology.original_build' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildChronology.original_build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildChronology.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildChronology.response
