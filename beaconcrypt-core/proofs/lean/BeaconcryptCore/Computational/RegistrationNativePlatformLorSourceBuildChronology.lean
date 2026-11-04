-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildChronology
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBuildChronology
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
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

variable (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "fullImpl" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State source Platform Private
private theorem no_earlier {before after : FullState} {entries : List Entry}
    (path : Path fullImpl before entries after) (handle : Nat)
    (fresh : handle = after.2.1.1.server.sessions.length) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (member : (⟨.inl (.inr (.build handle payload)), some response⟩ : Entry) ∈ entries) : False := by
  obtain ⟨left, right, recorded⟩ := List.mem_iff_append.mp member
  obtain ⟨first, last, _prior, called, later⟩ := RegistrationNativeSecretWordTargetPath.split fullImpl path left _ right recorded
  obtain ⟨ready, found,_ciphertext,_identity⟩ := RegistrationNativePlatformLorSourceResponseFields.full setup checks wire source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation serverKeyId bounds handle payload response first last called
  have step := RegistrationNativePlatformLorSourceSessions.full setup checks wire source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds (.inl (.inr (.build handle payload))) first (some response, last) called
  have suffix := RegistrationNativePlatformLorSourceSessions.path setup checks wire source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds later
  have below := (List.getElem?_eq_some_iff.mp found).1
  have size := step.1.trans suffix.1
  omega

/-- The successful original response uses the exact Ready retained by its earlier same-path accept. -/
theorem response {before first last after : FullState} {pre post : List Entry}
    (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (handle : Nat)
    (decoded : RegistrationNativeWire.readInit wire raw = some packet)
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
  have fresh := RegistrationNativePlatformLorSourceSessions.full_fresh setup checks wire source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds raw packet handle decoded first last called
  rw [List.mem_append, List.mem_cons] at member
  rcases member with earlier | equal | subsequent
  · exact (no_earlier setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation serverKeyId bounds prior handle fresh payload published earlier).elim
  · cases equal
  · obtain ⟨left, right, recorded⟩ := List.mem_iff_append.mp subsequent
    obtain ⟨buildFirst, buildLast, beforeBuild, built, afterBuild⟩ :=
      RegistrationNativeSecretWordTargetPath.split fullImpl later left _ right recorded
    obtain ⟨actual, selectedReady,_ciphertext,_identity⟩ := RegistrationNativePlatformLorSourceResponseFields.full setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation serverKeyId bounds handle payload published buildFirst buildLast built
    have slots := RegistrationNativePlatformLorSourceSessions.path setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds beforeBuild
    have equal := slots.2 handle (List.getElem?_eq_some_iff.mp stored).1 actual selectedReady
    have same : actual = ready := Option.some.inj (Option.some.inj (equal.symm.trans stored))
    subst actual
    exact ⟨buildFirst, buildLast, left, right, recorded, beforeBuild, built, afterBuild, selectedReady⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBuildChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBuildChronology.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBuildChronology.response
