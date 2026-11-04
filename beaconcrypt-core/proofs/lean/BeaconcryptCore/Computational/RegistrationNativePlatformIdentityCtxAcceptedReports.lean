-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptCandidate
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedReports
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (acceptPhase1Candidate encodedIdentity)
open RegistrationNativePlatformIdentityCtxMain (Full interpret project)
variable {n count : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
  setup.source.crypto.verify publicKey.toList bytes = none)
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
include shortRejects in
/-- Every successful literal typed Context accept validates its original detached candidate, without any owner, created-key or admission condition. -/
theorem accepted (packet : registration.InitPacket) (tokenIndex : Nat) (before after : Full n KemSK Platform source)
    (supported : (.ok (some tokenIndex), after) ∈ support
      ((interpret setup.joint (frontend (.inr (.accept packet)))).run before)) :
    ∃ identity decoded, acceptPhase1Candidate setup.joint.verify (RegistrationRootInput.candidate packet) = some (identity, decoded) := by
  unfold RegistrationNativePlatformIdentityCtxTyped.handler at supported
  rw [RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind,
    RegistrationNativePlatformIdentityCtxOrdinary.report_source, pure_bind] at supported
  change (.ok (some tokenIndex), after) ∈ support
    ((interpret setup.joint (RegistrationNativePlatformIdentityCtxOrdinary.ordinary
      (RegistrationNativePlatformCtxAccept.accept setup checks reserveRegistration source.verify representation created packet))).run before) at supported
  have mapped := Set.mem_image_of_mem (Prod.map id project) supported
  rw [← support_map, RegistrationNativePlatformIdentityCtxOrdinary.ordinary_source, Functor.map_map, support_map] at mapped
  obtain ⟨middle, reached, equal⟩ := mapped
  have output := congrArg Prod.fst equal
  change middle.1 = .ok (some tokenIndex) at output
  have sameResult : middle = (.ok (some tokenIndex), middle.2) := Prod.ext output rfl
  rw [sameResult] at reached
  exact RegistrationNativePlatformIdentityCtxAcceptCandidate.accepted setup
    (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
    shortRejects route source.verify packet checks reserveRegistration representation created tokenIndex
    ((before.1.1.context, before.1.2), before.2.2) middle.2 reached
include shortRejects in
/-- Source success covers every reserved key alias encoded in the unchanged original packet, including aliases whose rows have not yet been created. -/
theorem packet_candidate (keys : Fin count → PqxdhJointIdentity.PublicIdentity)
    (packet : registration.InitPacket) (index : Fin count) (tokenIndex : Nat) (before after : Full n KemSK Platform source)
    (matched : encodedIdentity (keys index).ed25519 = PqxdhRefinement.absBytes packet.identity_key)
    (supported : (.ok (some tokenIndex), after) ∈ support
      ((interpret setup.joint (frontend (.inr (.accept packet)))).run before)) :
    ∃ decoded, acceptPhase1Candidate setup.joint.verify (RegistrationRootInput.candidate packet) =
      some ((keys index).ed25519, decoded) := by
  obtain ⟨identity, decoded, validated⟩ := accepted setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer shortRejects packet tokenIndex before after supported
  have literal := (PqxdhEd25519EufCma.acceptPhase1Candidate_some_witness setup.joint.verify
    (RegistrationRootInput.candidate packet) identity decoded validated).1
  change PqxdhRefinement.absBytes packet.identity_key = encodedIdentity identity at literal
  have encoded := matched.trans literal
  have parsed := congrArg PqxdhEd25519EufCma.parseIdentity encoded
  simp only [PqxdhEd25519EufCma.parseIdentity_encodedIdentity, Option.some.injEq] at parsed
  exact ⟨decoded, by simpa only [parsed] using validated⟩
include shortRejects in
/-- Any unissued attached field under any unrevealed matching reserved alias gives its original same-prefix weak-EUF report at an actual successful acceptance. -/
theorem packet_cover (keys : Fin count → PqxdhJointIdentity.PublicIdentity)
    (history : PqxdhJointIdentityFreshness.GlobalState count) (packet : registration.InitPacket) (index : Fin count)
    (tokenIndex : Nat) (before after : Full n KemSK Platform source)
    (matched : encodedIdentity (keys index).ed25519 = PqxdhRefinement.absBytes packet.identity_key)
    (supported : (.ok (some tokenIndex), after) ∈ support
      ((interpret setup.joint (frontend (.inr (.accept packet)))).run before))
    (fresh : index ∉ history.reveals)
    (unissued : ∃ forgery ∈ PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate packet),
      forgery.message ∉ PqxdhJointIdentity.signedMessages (history.histories index)) :
    ∃ report ∈ PqxdhJointReservedPhase1Reports.packetReports keys packet, ∃ forgery : PqxdhJointIdentity.Forgery,
      PqxdhJointReservedPhase1Reports.translateReport setup.joint keys report history = some ⟨index, forgery⟩ ∧
      PqxdhJointIdentityEvents.ReportEvent setup.joint keys ⟨index, forgery⟩ history ∧
      forgery ∈ PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate packet) ∧
      forgery.message ∉ PqxdhJointIdentity.signedMessages (history.histories index) := by
  obtain ⟨decoded, validated⟩ := packet_candidate setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer shortRejects keys packet index tokenIndex before after matched supported
  exact PqxdhJointReservedPhase1Reports.packet_cover setup.joint keys history packet index decoded validated fresh unissued
include shortRejects in
/-- The unrestricted ghost reporter retains this actual successful-accept field cover and the same complete source poststate. -/
theorem wrapped_cover (keys : Fin count → PqxdhJointIdentity.PublicIdentity)
    (history : PqxdhJointIdentityFreshness.GlobalState count) (packet : registration.InitPacket) (index : Fin count)
    (tokenIndex : Nat) (before after : Full n KemSK Platform source)
    (matched : encodedIdentity (keys index).ed25519 = PqxdhRefinement.absBytes packet.identity_key)
    (supported : (.ok (some tokenIndex), after) ∈ support
      ((RegistrationNativePlatformIdentityCtxReservedReports.callback setup.joint
        (RegistrationNativePlatformIdentityCtxReservedReports.wrap keys frontend) (.inr (.accept packet))).run before))
    (fresh : index ∉ history.reveals)
    (unissued : ∃ forgery ∈ PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate packet),
      forgery.message ∉ PqxdhJointIdentity.signedMessages (history.histories index)) :
    ∃ report ∈ PqxdhJointReservedPhase1Reports.packetReports keys packet, ∃ forgery : PqxdhJointIdentity.Forgery,
      PqxdhJointReservedPhase1Reports.translateReport setup.joint keys report history = some ⟨index, forgery⟩ ∧
      PqxdhJointIdentityEvents.ReportEvent setup.joint keys ⟨index, forgery⟩ history ∧
      forgery ∈ PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate packet) ∧
      forgery.message ∉ PqxdhJointIdentity.signedMessages (history.histories index) := by
  rw [RegistrationNativePlatformIdentityCtxReservedReports.query_source] at supported
  change (.ok (some tokenIndex), after) ∈ support
    ((interpret setup.joint (frontend (.inr (.accept packet)))).run before) at supported
  exact packet_cover setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer shortRejects keys history packet index tokenIndex before after matched supported fresh unissued

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports.accepted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports.packet_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports.packet_candidate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports.packet_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports.packet_cover
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports.wrapped_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports.wrapped_cover
