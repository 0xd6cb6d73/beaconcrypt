-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalReservedCover
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptedReports
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut

/-! The original complete causal event has a real successful parsed acceptance at a bounded all-attempt ordinal and its actual final owner. Later callbacks and future-created aliases remain eligible. The ordinary attached-verifier contract is explicit; no source/history conclusion is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCausalAttempt
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativePlatformIdentityCtxFirstBundleCut (messages)
variable {V : Type}

variable {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}

structure Attempt (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire)
    (budget : PqxdhDeploymentInterface.Budget) (calls : List (Call TypedSpec (Whole n KemSK Platform source)))
    (final : Whole n KemSK Platform source) where
  ownerIndex : Nat
  finalOwner : RegistrationNativeIdentityFrontend.Owner source
  finalFound : (owners final)[ownerIndex]? = some finalOwner
  leading : List (Call TypedSpec (Whole n KemSK Platform source))
  call : Call TypedSpec (Whole n KemSK Platform source)
  trailing : List (Call TypedSpec (Whole n KemSK Platform source))
  split : calls = leading ++ call :: trailing
  packet : registration.InitPacket
  session : Nat
  decoded : PqxdhEd25519EufCma.Phase1KeyTuple
  marked : RegistrationNativeRawRegistrationJournal.typedMark call.query call.reply = some (.accept packet (some session))
  finite : RegistrationNativeRegistrationJournalCoverage.count RegistrationNativeRegistrationJournalCoverage.IsAccept leading < budget.accept
  accepted : PqxdhEd25519EufCma.acceptPhase1Candidate joint.verify (RegistrationRootInput.candidate packet) =
    some (finalOwner.identity.publicIdentity.ed25519, decoded)
  unpublished : RegistrationNativeRegistrationMarkCausal.published wire
    (leading.filterMap (fun call => RegistrationNativeRawRegistrationJournal.typedMark call.query call.reply)) ownerIndex ≠ some decoded

private theorem native_owner (joint : PqxdhJointIdentity.Primitives) (final : Whole n KemSK Platform source)
    (owned : RegistrationNativePlatformIdentityCtxLifecycle.Owned joint (drop final))
    (position : Nat) (identity : PqxdhEd25519EufCma.Ed25519PublicKey)
    (found : (RegistrationNativePlatformOrdinaryCausalReservedCover.identities joint (drop final))[position]? = some identity) :
    ∃ selected, (owners final)[position]? = some selected ∧ selected.identity.publicIdentity.ed25519 = identity := by
  simp only [RegistrationNativePlatformOrdinaryCausalReservedCover.identities,
    RegistrationNativePlatformIdentityCtxLifecycle.native, RegistrationNativePlatformIdentityCtxMain.project,
    RegistrationNativePlatformIdentityMain.project, RegistrationNativeIdentityMainSource.project,
    RegistrationNativeIdentityRealization.owners, List.map_map] at found
  change ((owners final).map fun current =>
    (joint.publicKeys (RegistrationNativeIdentityRealization.seedFor final.2.1 current.identity)).ed25519)[position]? = some identity at found
  rw [List.getElem?_map] at found
  obtain ⟨selected, present, equal⟩ := Option.map_eq_some_iff.mp found
  change RegistrationNativeIdentityRealization.Owned joint final.2.1 (owners final) at owned
  obtain ⟨seed, stored, same⟩ := owned selected (List.mem_of_getElem? present)
  rw [RegistrationNativeIdentityRealization.seed_found final.2.1 selected.identity seed stored, ← same] at equal
  exact ⟨selected, present, equal⟩

variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


/-- Original final-owner causal failure yields its literal typed acceptance and finite public ordinal on the same complete source journal. -/
theorem causal_attempt (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : Whole n KemSK Platform source) (empty : owners before = [])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before, [])))
    (failed : RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.Historical setup.source.crypto wire
      (RegistrationNativePlatformOrdinaryCausalReservedCover.identities setup.joint (drop result.2.2.1)) result.2.1.transcript) :
    Nonempty (Attempt setup.joint wire budget result.2.2.2 result.2.2.1) := by
  have path := RegistrationNativeFullRegistrationJournal.path setup.source.crypto wire serverKeyId bounds actual mode work before result reached
  have owned : RegistrationNativePlatformIdentityCtxLifecycle.Owned setup.joint (drop result.2.2.1) := by
    apply (RegistrationNativePlatformIdentityCtxKeyJournal.path_good setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer path ?_).1
    constructor
    · change RegistrationNativeIdentityRealization.Owned setup.joint _ (owners before)
      rw [empty]
      intro owner member
      cases member
    · simp only [RegistrationNativeIdentityHistorySync.Distinct, RegistrationNativeIdentityHistorySync.handles, empty, List.map_nil, List.nodup_nil]
  have marked := RegistrationNativeRegistrationMarkCausal.historical_projection setup.source.crypto wire
    (RegistrationNativePlatformOrdinaryCausalReservedCover.identities setup.joint (drop result.2.2.1)) result.2.1.transcript failed
  obtain ⟨earlier, later, logSplit, prior, packet, session, identity, decoded, ownerIndex, earlierEq, accepted, found, unpublished⟩ := marked
  have completeLog : RegistrationNativeRegistrationLedgerLog.transcript wire result.2.1.transcript =
      prior ++ RegistrationNativeRawRegistrationJournal.Mark.accept packet (some session) :: later := by
    rw [logSplit, earlierEq, List.append_assoc]
    rfl
  obtain ⟨firstCalls, acceptedCall, lastCalls, split, projected, success, finite, _previous, _called, _following⟩ :=
    RegistrationNativeFullRegistrationJournal.acceptance setup.source.crypto wire serverKeyId bounds actual mode work before budget bounded
      result reached prior later packet session completeLog
  obtain ⟨selected, selectedAt, keyEq⟩ := native_owner setup.joint result.2.2.1 owned ownerIndex identity found
  have detached : PqxdhEd25519EufCma.acceptPhase1Candidate setup.joint.verify (RegistrationRootInput.candidate packet) =
      some (identity, decoded) := by
    unfold PqxdhDeploymentTranscript.acceptedKeys at accepted
    rw [PqxdhJointPhase1Reports.sourceAccept_eq _ setup.joint
      (PqxdhJointPhase1Reports.source_attached_adapter setup.source.crypto setup.joint setup.secretOfSeed setup.wiring shortRejects)] at accepted
    exact accepted
  exact ⟨⟨ownerIndex, selected, selectedAt, firstCalls, acceptedCall, lastCalls, split, packet, session, decoded,
    success, finite, by simpa only [keyEq] using detached, by simpa only [projected] using unpublished⟩⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCausalAttempt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCausalAttempt.causal_attempt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCausalAttempt.causal_attempt
