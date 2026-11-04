-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleFixed
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxJournalFirst
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCausalAttempt
import BeaconcryptCore.Computational.RegistrationNativeIdentityAcceptedOneTimeCover

/-! The original final-owner causal event has an actual finite accept attempt and either an original unissued verified field at that same prefix or a finite strict earlier first signing of its accepted one-time field. Both fixed keys belong to the same final generated handle; public keys may alias and that owner may have been created after the accept. This functional cover is not an identification with a reserved-family probability experiment. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativePlatformIdentityCtxCausalAttempt (Attempt)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativePlatformIdentityCtxFirstBundleCut (messages)
open PqxdhEd25519EufCma (prekeyMessage pqMessage oneTimeMessage)
variable {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}

/-- This is the original attached field, its actual public verification, and its same-prefix private source history. No unrevealed-family event is inferred here. -/
def Unissued {joint : PqxdhJointIdentity.Primitives} {wire : RegistrationNativeWire.Wire}
    {budget : PqxdhDeploymentInterface.Budget} {calls : List (Call TypedSpec (Whole n KemSK Platform source))}
    {final : Whole n KemSK Platform source} (attempt : Attempt joint wire budget calls final) : Prop :=
  ∃ forgery ∈ PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate attempt.packet),
    joint.verify attempt.finalOwner.identity.publicIdentity.ed25519 forgery.message forgery.signature = true ∧
    forgery.message ∉ messages attempt.finalOwner.identity.handle attempt.call.before

structure FirstCut {joint : PqxdhJointIdentity.Primitives} {wire : RegistrationNativeWire.Wire}
    {budget : PqxdhDeploymentInterface.Budget} {calls : List (Call TypedSpec (Whole n KemSK Platform source))}
    {final : Whole n KemSK Platform source} (attempt : Attempt joint wire budget calls final) where
  leading : List (Call TypedSpec (Whole n KemSK Platform source))
  call : Call TypedSpec (Whole n KemSK Platform source)
  trailing : List (Call TypedSpec (Whole n KemSK Platform source))
  split : attempt.leading = leading ++ call :: trailing
  index : Nat
  queryEq : call.query = .inr (.bundle index)
  fresh : oneTimeMessage attempt.decoded.oneTime ∉ messages attempt.finalOwner.identity.handle call.before
  signed : oneTimeMessage attempt.decoded.oneTime ∈ messages attempt.finalOwner.identity.handle call.after
  finite : call.before.1.2.nextBundle < budget.bundle

structure Issued {joint : PqxdhJointIdentity.Primitives} {wire : RegistrationNativeWire.Wire}
    {budget : PqxdhDeploymentInterface.Budget} {calls : List (Call TypedSpec (Whole n KemSK Platform source))}
    {final : Whole n KemSK Platform source} (attempt : Attempt joint wire budget calls final) where
  fixedPrekey : attempt.decoded.prekey = PqxdhPhase2InputBytes.word attempt.finalOwner.prekeyPublic
  fixedPq : attempt.decoded.pqKey = attempt.finalOwner.kemPublic
  cut : FirstCut attempt

def acceptanceOrdinal {joint : PqxdhJointIdentity.Primitives} {wire : RegistrationNativeWire.Wire}
    {budget : PqxdhDeploymentInterface.Budget} {calls : List (Call TypedSpec (Whole n KemSK Platform source))}
    {final : Whole n KemSK Platform source} (attempt : Attempt joint wire budget calls final) : Fin budget.accept :=
  ⟨RegistrationNativeRegistrationJournalCoverage.count RegistrationNativeRegistrationJournalCoverage.IsAccept attempt.leading, attempt.finite⟩

def bundleOrdinal {joint : PqxdhJointIdentity.Primitives} {wire : RegistrationNativeWire.Wire}
    {budget : PqxdhDeploymentInterface.Budget} {calls : List (Call TypedSpec (Whole n KemSK Platform source))}
    {final : Whole n KemSK Platform source} {attempt : Attempt joint wire budget calls final} (cut : FirstCut attempt) : Fin budget.bundle :=
  ⟨cut.call.before.1.2.nextBundle, cut.finite⟩

variable {V : Type}
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


/-- Every message actually issued before the accepted attempt obeys the exact final owner's fixed-key policy. -/
theorem message_fixed (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) (empty : before.1.beacons = [])
    (physical : RegistrationNativePlatformCtxBackend.State)
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)), [])))
    (attempt : Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (message : Pqxdh.Bytes) (signed : message ∈ messages attempt.finalOwner.identity.handle attempt.call.before) :
    RegistrationNativeEdKeyPolicy.Allowed (PqxdhPhase2InputBytes.word attempt.finalOwner.prekeyPublic) attempt.finalOwner.kemPublic message := by
  obtain ⟨leading, chosen, trailing, index, split, _previous, called, _following, queryEq, freshAt, signedAt, _finite⟩ :=
    RegistrationNativePlatformIdentityCtxJournalFirst.first_before setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget bounded before physical result reached
      attempt.leading attempt.trailing attempt.call attempt.split attempt.finalOwner.identity.handle message signed
  have member : chosen ∈ result.2.2.2 := by
    rw [attempt.split, split]
    simp only [List.mem_append, List.mem_cons, true_or, or_true]
  exact RegistrationNativePlatformIdentityCtxFirstBundleFixed.full_new_fixed setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work ((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) empty result reached
    chosen member called index queryEq attempt.finalOwner.identity.handle message freshAt signedAt attempt.finalOwner
    (List.mem_of_getElem? attempt.finalFound) rfl

/-- Every accepted field family is either originally unissued or has the actual fixed prekey/PQ and a strict earlier finite first one-time signing cut. -/
theorem attempt_cover (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) (empty : before.1.beacons = [])
    (physical : RegistrationNativePlatformCtxBackend.State)
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)), [])))
    (attempt : Attempt setup.joint wire budget result.2.2.2 result.2.2.1) :
    Unissued attempt ∨ Nonempty (Issued attempt) := by
  classical
  by_cases unused : ∃ forgery ∈ PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate attempt.packet),
      forgery.message ∉ messages attempt.finalOwner.identity.handle attempt.call.before
  · obtain ⟨forgery, member, fresh⟩ := unused
    exact Or.inl ⟨forgery, member, PqxdhJointPhase1Reports.acceptedFields_valid setup.joint _ _ _ attempt.accepted forgery member, fresh⟩
  · have allIssued : ∀ forgery ∈ PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate attempt.packet),
        forgery.message ∈ messages attempt.finalOwner.identity.handle attempt.call.before := by
      intro forgery member
      by_contra fresh
      exact unused ⟨forgery, member, fresh⟩
    obtain ⟨_encoded, pqSignature, preSignature, oneSignature, pqAttached, _pqVerified,
      preAttached, _preVerified, oneAttached, _oneVerified⟩ := PqxdhEd25519EufCma.acceptPhase1Candidate_some_witness
        setup.joint.verify _ _ _ attempt.accepted
    have preMember : (⟨prekeyMessage attempt.decoded.prekey, preSignature⟩ : PqxdhJointIdentity.Forgery) ∈
        PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate attempt.packet) := by
      simp [PqxdhJointPhase1Reports.candidateFields, pqAttached, preAttached, oneAttached]
    have pqMember : (⟨pqMessage attempt.decoded.pqKey, pqSignature⟩ : PqxdhJointIdentity.Forgery) ∈
        PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate attempt.packet) := by
      simp [PqxdhJointPhase1Reports.candidateFields, pqAttached, preAttached, oneAttached]
    have preAllowed := message_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode work budget bounded before empty physical result reached attempt _ (allIssued _ preMember)
    have pqAllowed := message_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode work budget bounded before empty physical result reached attempt _ (allIssued _ pqMember)
    obtain ⟨preEq, pqEq⟩ := RegistrationNativeEdKeyPolicy.decoded_fixed _ _ _ _ preAllowed pqAllowed
    obtain ⟨signature, oneMember, _valid⟩ := RegistrationNativeIdentityAcceptedOneTimeCover.field setup.joint _ _ _ attempt.accepted
    have oneIssued := allIssued (⟨oneTimeMessage attempt.decoded.oneTime, signature⟩ : PqxdhJointIdentity.Forgery) oneMember
    obtain ⟨leading, chosen, trailing, index, split, _previous, _called, _following, queryEq, freshAt, signedAt, finite⟩ :=
      RegistrationNativePlatformIdentityCtxJournalFirst.first_before setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget bounded before physical result reached
        attempt.leading attempt.trailing attempt.call attempt.split attempt.finalOwner.identity.handle _ oneIssued
    exact Or.inr ⟨⟨preEq, pqEq, ⟨leading, chosen, trailing, split, index, queryEq, freshAt, signedAt, finite⟩⟩⟩

/-- The original complete final-owner event has this finite same-run field/first-bundle cover, including future-created aliases and failed calls. -/
theorem causal_cover (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) (empty : before.1.beacons = [])
    (physical : RegistrationNativePlatformCtxBackend.State)
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)), [])))
    (failed : RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.Historical setup.source.crypto wire
      (RegistrationNativePlatformOrdinaryCausalReservedCover.identities setup.joint (drop result.2.2.1)) result.2.1.transcript) :
    ∃ attempt : Attempt setup.joint wire budget result.2.2.2 result.2.2.1, Unissued attempt ∨ Nonempty (Issued attempt) := by
  obtain ⟨attempt⟩ := RegistrationNativePlatformIdentityCtxCausalAttempt.causal_attempt setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer shortRejects serverKeyId bounds mode work budget bounded ((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) empty result reached failed
  exact ⟨attempt, attempt_cover setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer serverKeyId bounds mode work budget bounded before empty physical result reached attempt⟩

/-- A returned first-cut witness retains its exact original source prefix, supported callback and complete suffix. -/
theorem full_cut_paths (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source)
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before, [])))
    (attempt : Attempt setup.joint wire budget result.2.2.2 result.2.2.1) (cut : FirstCut attempt) :
    Path actual before cut.leading cut.call.before ∧ Executed actual cut.call ∧
      Path actual cut.call.after (cut.trailing ++ attempt.call :: attempt.trailing) result.2.2.1 := by
  have path := RegistrationNativeFullRegistrationJournal.path setup.source.crypto wire serverKeyId bounds actual mode work before result reached
  have split : result.2.2.2 = cut.leading ++ cut.call :: (cut.trailing ++ attempt.call :: attempt.trailing) := by
    calc
      result.2.2.2 = attempt.leading ++ attempt.call :: attempt.trailing := attempt.split
      _ = (cut.leading ++ cut.call :: cut.trailing) ++ attempt.call :: attempt.trailing :=
        congrArg (fun leading => leading ++ attempt.call :: attempt.trailing) cut.split
      _ = _ := by rw [List.append_assoc]; rfl
  rw [split] at path
  exact RegistrationNativeRegistrationJournalCoverage.path_split actual _ _ _ _ _ path

/-- A reserved-family interpretation of the final same-run pool supplies its exact finite generated-handle index. This is a representation corollary, not a probability-game identification. -/
theorem reserved_cover (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) (empty : before.1.beacons = [])
    (physical : RegistrationNativePlatformCtxBackend.State)
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)), [])))
    (failed : RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.Historical setup.source.crypto wire
      (RegistrationNativePlatformOrdinaryCausalReservedCover.identities setup.joint (drop result.2.2.1)) result.2.1.transcript)
    (seeds : Fin budget.create → PqxdhJointIdentity.IdentitySeed) (router : PqxdhDynamicIdentityRouting.PublicState)
    (capacity : router.created ≤ budget.create)
    (pool : result.2.2.1.2.1 = PqxdhDynamicIdentityRouting.sourceState seeds router) :
    ∃ attempt : Attempt setup.joint wire budget result.2.2.2 result.2.2.1, ∃ identity : Fin budget.create,
      identity.val = attempt.finalOwner.identity.handle ∧
      attempt.finalOwner.identity.publicIdentity = setup.joint.publicKeys (seeds identity) ∧
      (Unissued attempt ∨ Nonempty (Issued attempt)) := by
  obtain ⟨attempt, branch⟩ := causal_cover setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer shortRejects serverKeyId bounds mode work budget bounded before empty physical result reached failed
  have path := RegistrationNativeFullRegistrationJournal.path setup.source.crypto wire serverKeyId bounds actual mode work _ result reached
  have owned : RegistrationNativePlatformIdentityCtxLifecycle.Owned setup.joint (drop result.2.2.1) := by
    apply (RegistrationNativePlatformIdentityCtxKeyJournal.path_good setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer path ?_).1
    constructor
    · change RegistrationNativeIdentityRealization.Owned setup.joint _ before.1.beacons
      rw [empty]
      intro owner member
      cases member
    · simp only [RegistrationNativeIdentityHistorySync.Distinct, RegistrationNativeIdentityHistorySync.handles, owners, empty, List.map_nil, List.nodup_nil]
  obtain ⟨identity, handleEq, publicEq⟩ := RegistrationNativePlatformIdentityCtxReservedOwners.owner setup.joint seeds router capacity
    (drop result.2.2.1) owned pool attempt.finalOwner (List.mem_of_getElem? attempt.finalFound)
  exact ⟨attempt, identity, handleEq, publicEq, branch⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover.message_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover.message_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover.attempt_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover.attempt_cover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover.causal_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover.causal_cover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover.full_cut_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover.full_cut_paths

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover.reserved_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover.reserved_cover
