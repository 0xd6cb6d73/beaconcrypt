-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaSuffix
import BeaconcryptCore.Computational.RegistrationNativeIdentityEdPair
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdForwardSource
import BeaconcryptCore.Computational.RegistrationNativeInitTupleSource

/-! Actual paired request-hash controllers keep the source one-time attachment and reach identical public template markers on the same physical private source. The source hash frame derives continued active routing; no hash or signing callback law is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFingerprintSuffix
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOutgoingView (view)
open RegistrationNativeIdentitySigningPair (stripState)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "action(" query ")" => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))
local notation "callback(" censored ")" => (fun query => source(censored, action(query)))
local notation "encoder(" censored ")" => (fun fields => source(censored, Main (RegistrationNativePlatformIdentityProgram.external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields))))

/-- Paired canonical request hashes derive the same current physical template and Ready/writer suffix. -/
theorem request_hash (left right : registration.BeaconInitHash) (same : stripState left.state = stripState right.state)
    (canonicalLeft : RegistrationNativeInitStageContents.Canonical left)
    (canonicalRight : RegistrationNativeInitStageContents.Canonical right)
    (canonical : Ed25519Signature) (message : Pqxdh.Bytes)
    (attachedLeft : absBytes left.state.one_time_key = canonical.toList ++ message)
    (attachedRight : absBytes right.state.one_time_key = placeholder.toList ++ message)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (active : before.1.2.active = true) :
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromHash (callback(false)) (encoder(false)) left).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromHash (callback(true)) (encoder(true)) right).run before := by
  obtain ⟨requestLeft,requestRight,requestedLeft,requestedRight,framing,_literal⟩ :=
    RegistrationNativeIdentityCensorTemplatePair.source left right same canonicalLeft canonicalRight canonical placeholder message attachedLeft attachedRight
  exact RegistrationNativeIdentityCensorMldsaSuffix.hash setup checks representation created selected index owner placeholder reserve
    left right same requestLeft requestRight requestedLeft requestedRight framing before active

private theorem retained_one_time (pending : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconInitHash) (resumed : pending.resume reply = .ok (.HashRequested next)) :
    absBytes next.state.one_time_key = absBytes pending.state.one_time_key := by
  obtain ⟨actual, run, facts⟩ := RegistrationSigning.ed_resume_refines pending reply
  cases RustM.ok.inj (run.symm.trans resumed)
  simp only [RegistrationSigning.EdReplyTransition] at facts
  exact congrArg (fun state => absBytes state.one_time_key) facts.2.2.2

private theorem pq_rejected (pending : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (stage : pending.stage = .PqKey)
    (invalid : ¬ ∃ signed, reply = .Some signed ∧ RegistrationSigning.replyTailMatches pending reply ∧ signed.val.length = 1249) :
    pending.resume reply = .ok (.Rejected pending.state.original_control) := by
  obtain ⟨effect, actual, facts⟩ := RegistrationSigning.ed_resume_refines pending reply
  cases effect <;> simp only [RegistrationSigning.EdReplyTransition, stage] at facts
  case Rejected previous => simpa only [facts] using actual
  case Ed25519SigningRequested next => exact False.elim facts.2
  case HashRequested next =>
    cases reply with
    | none => cases facts.1
    | some signed =>
      have bytes : next.state.pq_key.val = signed.val := facts.2.2.1
      have width : signed.val.length = 1249 := (congrArg List.length bytes).symm.trans next.state.pq_key.property
      exact False.elim (invalid ⟨signed, rfl, facts.1, width⟩)

/-- The actual role-separated PQ service forwards every genuine optional reply, preserves the selected source target and composes its original resume into the concrete hash/Ready/writer suffix. -/
theorem pq (left right : registration.BeaconEd25519Signing) (same : RegistrationNativeIdentityEdPair.Same left right)
    (stage : left.stage = .PqKey) (tagged : RegistrationNativeIdentitySigningRole.Tagged left.state.started)
    (canonical : Ed25519Signature) (message : Pqxdh.Bytes)
    (targetRole : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (attachedLeft : absBytes left.state.one_time_key = canonical.toList ++ message)
    (attachedRight : absBytes right.state.one_time_key = placeholder.toList ++ message)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (held : before.1.2.target = some message) (active : before.1.2.active = true) :
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (callback(false)) (encoder(false)) left).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (callback(true)) (encoder(true)) right).run before := by
  obtain ⟨request, requestedLeft, role⟩ := RegistrationNativeIdentitySigningRole.request left tagged
  have currentRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = false := by
    simpa only [stage, RegistrationNativeIdentitySigningRole.slot] using role
  have requestedRight : right.request = .ok request := (RegistrationNativeIdentityEdPair.request left right same).symm.trans requestedLeft
  have stageRight : right.stage = .PqKey := same.2.symm.trans stage
  have started := congrArg registration.BeaconInitState.started same.1
  change left.state.started = right.state.started at started
  have controls := congrArg registration.BeaconInitState.original_control same.1
  change left.state.original_control = right.state.original_control at controls
  have matching (reply : RegistrationSigningShared.SignReply) :
      RegistrationSigning.replyTailMatches left reply ↔ RegistrationSigning.replyTailMatches right reply := by
    cases reply <;> simp only [RegistrationSigning.replyTailMatches, RegistrationSigning.signingMessageValues,
      stage, stageRight, started]
  have currentEd : (callback(false) (.inr request)).run before = (callback(true) (.inr request)).run before :=
    RegistrationNativeIdentityCensorEdForwardSource.outgoing setup checks representation created selected index owner request placeholder before message held targetRole currentRole
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [requestedLeft, requestedRight, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, map_bind]
  rw [currentEd]
  apply bind_congr_of_forall_mem_support
  intro result supported
  have kept := RegistrationNativeIdentityCensorEdForwardSource.frame setup checks representation created selected index owner request placeholder true before message held targetRole currentRole result supported
  have modes := congrArg Prod.fst kept
  have activeAfter : result.2.1.2.active = true := (congrArg RegistrationNativeIdentityCensorCompiler.Mode.active modes).trans active
  by_cases valid : ∃ signed, result.1 = .Some signed ∧ RegistrationSigning.replyTailMatches left result.1 ∧ signed.val.length = 1249
  · obtain ⟨signed, returned, admitted, width⟩ := valid
    obtain ⟨nextLeft, nextRight, resumedLeft, resumedRight, paired⟩ := RegistrationNativeIdentityEdPair.pq_key left right same signed stage
      (returned ▸ admitted) (returned ▸ (matching result.1).mp admitted) width
    conv_lhs => rw [returned, resumedLeft]
    conv_rhs => rw [returned, resumedRight]
    have nextAttachedLeft := (retained_one_time left (.Some signed) nextLeft resumedLeft).trans attachedLeft
    have nextAttachedRight := (retained_one_time right (.Some signed) nextRight resumedRight).trans attachedRight
    exact request_hash setup checks representation created selected index owner placeholder reserve nextLeft nextRight paired
      (RegistrationNativeInitTupleSource.canonical_of_resume left (.Some signed) nextLeft resumedLeft)
      (RegistrationNativeInitTupleSource.canonical_of_resume right (.Some signed) nextRight resumedRight)
      canonical message nextAttachedLeft nextAttachedRight result.2 activeAfter
  · have invalidRight : ¬ ∃ signed, result.1 = .Some signed ∧ RegistrationSigning.replyTailMatches right result.1 ∧ signed.val.length = 1249 := by
      rintro ⟨signed, returned, admitted, width⟩
      exact valid ⟨signed, returned, (matching result.1).mpr admitted, width⟩
    conv_lhs => rw [pq_rejected left result.1 stage valid]
    conv_rhs => rw [pq_rejected right result.1 stageRight invalidRight]
    simp only [controls]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFingerprintSuffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFingerprintSuffix.request_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFingerprintSuffix.request_hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFingerprintSuffix.pq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFingerprintSuffix.pq
