-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFingerprintSuffix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorReply

/-! The selected actual one-time source call supplies the two original Core continuations. Its canonical private receipt is shared, current reply bytes remain distinct, and the complete failed-publication suffix is compared after only the previously proved stored-log projection. This is a source-stage theorem, not the finite causal-event probability bound. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret after)
open RegistrationNativeIdentityCensorOutgoingView (view)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

private theorem after_view (selected index : Nat) (message : Pqxdh.Bytes) (canonical placeholder : Ed25519Signature)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    view placeholder (after selected index message canonical canonical before) =
      view placeholder (after selected index message canonical placeholder before) := by
  unfold view RegistrationNativePlatformIdentityCtxTypedJointView.view after
  have same := RegistrationNativePlatformIdentityCtxEdOutgoing.projected_append placeholder canonical placeholder index message before.1.1
  exact congrArg (fun native => ((RegistrationNativePlatformIdentityCtxReceiptView.view native,
    {before.1.2 with active := true}), {before.2 with
      pool := PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message))) (some canonical) before.2.pool
      canonical := some canonical})) same

private theorem one_time_message (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .OneTimeKey) :
    TranscriptAuthParts.absSlice request.message = absBytes pending.state.started.message.one_time_key := by
  obtain ⟨actual, run, _publicKey, _role, message⟩ := RegistrationSigning.ed_request_exact pending
  cases RustM.ok.inj (run.symm.trans requested)
  exact congrArg (List.map absByte) (by simpa only [RegistrationSigning.signingMessageValues, stage] using message)

private theorem attached (pending : registration.BeaconEd25519Signing) (signature : Ed25519Signature)
    (next : registration.BeaconEd25519Signing) (stage : pending.stage = .OneTimeKey)
    (resumed : pending.resume (.Some (RegistrationNativeIdentityCensorReply.buffer signature pending.state.started.message.one_time_key).to_slice) =
      .ok (.Ed25519SigningRequested next)) :
    absBytes next.state.one_time_key = signature.toList ++ absBytes pending.state.started.message.one_time_key := by
  obtain ⟨actual, run, facts⟩ := RegistrationSigning.ed_resume_refines pending
    (.Some (RegistrationNativeIdentityCensorReply.buffer signature pending.state.started.message.one_time_key).to_slice)
  cases RustM.ok.inj (run.symm.trans resumed)
  simp only [RegistrationSigning.EdReplyTransition, stage] at facts
  have copied := congrArg (List.map absByte) facts.2.2.1
  simpa [RegistrationSigning.replyValues, absBytes, RegistrationNativeIdentityCensorReply.buffer, Std.Array.to_slice,
    List.map_append, List.map_map, Function.comp_def] using copied

private theorem observed_stable {S A B : Type} (project : S → S) (observe : A → B)
    (work : StateT S ProbComp A) (stable : RegistrationNativePlatformViewStable.Stable project work) (before : S) :
    Prod.map observe project <$> work.run before = Prod.map observe project <$> work.run (project before) := by
  have same := congrArg (fun distribution => Prod.map observe id <$> distribution) (stable before)
  simpa only [Functor.map_map, Prod.map_def, id_eq] using same

section Actual
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

/-- The actual selected canonical service receipt and its placeholder delivery drive the original complete failed source-publication controller with identical remaining native/private/P observation. -/
theorem one_time (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .OneTimeKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (held : before.1.2.target = some (absBytes pending.state.started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes pending.state.started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (callback(false)) (encoder(false)) pending).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (callback(true)) (encoder(true)) pending).run before := by
  let message := absBytes pending.state.started.message.one_time_key
  let canonical := setup.joint.sign seed message
  have messageEq := one_time_message pending request requested stage
  have actualHeld : before.1.2.target = some (TranscriptAuthParts.absSlice request.message) := messageEq.symm ▸ held
  have actualSourceTarget : before.2.target = some (TranscriptAuthParts.absSlice request.message) := messageEq.symm ▸ sourceTarget
  have actualRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true := by rw [messageEq]; exact tagged.2.1
  have real := RegistrationNativeIdentityCensorEdOutgoingSource.real setup checks representation created selected index owner request placeholder before seed handle publicKey actualHeld actualSourceTarget actualRole found
  have censored := RegistrationNativeIdentityCensorEdOutgoingSource.censored setup checks representation created selected index owner request placeholder before seed handle publicKey actualHeld actualSourceTarget actualRole found
  rw [messageEq] at real censored
  have leftAdmitted := RegistrationNativeIdentityCensorReply.admitted pending canonical stage
  have rightAdmitted := RegistrationNativeIdentityCensorReply.admitted pending placeholder stage
  obtain ⟨nextLeft, nextRight, resumedLeft, resumedRight, nextStage, paired⟩ := RegistrationNativeIdentityEdPair.one_time pending
    (RegistrationNativeIdentityCensorReply.buffer canonical pending.state.started.message.one_time_key).to_slice
    (RegistrationNativeIdentityCensorReply.buffer placeholder pending.state.started.message.one_time_key).to_slice
    stage leftAdmitted.1 rightAdmitted.1 leftAdmitted.2 rightAdmitted.2
  have attachedLeft := attached pending canonical nextLeft stage resumedLeft
  have attachedRight := attached pending placeholder nextRight stage resumedRight
  have nextTagged := RegistrationNativeIdentitySigningRole.preserved pending tagged _ _ resumedLeft
  change RegistrationNativeIdentitySigningRole.Tagged nextLeft.state.started at nextTagged
  rw [← RegistrationNativeIdentityCensorReply.packed canonical _] at resumedLeft
  rw [← RegistrationNativeIdentityCensorReply.packed placeholder _] at resumedRight
  dsimp only [canonical, message] at resumedLeft resumedRight
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, map_bind]
  rw [real, censored]
  simp only [pure_bind]
  rw [resumedLeft, resumedRight]
  let beforeLeft := after selected index message canonical canonical before
  let beforeRight := after selected index message canonical placeholder before
  change Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (callback(false)) (encoder(false)) nextLeft).run beforeLeft =
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (callback(true)) (encoder(true)) nextRight).run beforeRight
  calc
    _ = Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
        (RegistrationNativePlatformBeaconPublication.fromEd (callback(false)) (encoder(false)) nextLeft).run (view placeholder beforeLeft) :=
      observed_stable (view placeholder) RegistrationNativeIdentityReadyFailure.observe _
        (RegistrationNativeIdentityCensorMldsaSuffix.ed_stable setup checks representation created selected index owner placeholder reserve false nextLeft) beforeLeft
    _ = Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
        (RegistrationNativePlatformBeaconPublication.fromEd (callback(false)) (encoder(false)) nextLeft).run (view placeholder beforeRight) := by
      rw [after_view selected index message canonical placeholder before]
    _ = Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
        (RegistrationNativePlatformBeaconPublication.fromEd (callback(true)) (encoder(true)) nextRight).run (view placeholder beforeRight) :=
      RegistrationNativeIdentityCensorFingerprintSuffix.pq setup checks representation created selected index owner placeholder reserve
        nextLeft nextRight paired nextStage nextTagged canonical message tagged.2.1 attachedLeft attachedRight
        (view placeholder beforeRight) held rfl
    _ = _ := (observed_stable (view placeholder) RegistrationNativeIdentityReadyFailure.observe _
      (RegistrationNativeIdentityCensorMldsaSuffix.ed_stable setup checks representation created selected index owner placeholder reserve true nextRight) beforeRight).symm
end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedSource.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedSource.one_time
