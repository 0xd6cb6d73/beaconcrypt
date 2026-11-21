-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorInactiveTail
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdForwardSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource

/-! A stale selected one-time message declines selection and forwards the exact honest signature. The complete original source marginal then follows through the inactive actual PQ-Ed/hash/writer tail. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleOriginal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] registration.BeaconEd25519Signing.resume
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
variable (writer : registration.InitView → StateT Platform ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "callback" => (fun query => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query)))
local notation "encoder" => (fun fields => Main (RegistrationNativePlatformIdentityProgram.external (writer fields)))

private theorem one_time_message (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .OneTimeKey) :
    TranscriptAuthParts.absSlice request.message = PqxdhRefinement.absBytes pending.state.started.message.one_time_key := by
  obtain ⟨actual, run, _publicKey, _role, message⟩ := RegistrationSigning.ed_request_exact pending
  cases RustM.ok.inj (run.symm.trans requested)
  exact congrArg (List.map PqxdhRefinement.absByte) (by simpa only [RegistrationSigning.signingMessageValues, stage] using message)

private theorem attached (pending : registration.BeaconEd25519Signing) (signature : Ed25519Signature)
    (next : registration.BeaconEd25519Signing) (stage : pending.stage = .OneTimeKey)
    (resumed : pending.resume (.Some (RegistrationNativeIdentityCensorReply.buffer signature pending.state.started.message.one_time_key).to_slice) =
      .ok (.Ed25519SigningRequested next)) :
    PqxdhRefinement.absBytes next.state.one_time_key = signature.toList ++ PqxdhRefinement.absBytes pending.state.started.message.one_time_key := by
  obtain ⟨actual, run, facts⟩ := RegistrationSigning.ed_resume_refines pending
    (.Some (RegistrationNativeIdentityCensorReply.buffer signature pending.state.started.message.one_time_key).to_slice)
  cases RustM.ok.inj (run.symm.trans resumed)
  simp only [RegistrationSigning.EdReplyTransition, stage] at facts
  have copied := congrArg (List.map PqxdhRefinement.absByte) facts.2.2.1
  simpa [RegistrationSigning.replyValues, PqxdhRefinement.absBytes, RegistrationNativeIdentityCensorReply.buffer, Std.Array.to_slice,
    List.map_append, List.map_map, Function.comp_def] using copied



private def after (selected index : Nat) (message : Pqxdh.Bytes) (signature : Ed25519Signature)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource) :=
  ((RegistrationNativePlatformIdentityCtxEdOutgoing.updated index message (some signature) before.1.1,
      {before.1.2 with active := false}),
    {before.2 with pool := PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message))) (some signature) before.2.pool})

private theorem interpret_run {A : Type} (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret joint selected placeholder false work).run before = (do
      let result ← (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2
      pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) := rfl

private theorem operational_sign (selected : Nat) (placeholder : Ed25519Signature) (handle : Nat) (message : Pqxdh.Bytes)
    (before : RegistrationNativeIdentityCensorCompiler.Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder
      (.inl (.inl (.inr (.service handle (.sign message)))))).run before =
      (RegistrationNativeIdentityCensorOperational.signing selected handle message).run before := rfl

private theorem stale_current (selected : Nat) (placeholder : Ed25519Signature)
    (request : registration.Ed25519SigningRequest)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (key : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (role : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (stale : TranscriptAuthParts.absSlice request.message ∈ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    (interpret setup.joint selected placeholder false (callback (.inr request))).run before =
      pure (RegistrationAuthenticationShared.openedBytes
          (some ((setup.joint.sign seed (TranscriptAuthParts.absSlice request.message)).toList ++ TranscriptAuthParts.absSlice request.message)),
        after selected index (TranscriptAuthParts.absSlice request.message) (setup.joint.sign seed (TranscriptAuthParts.absSlice request.message)) before) := by
  subst selected
  rw [interpret_run, RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
  simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, key, ite_true,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  simp only [operational_sign]
  have forwarded := RegistrationNativeIdentityCensorStaleSource.signing_found setup.joint owner.identity.handle placeholder false
    (TranscriptAuthParts.absSlice request.message) before.1.2 before.2 role held sourceTarget stale seed found
  simp only [Bool.false_eq_true, ite_false] at forwarded
  rw [forwarded]
  rfl
/-- A previously signed selected message forwards its exact honest reply, declines selection and preserves the original full source marginal through its actual remaining callbacks. -/
theorem one_time (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .OneTimeKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (held : before.1.2.target = none)
    (sourceTarget : before.2.target = none)
    (stale : PqxdhRefinement.absBytes pending.state.started.message.one_time_key ∈ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (RegistrationNativePlatformBeaconPublication.fromEd
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromEd
        (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  let message := PqxdhRefinement.absBytes pending.state.started.message.one_time_key
  let canonical := setup.joint.sign seed message
  have messageEq := one_time_message pending request requested stage
  have actualRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true := by
    rw [messageEq]
    exact tagged.2.1
  have issued : TranscriptAuthParts.absSlice request.message ∈ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript) := messageEq.symm ▸ stale
  have real := stale_current setup checks representation created index owner selected placeholder request before seed
    handle publicKey actualRole held sourceTarget issued found
  rw [messageEq] at real
  have honest := RegistrationNativeIdentityCensorRealSigning.outgoing setup checks representation created selected index owner request placeholder before
  dsimp only at honest
  rw [real, map_pure] at honest
  have admitted := RegistrationNativeIdentityCensorReply.admitted pending canonical stage
  obtain ⟨next, resumed, nextStage, _copied, _restored⟩ := RegistrationNativeIdentityEdProgress.one_time pending
    (RegistrationNativeIdentityCensorReply.buffer canonical pending.state.started.message.one_time_key).to_slice stage admitted.1 admitted.2
  have copied := attached pending canonical next stage resumed
  have nextTagged := RegistrationNativeIdentitySigningRole.preserved pending tagged _ _ resumed
  change RegistrationNativeIdentitySigningRole.Tagged next.state.started at nextTagged
  rw [← RegistrationNativeIdentityCensorReply.packed canonical _] at resumed
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, map_bind]
  rw [real, ← honest]
  simp only [pure_bind, Prod.map, id_eq]
  rw [resumed]
  exact RegistrationNativeIdentityCensorInactiveTail.pq setup checks representation created index owner writer selected placeholder
    next nextStage nextTagged
    (after selected index message canonical before) held rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleOriginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleOriginal.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleOriginal.one_time
