-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail
import BeaconcryptCore.Computational.RegistrationNativeInitTupleSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdForwardSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource

/-! The actual Ed stages retain the canonical one-time attachment used by the literal source hash. The private real-marker execution projects to the ordinary source at the same callbacks; no selected signature or seed enters an executable reduction constructor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealEdSource
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

/-- The role-separated PQ request cannot alter the selected one-time memo. Every actual optional reply either rejects normally or carries the same canonical attachment into the checked request-hash/writer source suffix. -/
theorem pq (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconEd25519Signing) (stage : pending.stage = .PqKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (signature : Ed25519Signature) (message : Pqxdh.Bytes)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (attached : PqxdhRefinement.absBytes pending.state.one_time_key = signature.toList ++ message)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (held : before.1.2.target = some message) (stored : before.2.canonical = some signature) (active : before.1.2.active = true) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (RegistrationNativePlatformBeaconPublication.fromEd
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromEd
        (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  obtain ⟨request, requested, requestRole⟩ := RegistrationNativeIdentitySigningRole.request pending tagged
  have currentRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = false := by
    simpa only [stage, RegistrationNativeIdentitySigningRole.slot] using requestRole
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, map_bind]
  have current := RegistrationNativeIdentityCensorRealSigning.outgoing setup checks representation created selected index owner request placeholder before
  dsimp only at current
  rw [← current, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨reply, after⟩ reached
  have frame := RegistrationNativeIdentityCensorEdForwardSource.frame setup checks representation created selected index owner request placeholder false before message held role currentRole (reply, after) reached
  have stillStored : after.2.canonical = some signature := (congrArg (fun value => value.2.canonical) frame).trans stored
  have stillActive : after.1.2.active = true := (congrArg (fun value => value.1.active) frame).trans active
  obtain ⟨effect, resumed, facts⟩ := RegistrationSigning.ed_resume_refines pending reply
  simp only [Prod.map, id_eq]
  rw [resumed]
  cases effect <;> simp only [RegistrationSigning.EdReplyTransition, stage] at facts
  case Rejected previous => simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  case Ed25519SigningRequested next => exact False.elim facts.2
  case HashRequested next =>
    have retained := congrArg (fun state : registration.BeaconInitState => PqxdhRefinement.absBytes state.one_time_key) facts.2.2.2
    change PqxdhRefinement.absBytes next.state.one_time_key = PqxdhRefinement.absBytes pending.state.one_time_key at retained
    exact RegistrationNativeIdentityCensorRealTail.request_hash setup checks representation created index owner writer selected placeholder
      next (RegistrationNativeInitTupleSource.canonical_of_resume pending reply next resumed) signature message (retained.trans attached) after stillStored stillActive

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


/-- A matching selected one-time call derives the canonical attachment before the original PQ-Ed/hash/Ready/writer suffix, including repeated target messages. -/
theorem one_time (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .OneTimeKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (held : before.1.2.target = some (PqxdhRefinement.absBytes pending.state.started.message.one_time_key))
    (sourceTarget : before.2.target = some (PqxdhRefinement.absBytes pending.state.started.message.one_time_key))
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
  have actualHeld : before.1.2.target = some (TranscriptAuthParts.absSlice request.message) := messageEq.symm ▸ held
  have actualSourceTarget : before.2.target = some (TranscriptAuthParts.absSlice request.message) := messageEq.symm ▸ sourceTarget
  have actualRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true := by
    rw [messageEq]
    exact tagged.2.1
  have real := RegistrationNativeIdentityCensorEdOutgoingSource.real setup checks representation created selected index owner request placeholder before seed
    handle publicKey actualHeld actualSourceTarget actualRole found
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
  exact pq setup checks representation created index owner writer selected placeholder next nextStage nextTagged
    canonical message tagged.2.1 copied
    (RegistrationNativeIdentityCensorEdOutgoingSource.after selected index message canonical canonical before) held rfl rfl

/-- The first fresh selected one-time call performs its actual source selection, then has the same honest-source marginal as the literal original controller. No selected target is supplied before that source call. -/
theorem first_one_time (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .OneTimeKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : PqxdhRefinement.absBytes pending.state.started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages
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
  have messageEq := one_time_message pending request requested stage
  have role : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true := by
    rw [messageEq]
    exact tagged.2.1
  have actualFresh : TranscriptAuthParts.absSlice request.message ∉ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript) := messageEq.symm ▸ fresh
  let chosen := RegistrationNativeIdentityCensorFirstSource.chosenFull (PqxdhRefinement.absBytes pending.state.started.message.one_time_key) before
  have current := RegistrationNativeIdentityCensorFirstSource.current_equal setup checks representation created selected index owner placeholder false
    request before seed handle publicKey role armed held sourceTarget actualFresh found
  rw [messageEq] at current
  change (interpret setup.joint selected placeholder false (callback (.inr request))).run before =
    (interpret setup.joint selected placeholder false (callback (.inr request))).run chosen at current
  calc
    _ = Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (RegistrationNativePlatformBeaconPublication.fromEd
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending).run chosen := by
      conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
      conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
      simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, map_bind]
      rw [current]
    _ = _ := one_time setup checks representation created index owner writer selected placeholder pending request requested stage tagged chosen seed handle publicKey rfl rfl found

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealEdSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealEdSource.pq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealEdSource.pq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealEdSource.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealEdSource.one_time

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealEdSource.first_one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealEdSource.first_one_time
