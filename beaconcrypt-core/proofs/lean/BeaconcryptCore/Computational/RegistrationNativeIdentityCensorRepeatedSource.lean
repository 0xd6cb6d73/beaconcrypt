-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTail
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal

/-! Repeated source bundles for the selected one-time message reuse the same canonical private signing realization and public placeholder. Genuine prekey calls preserve the fixed target and reach the original selected suffix without a fresh-message or rearming premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOutgoingView (view)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "action(" query ")" => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))
local notation "callback(" censored ")" => (fun query => source(censored, action(query)))
local notation "encoder(" censored ")" => (fun fields => source(censored, Main (RegistrationNativePlatformIdentityProgram.external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields))))

private theorem current (censored : Bool) (request : registration.Ed25519SigningRequest)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (role : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true)
    (held : before.1.2.target = some (TranscriptAuthParts.absSlice request.message))
    (sourceTarget : before.2.target = some (TranscriptAuthParts.absSlice request.message))
    (found : before.2.pool.seeds[selected]? = some seed) :
    (callback(censored) (.inr request)).run before =
      pure (RegistrationAuthenticationShared.openedBytes (some ((if censored then placeholder else setup.joint.sign seed (TranscriptAuthParts.absSlice request.message)).toList ++ TranscriptAuthParts.absSlice request.message)),
        RegistrationNativeIdentityCensorEdOutgoingSource.after selected index (TranscriptAuthParts.absSlice request.message)
          (setup.joint.sign seed (TranscriptAuthParts.absSlice request.message))
          (if censored then placeholder else setup.joint.sign seed (TranscriptAuthParts.absSlice request.message)) before) := by
  cases censored with
  | false =>
    exact RegistrationNativeIdentityCensorEdOutgoingSource.real setup checks representation created selected index owner request placeholder
      before seed handle publicKey held sourceTarget role found
  | true =>
    exact RegistrationNativeIdentityCensorEdOutgoingSource.censored setup checks representation created selected index owner request placeholder
      before seed handle publicKey held sourceTarget role found

/-- Every reached repeated selected one-time continuation retains the actual active flag, with the canonical source row and every later failure preserved. -/
theorem one_time_active (censored : Bool) (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .OneTimeKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (held : before.1.2.target = some (absBytes pending.state.started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes pending.state.started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed)
    (result : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.fromEd (callback(censored)) (encoder(censored)) pending).run before)) :
    result.2.1.2.active = true := by
  obtain ⟨actual, run, _key, _role, bytes⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_request_exact pending
  cases RustM.ok.inj (run.symm.trans requested)
  have messageEq : TranscriptAuthParts.absSlice request.message = PqxdhRefinement.absBytes pending.state.started.message.one_time_key :=
    congrArg (List.map PqxdhRefinement.absByte) (by simpa only [BeaconcryptCore.Refinement.RegistrationSigning.signingMessageValues, stage] using bytes)
  have role : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true := by
    rw [messageEq]
    exact tagged.2.1
  have current := current setup checks representation created selected index owner placeholder censored request before seed handle publicKey role (messageEq.symm ▸ held) (messageEq.symm ▸ sourceTarget) found
  rw [messageEq] at current
  let signature := if censored then placeholder else setup.joint.sign seed (PqxdhRefinement.absBytes pending.state.started.message.one_time_key)
  have admitted := RegistrationNativeIdentityCensorReply.admitted pending signature stage
  obtain ⟨next, resumed, nextStage, _copied, _restored⟩ := RegistrationNativeIdentityEdProgress.one_time pending
    (RegistrationNativeIdentityCensorReply.buffer signature pending.state.started.message.one_time_key).to_slice stage admitted.1 admitted.2
  have nextTagged := RegistrationNativeIdentitySigningRole.preserved pending tagged _ _ resumed
  change RegistrationNativeIdentitySigningRole.Tagged next.state.started at nextTagged
  rw [← RegistrationNativeIdentityCensorReply.packed signature _] at resumed
  rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def] at possible
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind] at possible
  rw [current] at possible
  simp only [pure_bind] at possible
  rw [resumed] at possible
  exact RegistrationNativeIdentityCensorActiveTail.pq setup checks representation created selected index owner placeholder reserve censored next nextStage nextTagged
    (RegistrationNativeIdentityCensorEdOutgoingSource.after selected index (PqxdhRefinement.absBytes pending.state.started.message.one_time_key)
      (setup.joint.sign seed (PqxdhRefinement.absBytes pending.state.started.message.one_time_key)) signature
      before)
    (PqxdhRefinement.absBytes pending.state.started.message.one_time_key) held tagged.2.1 result possible

/-- The actual prekey prefix forwards its genuine service and reaches the repeated selected one-time suffix without reselecting the message. -/
theorem pre_key (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .PreKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (lineage : pending.state.beacon_identity = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = some (absBytes pending.state.started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes pending.state.started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (callback(false)) (encoder(false)) pending).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (callback(true)) (encoder(true)) pending).run before := by
  obtain ⟨actual, run, _key, _role, message⟩ := RegistrationSigning.ed_request_exact pending
  cases RustM.ok.inj (run.symm.trans requested)
  have messageEq : TranscriptAuthParts.absSlice request.message = absBytes pending.state.started.message.prekey :=
    congrArg (List.map absByte) (by simpa only [RegistrationSigning.signingMessageValues, stage] using message)
  have currentRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = false := by
    rw [messageEq]
    exact tagged.1
  have current := RegistrationNativeIdentityCensorEdForwardSource.outgoing setup checks representation created selected index owner request placeholder before _ held tagged.2.1 currentRole
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, map_bind]
  rw [current]
  apply bind_congr_of_forall_mem_support
  rintro ⟨reply, middle⟩ called
  have frame := RegistrationNativeIdentityCensorEdForwardSource.frame setup checks representation created selected index owner request placeholder true before _ held tagged.2.1 currentRole (reply, middle) called
  obtain ⟨effect, resumed, facts⟩ := RegistrationSigning.ed_resume_refines pending reply
  rw [resumed]
  cases effect <;> simp only [RegistrationSigning.EdReplyTransition, stage] at facts
  case Rejected previous => rfl
  case FingerprintRequested next => cases facts.2.1
  case Ed25519SigningRequested next =>
    have nextStage : next.stage = .OneTimeKey := facts.2.1
    have nextStarted : next.state.started = pending.state.started := by
      simpa only using congrArg (fun state : registration.BeaconInitState => state.started) facts.2.2.2
    have nextTagged : RegistrationNativeIdentitySigningRole.Tagged next.state.started := nextStarted ▸ tagged
    obtain ⟨nextRequest, nextRequested, nextKey, _nextRole, _nextMessage⟩ := RegistrationSigning.ed_request_exact next
    have publicKey : nextRequest.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519 :=
      nextKey.trans ((RegistrationNativePlatformEdOperandLineage.resume_identity pending next reply resumed).trans lineage)
    have nextHeld : middle.1.2.target = some (absBytes next.state.started.message.one_time_key) := by
      rw [nextStarted]
      exact (congrArg (fun state => state.1.target) frame).trans held
    have nextSourceTarget : middle.2.target = some (absBytes next.state.started.message.one_time_key) := by
      rw [nextStarted]
      exact (congrArg (fun state => state.2.target) frame).trans sourceTarget
    exact RegistrationNativeIdentityCensorSelectedSource.one_time setup checks representation created selected index owner placeholder reserve
      next nextRequest nextRequested nextStage nextTagged middle seed handle publicKey nextHeld nextSourceTarget
      ((congrArg (fun state => state.2.pool.seeds[selected]?) frame).trans found)


attribute [local irreducible] registration.begin_beacon_init

private def BeginProgress (inputs : pqxdh.BeaconStartInputs) (started : pqxdh.BeaconStart) : registration.BeaconInitEffect → Prop
  | .Rejected _ => True
  | .Ed25519SigningRequested pending => pending.stage = .PreKey ∧ pending.state.started = started ∧
      pending.state.beacon_identity = inputs.identity_public_key
  | _ => False

private theorem begin_progress (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Array U8 1952#usize)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started) :
    ∃ effect, registration.begin_beacon_init control inputs coins pin mldsa = .ok effect ∧ BeginProgress inputs started effect := by
  obtain ⟨actual, actualRun, begun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin mldsa
  have same : actual = started := RustM.ok.inj (actualRun.symm.trans built)
  subst actual
  rw [begun]
  split_ifs
  · exact ⟨_, rfl, trivial⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩

private def fromEffect {S Encoded : Type}
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → StateT S ProbComp (RustM (core.option.Option Encoded))) :
    registration.BeaconInitEffect → StateT S ProbComp (RustM (RegistrationBeaconInitExecutor.Result Encoded))
  | .Rejected previous => pure (.ok (.Err previous))
  | .Ed25519SigningRequested pending => RegistrationNativePlatformBeaconPublication.fromEd impl encode pending
  | _ => pure .div

private theorem begin_eq {S Encoded : Type}
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Array U8 1952#usize)
    (effect : registration.BeaconInitEffect)
    (begun : registration.begin_beacon_init control inputs coins pin mldsa = .ok effect) :
    RegistrationNativePlatformBeaconPublication.begin impl encode control inputs coins pin mldsa = fromEffect impl encode effect := by
  unfold RegistrationNativePlatformBeaconPublication.begin
  rw [begun]
  cases effect <;> rfl

/-- The actual original begin gate supplies the repeated-target prekey entry and preserves every rejected pin/signature/writer branch. -/
theorem begin (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Array U8 1952#usize)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started)
    (lineage : inputs.identity_public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = some (absBytes started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.begin (callback(false)) (encoder(false)) control inputs coins pin mldsa).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.begin (callback(true)) (encoder(true)) control inputs coins pin mldsa).run before := by
  obtain ⟨effect, begun, progress⟩ := begin_progress control inputs coins pin mldsa started built
  obtain ⟨taggedStart, tagRun, tagged⟩ := RegistrationNativeIdentitySigningRole.initial control inputs coins
  have taggedSame : taggedStart = started := RustM.ok.inj (tagRun.symm.trans built)
  subst taggedStart
  rw [begin_eq _ _ control inputs coins pin mldsa effect begun, begin_eq _ _ control inputs coins pin mldsa effect begun]
  cases effect <;> simp only [BeginProgress] at progress
  case Rejected previous => rfl
  case Ed25519SigningRequested pending =>
    change Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
        (RegistrationNativePlatformBeaconPublication.fromEd (callback(false)) (encoder(false)) pending).run before =
      Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
        (RegistrationNativePlatformBeaconPublication.fromEd (callback(true)) (encoder(true)) pending).run before
    obtain ⟨request, requested, _key, _role, _message⟩ := RegistrationSigning.ed_request_exact pending
    have nextTagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started := progress.2.1 ▸ tagged
    have pendingHeld : before.1.2.target = some (absBytes pending.state.started.message.one_time_key) := progress.2.1 ▸ held
    have pendingSourceTarget : before.2.target = some (absBytes pending.state.started.message.one_time_key) := progress.2.1 ▸ sourceTarget
    exact pre_key setup checks representation created selected index owner placeholder reserve pending request requested progress.1 nextTagged (progress.2.2.trans lineage)
      before seed handle pendingHeld pendingSourceTarget found

/-- The actual Main publication retains the repeated-target failed-publication coupling, without a fresh-message or rearming condition. -/
theorem publication (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Array U8 1952#usize)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started)
    (lineage : inputs.identity_public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = some (absBytes started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed) :
    let publication := Main (simulateQ
      (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
      (RegistrationNativePlatformWriter.begin E control inputs coins pin mldsa))
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$> (source(false, publication)).run before =
      Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$> (source(true, publication)).run before := by
  dsimp only
  rw [RegistrationNativeIdentityCensorPublicationSource.source, RegistrationNativeIdentityCensorPublicationSource.source]
  exact begin setup checks representation created selected index owner placeholder reserve
    control inputs coins pin mldsa started built lineage before seed handle held sourceTarget found

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedSource.one_time_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedSource.one_time_active
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedSource.pre_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedSource.pre_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedSource.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedSource.begin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedSource.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedSource.publication
