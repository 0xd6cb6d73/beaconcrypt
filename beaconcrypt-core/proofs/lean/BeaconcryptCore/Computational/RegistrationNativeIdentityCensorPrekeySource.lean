-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal

/-! The literal prekey signing prefix forwards its genuine source reply before the public one-time selection. Its actual transcript append preserves the fresh one-time message, and the reached original continuation supplies the already checked selected suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrekeySource
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

/-- A genuinely fresh selected one-time tuple can be coupled from the actual first Ed stage, including every prekey rejection and actual current source-history update. -/
theorem pre_key (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .PreKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (lineage : pending.state.beacon_identity = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes pending.state.started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
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
  have current := RegistrationNativeIdentityCensorEdUnselectedSource.outgoing setup checks representation created selected index owner request placeholder before held currentRole
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, map_bind]
  rw [current]
  apply bind_congr_of_forall_mem_support
  rintro ⟨reply, middle⟩ called
  have frame := RegistrationNativeIdentityCensorEdUnselectedSource.frame setup checks representation created selected index owner request placeholder true before held currentRole (reply, middle) called
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
    have nextFresh := RegistrationNativeIdentityCensorEdUnselectedSource.fresh setup checks representation created selected index owner request placeholder true before held currentRole
      (absBytes pending.state.started.message.one_time_key) tagged.2.1 fresh (reply, middle) called
    rw [← nextStarted] at nextFresh
    exact RegistrationNativeIdentityCensorFirstSource.one_time setup checks representation created selected index owner placeholder reserve
      next nextRequest nextRequested nextStage nextTagged middle seed handle publicKey
      ((congrArg (fun state => state.1.armed) frame).trans armed)
      ((congrArg (fun state => state.1.target) frame).trans held)
      ((congrArg (fun state => state.2.target) frame).trans sourceTarget)
      nextFresh ((congrArg (fun state => state.2.pool.seeds[selected]?) frame).trans found)

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

/-- The actual original begin gate and source tag construction supply the prekey entry. A fresh first one-time message is the only chronological selection condition; no source signing/writer success is assumed. -/
theorem begin (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Array U8 1952#usize)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started)
    (lineage : inputs.identity_public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
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
    have pendingFresh : absBytes pending.state.started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages
        (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript) := progress.2.1 ▸ fresh
    exact pre_key setup checks representation created selected index owner placeholder reserve pending request requested progress.1 nextTagged (progress.2.2.trans lineage)
      before seed handle armed held sourceTarget pendingFresh found

/-- The actual complete begin returns normally for every crypto reply and failed or successful source reservation, without a freshness or key-row premise. -/
theorem normal (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Array U8 1952#usize) (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (result : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.begin
      (callback(censored)) (encoder(censored)) control inputs coins pin mldsa).run before)) :
    RegistrationNativeIdentityCensorPublicationNormal.Normal result.1 := by
  obtain ⟨started, built, _tagged⟩ := RegistrationNativeIdentitySigningRole.initial control inputs coins
  obtain ⟨effect, begun, progress⟩ := begin_progress control inputs coins pin mldsa started built
  rw [begin_eq _ _ control inputs coins pin mldsa effect begun] at possible
  cases effect <;> simp only [BeginProgress] at progress
  case Rejected previous =>
    change result ∈ support (pure (.ok (.Err previous), before) : ProbComp _) at possible
    rw [support_pure, Set.mem_singleton_iff] at possible
    subst result
    trivial
  case Ed25519SigningRequested pending =>
    change result ∈ support ((RegistrationNativePlatformBeaconPublication.fromEd (callback(censored)) (encoder(censored)) pending).run before) at possible
    exact RegistrationNativeIdentityCensorPublicationNormal.source_ed setup checks representation created selected index owner placeholder reserve censored pending before result possible

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrekeySource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrekeySource.pre_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrekeySource.pre_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrekeySource.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrekeySource.begin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrekeySource.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrekeySource.normal
