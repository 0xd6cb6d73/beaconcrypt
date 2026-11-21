-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTail
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleFailureSource

/-! A selected successful source publication carries the actual public active flag to the bundle return. Public stopping is derived from the reached source controller and terminal state rather than from private publication membership. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "callback(" censored ")" => (fun query => source(censored, Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))))
local notation "encoder(" censored ")" => (fun fields => source(censored, Main (RegistrationNativePlatformIdentityProgram.external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields))))

/-- A successful literal source continuation from the first Ed stage must traverse its selected one-time call, whose public active flag is then retained. -/
theorem pre_key (censored : Bool) (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .PreKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (lineage : pending.state.beacon_identity = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes pending.state.started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed)
    (published : registration.PublishedBeaconInit (alloc.vec.Vec U8)) (after : FullState)
    (possible : (.ok (.Ok published), after) ∈ support ((RegistrationNativePlatformBeaconPublication.fromEd (callback(censored)) (encoder(censored)) pending).run before)) :
    after.1.2.active = true := by
  obtain ⟨actual, run, _key, _role, message⟩ := RegistrationSigning.ed_request_exact pending
  cases RustM.ok.inj (run.symm.trans requested)
  have messageEq : TranscriptAuthParts.absSlice request.message = absBytes pending.state.started.message.prekey :=
    congrArg (List.map absByte) (by simpa only [RegistrationSigning.signingMessageValues, stage] using message)
  have currentRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = false := by
    rw [messageEq]
    exact tagged.1
  rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def] at possible
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨⟨reply, middle⟩, called, later⟩ := possible
  have frame := RegistrationNativeIdentityCensorEdUnselectedSource.frame setup checks representation created selected index owner request placeholder censored before held currentRole (reply, middle) called
  obtain ⟨effect, resumed, facts⟩ := RegistrationSigning.ed_resume_refines pending reply
  rw [resumed] at later
  cases effect <;> simp only [RegistrationSigning.EdReplyTransition, stage] at facts
  case Rejected previous =>
    change _ ∈ support (pure ((RustM.ok (.Err previous) : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))), middle) : ProbComp _) at later
    rw [support_pure, Set.mem_singleton_iff] at later
    cases congrArg Prod.fst later
  case HashRequested next => cases facts.2.1
  case Ed25519SigningRequested next =>
    have nextStarted : next.state.started = pending.state.started := by
      simpa only using congrArg (fun state : registration.BeaconInitState => state.started) facts.2.2.2
    have nextTagged : RegistrationNativeIdentitySigningRole.Tagged next.state.started := nextStarted ▸ tagged
    obtain ⟨nextRequest, nextRequested, nextKey, _nextRole, _nextMessage⟩ := RegistrationSigning.ed_request_exact next
    have publicKey : nextRequest.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519 :=
      nextKey.trans ((RegistrationNativePlatformEdOperandLineage.resume_identity pending next reply resumed).trans lineage)
    have nextFresh := RegistrationNativeIdentityCensorEdUnselectedSource.fresh setup checks representation created selected index owner request placeholder censored before held currentRole
      (absBytes pending.state.started.message.one_time_key) tagged.2.1 fresh (reply, middle) called
    rw [← nextStarted] at nextFresh
    exact RegistrationNativeIdentityCensorActiveTail.one_time setup checks representation created selected index owner placeholder reserve censored
      next nextRequest nextRequested facts.2.1 nextTagged middle seed handle publicKey
      ((congrArg (fun state => state.1.armed) frame).trans armed)
      ((congrArg (fun state => state.1.target) frame).trans held)
      ((congrArg (fun state => state.2.target) frame).trans sourceTarget)
      nextFresh ((congrArg (fun state => state.2.pool.seeds[selected]?) frame).trans found)
      (.ok (.Ok published), after) later

attribute [local irreducible] registration.begin_beacon_init

private def BeginProgress (inputs : pqxdh.BeaconStartInputs) (started : pqxdh.BeaconStart) : registration.BeaconInitEffect → Prop
  | .Rejected _ => True
  | .Ed25519SigningRequested pending => pending.stage = .PreKey ∧ pending.state.started = started ∧
      pending.state.beacon_identity = inputs.identity_public_key
  | _ => False

private theorem begin_progress (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started) :
    ∃ effect, registration.begin_beacon_init control inputs coins pin = .ok effect ∧ BeginProgress inputs started effect := by
  obtain ⟨actual, actualRun, begun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin
  have same : actual = started := RustM.ok.inj (actualRun.symm.trans built)
  subst actual
  rw [begun]
  split_ifs
  · exact ⟨_, rfl, trivial⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩

private def fromEffect {S Encoded : Type}
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S ProbComp))
    (encode : registration.InitView → StateT S ProbComp (RustM (core.option.Option Encoded))) :
    registration.BeaconInitEffect → StateT S ProbComp (RustM (RegistrationBeaconInitExecutor.Result Encoded))
  | .Rejected previous => pure (.ok (.Err previous))
  | .Ed25519SigningRequested pending => RegistrationNativePlatformBeaconPublication.fromEd impl encode pending
  | _ => pure .div

private theorem begin_eq {S Encoded : Type}
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S ProbComp))
    (encode : registration.InitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (effect : registration.BeaconInitEffect)
    (begun : registration.begin_beacon_init control inputs coins pin = .ok effect) :
    RegistrationNativePlatformBeaconPublication.begin impl encode control inputs coins pin = fromEffect impl encode effect := by
  unfold RegistrationNativePlatformBeaconPublication.begin
  rw [begun]
  cases effect <;> rfl

/-- A successful actual original begin must enter the selected one-time stage; rejected pins return normally and cannot satisfy this successful-publication cut. -/
theorem begin (censored : Bool) (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started)
    (lineage : inputs.identity_public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed)
    (published : registration.PublishedBeaconInit (alloc.vec.Vec U8)) (after : FullState)
    (possible : (.ok (.Ok published), after) ∈ support ((RegistrationNativePlatformBeaconPublication.begin (callback(censored)) (encoder(censored)) control inputs coins pin).run before)) :
    after.1.2.active = true := by
  obtain ⟨effect, begun, progress⟩ := begin_progress control inputs coins pin started built
  obtain ⟨taggedStart, tagRun, tagged⟩ := RegistrationNativeIdentitySigningRole.initial control inputs coins
  have taggedSame : taggedStart = started := RustM.ok.inj (tagRun.symm.trans built)
  subst taggedStart
  rw [begin_eq _ _ control inputs coins pin effect begun] at possible
  cases effect <;> simp only [BeginProgress] at progress
  case Rejected previous =>
    change _ ∈ support (pure ((RustM.ok (.Err previous) : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))), before) : ProbComp _) at possible
    rw [support_pure, Set.mem_singleton_iff] at possible
    cases congrArg Prod.fst possible
  case Ed25519SigningRequested pending =>
    change _ ∈ support ((RegistrationNativePlatformBeaconPublication.fromEd (callback(censored)) (encoder(censored)) pending).run before) at possible
    obtain ⟨request, requested, _key, _role, _message⟩ := RegistrationSigning.ed_request_exact pending
    have nextTagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started := progress.2.1 ▸ tagged
    have nextFresh : absBytes pending.state.started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages
        (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript) := progress.2.1 ▸ fresh
    exact pre_key setup checks representation created selected index owner placeholder reserve censored pending request requested progress.1 nextTagged (progress.2.2.trans lineage)
      before seed handle armed held sourceTarget nextFresh found published after possible

/-- The literal Main dictionary has the same reached active flag as its original source controller; no whole publication/flag law is an assumption. -/
theorem source (censored : Bool) (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started)
    (lineage : inputs.identity_public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed)
    (published : registration.PublishedBeaconInit (alloc.vec.Vec U8)) (after : FullState)
    (possible : (.ok (.Ok published), after) ∈ support ((source(censored, Main (simulateQ
      (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
      (RegistrationNativePlatformWriter.begin E control inputs coins pin)))).run before)) :
    after.1.2.active = true := by
  rw [RegistrationNativeIdentityCensorPublicationSource.source] at possible
  exact begin setup checks representation created selected index owner placeholder reserve censored control inputs coins pin
    started built lineage before seed handle armed held sourceTarget fresh found published after possible

/-- Every actual successful selected bundle return carries active=true after its charged terminal phase/World action. It is therefore recognized by the public bundle-return test, without inspecting a private origin event. -/
theorem bundled (censored : Bool) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) = .ok started)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) (encoded : alloc.vec.Vec U8) (after : FullState)
    (possible : (RustM.ok (some encoded), after) ∈ support ((source(censored, Main
      (RegistrationNativePlatformIdentityBundle.bundled setup index owner oneTime (RegistrationNativePlatformConcreteSource.writer reserve)))).run before)) :
    after.1.2.active = true := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold,
    RegistrationNativeIdentityCensorSourceFold.bind_source, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨⟨reply, middle⟩, published, continued⟩ := possible
  have terminal := RegistrationNativeIdentityCensorBundleTerminal.frame setup checks representation created index owner oneTime reply selected placeholder censored middle (RustM.ok (some encoded), after) continued
  have value := terminal.1
  have active : after.1.2.active = middle.1.2.active := congrArg (fun mode => mode.active) terminal.2.1
  cases reply with
  | fail error | div => cases value
  | ok reply => cases reply with
    | Err previous => cases value
    | Ok publication =>
      exact active.trans (source setup checks representation created selected index owner placeholder reserve censored
        (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
        (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) owner.pin
        started built rfl before seed handle armed held sourceTarget fresh found publication middle published)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive.pre_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive.pre_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive.begin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive.bundled
