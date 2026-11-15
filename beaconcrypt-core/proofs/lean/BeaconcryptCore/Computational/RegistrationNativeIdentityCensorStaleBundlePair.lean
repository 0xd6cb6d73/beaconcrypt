-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal

/-! A previously signed one-time operand remains stale through the actual prekey prefix. Both private interpretations retain the same full result and state through the declined selection and mutable publication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleBundlePair
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] registration.BeaconEd25519Signing.resume
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativeIdentityCensorConcreteWriter.encode reserve
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "callback" => (fun query => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query)))
local notation "encoder" => (fun fields => Main (RegistrationNativePlatformIdentityProgram.external (writer fields)))

theorem pre_key (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .PreKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (stale : absBytes pending.state.started.message.one_time_key ∈ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript)) :
    (RegistrationNativePlatformBeaconPublication.fromEd
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromEd
        (fun query => interpret setup.joint selected placeholder true (callback query))
        (fun fields => interpret setup.joint selected placeholder true (encoder fields)) pending).run
          before := by
  obtain ⟨actual, run, _key, _role, message⟩ := RegistrationSigning.ed_request_exact pending
  cases RustM.ok.inj (run.symm.trans requested)
  have messageEq : TranscriptAuthParts.absSlice request.message = absBytes pending.state.started.message.prekey :=
    congrArg (List.map absByte) (by simpa only [RegistrationSigning.signingMessageValues, stage] using message)
  have currentRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = false := by
    rw [messageEq]
    exact tagged.1
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind]
  have current := RegistrationNativeIdentityCensorEdUnselectedSource.outgoing setup checks representation created selected index owner request placeholder before held currentRole
  rw [current]
  apply bind_congr_of_forall_mem_support
  rintro ⟨reply, after⟩ reached
  have frame := RegistrationNativeIdentityCensorEdUnselectedSource.frame setup checks representation created selected index owner request placeholder true before held currentRole (reply, after) reached
  obtain ⟨effect, resumed, facts⟩ := RegistrationSigning.ed_resume_refines pending reply
  rw [resumed]
  cases effect <;> simp only [RegistrationSigning.EdReplyTransition, stage] at facts
  case Rejected previous => rfl
  case HashRequested next => cases facts.2.1
  case Ed25519SigningRequested next =>
    have nextStage : next.stage = .OneTimeKey := facts.2.1
    have nextStarted := congrArg (fun state : registration.BeaconInitState => state.started) facts.2.2.2
    change next.state.started = pending.state.started at nextStarted
    have nextTagged : RegistrationNativeIdentitySigningRole.Tagged next.state.started := nextStarted ▸ tagged
    obtain ⟨nextRequest, nextRequested, _nextKey, _nextRole, _nextMessage⟩ := RegistrationSigning.ed_request_exact next
    have nextStale := RegistrationNativeIdentityCensorEdUnselectedSource.stale setup checks representation created selected index owner request placeholder true before held currentRole
      (absBytes pending.state.started.message.one_time_key) tagged.2.1 stale (reply, after) reached
    rw [← nextStarted] at nextStale
    exact RegistrationNativeIdentityCensorStaleSource.one_time setup checks representation created selected index owner nextRequest placeholder
      reserve next nextRequested nextStage nextTagged after handle
      ((congrArg (fun state => state.1.target) frame).trans held)
      ((congrArg (fun state => state.2.target) frame).trans sourceTarget) nextStale

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


/-- The literal begin gate and stale prekey prefix have identical real and censored source results, including all rejected and failed writes. -/
theorem begin (selected : Nat) (placeholder : Ed25519Signature)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (stale : absBytes started.message.one_time_key ∈ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript)) :
    (RegistrationNativePlatformBeaconPublication.begin
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) control inputs coins pin).run before =
      (RegistrationNativePlatformBeaconPublication.begin
        (fun query => interpret setup.joint selected placeholder true (callback query))
        (fun fields => interpret setup.joint selected placeholder true (encoder fields)) control inputs coins pin).run
          before := by
  obtain ⟨effect, begun, progress⟩ := begin_progress control inputs coins pin started built
  obtain ⟨taggedStart, tagRun, tagged⟩ := RegistrationNativeIdentitySigningRole.initial control inputs coins
  have taggedSame : taggedStart = started := RustM.ok.inj (tagRun.symm.trans built)
  subst taggedStart
  rw [begin_eq _ _ control inputs coins pin effect begun, begin_eq _ _ control inputs coins pin effect begun]
  cases effect <;> simp only [BeginProgress] at progress
  case Rejected previous => rfl
  case Ed25519SigningRequested pending =>
    obtain ⟨request, requested, _key, _role, _message⟩ := RegistrationSigning.ed_request_exact pending
    have nextTagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started := progress.2.1 ▸ tagged
    have pendingStale : absBytes pending.state.started.message.one_time_key ∈ PqxdhJointIdentity.signedMessages
        (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript) := progress.2.1 ▸ stale
    exact pre_key setup checks representation created index owner reserve selected placeholder pending request requested progress.1 nextTagged
      before handle held sourceTarget pendingStale



/-- A stale selected body keeps its entire real and censored result through publication and terminal owner updates. -/
theorem bundled (selected : Nat) (placeholder : Ed25519Signature) (scalar : PqxdhJointGapDh.ScalarBytes)
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (stale : absBytes started.message.one_time_key ∈ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript)) :
    (interpret setup.joint selected placeholder false (Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar
      (RegistrationNativePlatformConcreteSource.writer reserve)))).run before =
    (interpret setup.joint selected placeholder true (Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar
      (RegistrationNativePlatformConcreteSource.writer reserve)))).run before := by
  have initial : (interpret setup.joint selected placeholder false (Main (simulateQ
        (RegistrationNativePlatformIdentityPublication.callback setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
        (RegistrationNativePlatformWriter.begin E (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
          (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) owner.pin)))).run before =
      (interpret setup.joint selected placeholder true (Main (simulateQ
        (RegistrationNativePlatformIdentityPublication.callback setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
        (RegistrationNativePlatformWriter.begin E (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
          (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) owner.pin)))).run before := by
    rw [RegistrationNativeIdentityCensorPublicationSource.source setup checks representation created selected index owner placeholder reserve false,
      RegistrationNativeIdentityCensorPublicationSource.source setup checks representation created selected index owner placeholder reserve true]
    exact begin setup checks representation created index owner reserve selected placeholder _ _ _ _ started built before handle held sourceTarget stale
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold,
    RegistrationNativeIdentityCensorSourceFold.bind_source,RegistrationNativeIdentityCensorSourceFold.bind_source,
    StateT.run_bind,StateT.run_bind,initial]
  apply bind_congr
  intro result
  rw [RegistrationNativeIdentityCensorBundleTerminal.source,RegistrationNativeIdentityCensorBundleTerminal.source]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleBundlePair

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleBundlePair.pre_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleBundlePair.pre_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleBundlePair.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleBundlePair.begin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleBundlePair.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleBundlePair.bundled
