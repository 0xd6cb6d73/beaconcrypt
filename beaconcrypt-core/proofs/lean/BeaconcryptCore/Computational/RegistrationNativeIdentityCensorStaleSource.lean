-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnselectedTail

/-! A guessed bundle whose one-time message was already signed makes no new target selection. Its literal source call is forwarded, and its original PQ/fingerprint suffix remains an ordinary source continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorSource (State)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}

private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run before) := rfl

/-- Public selection declines a previously forwarded one-time message and disarms its internal token; the actual source key/hash history is unchanged by that selection. -/
theorem prepare (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (message : Pqxdh.Bytes) (mode : Mode) (before : State)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (modeTarget : mode.target = none) (sourceTarget : before.target = none)
    (stale : message ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.pool.transcript)) :
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.promote
        (RegistrationNativeIdentityCensorCompiler.prepare selected selected message)).run mode)).run before =
      pure (((), {mode with active := false}), before) := by
  have declined : (RegistrationNativeIdentityCensorSource.select selected message).run before = pure (false, before) := by
    simp [RegistrationNativeIdentityCensorSource.select, StateT.run, sourceTarget, stale]
  have beqNone : ((none : Option Pqxdh.Bytes) == some message) = false := rfl
  by_cases armed : mode.armed = true
  · have tree : (RegistrationNativeIdentityCensorCompiler.prepare selected selected message).run mode = (do
        let chosen ← RegistrationNativeIdentityCensorCompiler.select message
        if chosen then RegistrationNativeIdentityCensorCompiler.inspect message mode.knownInputs else pure ()
        pure ((), {mode with
          target := (if chosen then some message else none)
          active := (if chosen then some message else none) == some message})) := by
      simp [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, role, armed, modeTarget]
    rw [promote_run, tree]
    cases censored <;>
      simp only [Bool.false_eq_true, ite_false, ite_true,
        RegistrationNativeIdentityCensorCompiler.select, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityCensorSource.censored,
        RegistrationNativeIdentityCensorSource.implementation, StateT.run_bind, declined, pure_bind,
        simulateQ_pure, StateT.run_pure, beqNone, modeTarget]
  · have tree : (RegistrationNativeIdentityCensorCompiler.prepare selected selected message).run mode =
        pure ((), {mode with active := false}) := by
      simp [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, role, armed, modeTarget]
    rw [promote_run, tree]
    simp only [simulateQ_pure, StateT.run_pure]

private def answer (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (message : Pqxdh.Bytes) (before : State) :
    Option Ed25519Signature := (before.pool.seeds[selected]?).map (fun seed => joint.sign seed message)
private def after (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (message : Pqxdh.Bytes) (before : State) : State :=
  {before with pool := PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message))) (answer joint selected message before) before.pool}

/-- Declined selection forwards the genuine optional source signing request exactly once and retains its literal successful or failed transcript record. -/
theorem signing (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (message : Pqxdh.Bytes) (mode : Mode) (before : State)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (modeTarget : mode.target = none) (sourceTarget : before.target = none)
    (stale : message ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.pool.transcript)) :
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected selected message).run mode)).run before =
      pure ((answer joint selected message before, {mode with active := false}), after joint selected message before) := by
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [prepare joint selected placeholder censored message mode before role modeTarget sourceTarget stale]
  simp only [pure_bind, StateT.run_get, simulateQ_pure, StateT.run_pure, modeTarget]
  cases censored <;> rfl

/-- A known source row makes the declined-selection reply and its precise transcript append explicit. -/
theorem signing_found (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (message : Pqxdh.Bytes) (mode : Mode) (before : State)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (modeTarget : mode.target = none) (sourceTarget : before.target = none)
    (stale : message ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.pool.transcript))
    (seed : PqxdhJointIdentity.IdentitySeed) (found : before.pool.seeds[selected]? = some seed) :
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected selected message).run mode)).run before =
      pure ((some (joint.sign seed message), {mode with active := false}),
        {before with pool := (PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message)))
          (some (joint.sign seed message)) before.pool)}) := by
  rw [signing joint selected placeholder censored message mode before role modeTarget sourceTarget stale]
  simp only [answer, after, found, Option.map_some]

section Actual
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

private theorem interpret_run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret joint selected placeholder censored work).run before = (do
      let result ← (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
        else RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2
      pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) := rfl

private theorem operational_sign (selected : Nat) (placeholder : Ed25519Signature) (handle : Nat) (message : Pqxdh.Bytes) (mode : Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder
      (.inl (.inl (.inr (.service handle (.sign message)))))).run mode =
      (RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode := rfl

def stable (mode : Mode) (before : State) : Mode × State :=
  ({mode with active := false}, {before with pool := {before.pool with transcript := []}})

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (request : registration.Ed25519SigningRequest)
variable (placeholder : Ed25519Signature)
local notation "message" => TranscriptAuthParts.absSlice request.message
local notation "action" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
  (RegistrationNativePlatformIdentityProgram.native
    (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner (Sum.inr request)))

private noncomputable def expected
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    RegistrationSigningShared.SignReply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource) := by
  classical
  exact if request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519 then
    (RegistrationAuthenticationShared.openedBytes ((answer setup.joint selected message before.2).map fun signature => signature.toList ++ message),
      ((RegistrationNativePlatformIdentityCtxEdOutgoing.updated index message (answer setup.joint selected message before.2) before.1.1, {before.1.2 with active := false}),
        after setup.joint selected message before.2))
  else (.None, before)

private theorem normalized (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (handle : owner.identity.handle = selected)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (stale : message ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript)) :
    (interpret setup.joint selected placeholder censored action).run before = pure (expected setup selected index owner request before) := by
  rw [interpret_run, RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
  by_cases publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519
  · simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_true,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    rw [operational_sign, handle, signing setup.joint selected placeholder censored message before.1.2 before.2 role held sourceTarget stale]
    simp only [pure_bind, expected, publicKey, ite_true]
    cases answer setup.joint selected message before.2 <;> rfl
  · simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_false,
      simulateQ_pure, StateT.run_pure, pure_bind, expected]

/-- The actual stale one-time callback forwards its genuine source request in both private interpretations, including every key gate and optional reply. -/
theorem outgoing
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (handle : owner.identity.handle = selected)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (stale : message ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript)) :
    (interpret setup.joint selected placeholder false action).run before =
      (interpret setup.joint selected placeholder true action).run before := by
  rw [normalized setup checks representation created selected index owner request placeholder false before handle role held sourceTarget stale,
    normalized setup checks representation created selected index owner request placeholder true before handle role held sourceTarget stale]

/-- Declined selection preserves the actual target and key/hash state, allowing only its genuine current source transcript append and deactivation. -/
theorem frame (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (handle : owner.identity.handle = selected)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (stale : message ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (result : RegistrationSigningShared.SignReply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored action).run before)) :
    stable result.2.1.2 result.2.2 = stable before.1.2 before.2 := by
  rw [normalized setup checks representation created selected index owner request placeholder censored before handle role held sourceTarget stale,
    support_pure, Set.mem_singleton_iff] at supported
  subst result
  unfold expected
  split <;> rfl

local notation "crypto(" censored ")" => (fun query => interpret setup.joint selected placeholder censored
  (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
    (RegistrationNativePlatformIdentityProgram.native
      (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))))
local notation "encoder(" reserve "," censored ")" => (fun fields => interpret setup.joint selected placeholder censored
  (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
    (RegistrationNativePlatformIdentityProgram.external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields))))

/-- A nonfresh one-time message forwards normally into the original PQ/fingerprint source tail. Every current reply and complete state remains literal, so unsuccessful guesses require no suppressed-signature coupling. -/
theorem one_time (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (pending : registration.BeaconEd25519Signing) (requested : pending.request = .ok request) (stage : pending.stage = .OneTimeKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (stale : PqxdhRefinement.absBytes pending.state.started.message.one_time_key ∈ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript)) :
    (RegistrationNativePlatformBeaconPublication.fromEd (crypto(false)) (encoder(reserve, false)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromEd (crypto(true)) (encoder(reserve, true)) pending).run before := by
  obtain ⟨actual, run, _key, _role, bytes⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_request_exact pending
  cases RustM.ok.inj (run.symm.trans requested)
  have messageEq : message = PqxdhRefinement.absBytes pending.state.started.message.one_time_key :=
    congrArg (List.map PqxdhRefinement.absByte) (by simpa only [BeaconcryptCore.Refinement.RegistrationSigning.signingMessageValues, stage] using bytes)
  have role : RegistrationNativeIdentitySigningRole.oneTime message = true := by
    rw [messageEq]
    exact tagged.2.1
  have issued : message ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript) := messageEq.symm ▸ stale
  have current := outgoing setup checks representation created selected index owner request placeholder before handle role held sourceTarget issued
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind]
  rw [current]
  apply bind_congr_of_forall_mem_support
  rintro ⟨reply, middle⟩ called
  have kept := frame setup checks representation created selected index owner request placeholder true before handle role held sourceTarget issued (reply, middle) called
  obtain ⟨effect, resumed, facts⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_resume_refines pending reply
  rw [resumed]
  cases effect <;> simp only [BeaconcryptCore.Refinement.RegistrationSigning.EdReplyTransition, stage] at facts
  case Rejected previous => rfl
  case FingerprintRequested next => cases facts.2.1
  case Ed25519SigningRequested next =>
    have nextTagged := RegistrationNativeIdentitySigningRole.preserved pending tagged reply _ resumed
    change RegistrationNativeIdentitySigningRole.Tagged next.state.started at nextTagged
    exact RegistrationNativeIdentityCensorUnselectedTail.pq setup checks representation created selected index owner placeholder reserve
      next facts.2.1 nextTagged middle ((congrArg (fun state => state.1.target) kept).trans held)

end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.prepare
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.signing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.one_time

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.signing_found' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource.signing_found
