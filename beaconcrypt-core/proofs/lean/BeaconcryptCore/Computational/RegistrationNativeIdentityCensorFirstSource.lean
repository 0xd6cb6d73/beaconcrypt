-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedSource

/-! At the guessed public bundle position, the first fresh one-time message is selected from the actual earlier source history. Selection/recognition markers change only private analysis metadata; the current source call then uses the same generated row. The executable selection policy uses its ordinary query history, and receives neither a private seed nor a canonical signature. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorSource (State)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}

def chosenMode (message : Pqxdh.Bytes) (before : Mode) : Mode :=
  {before with target := some message, active := true}
def chosenPrivate (message : Pqxdh.Bytes) (before : State) : State :=
  {before with target := some message, canonical := none, framing := none}

private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run before) := rfl

/-- The literal source selection and prior-input scan have their actual chronological prefix and preserve the complete original key pool/hash state. -/
theorem prepare (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (message : Pqxdh.Bytes) (mode : Mode) (before : State)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true) (armed : mode.armed = true)
    (modeTarget : mode.target = none) (sourceTarget : before.target = none)
    (fresh : message ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.pool.transcript)) :
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.promote
        (RegistrationNativeIdentityCensorCompiler.prepare selected selected message)).run mode)).run before =
      pure (((), chosenMode message mode), chosenPrivate message before) := by
  have tree : (RegistrationNativeIdentityCensorCompiler.prepare selected selected message).run mode = (do
      let chosen ← RegistrationNativeIdentityCensorCompiler.select message
      if chosen then RegistrationNativeIdentityCensorCompiler.inspect message mode.knownInputs else pure ()
      pure ((), {mode with
        target := (if chosen then some message else none)
        active := (if chosen then some message else none) == some message})) := by
    simp [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, role, armed, modeTarget]
  have selectSource : (RegistrationNativeIdentityCensorSource.select selected message).run before =
      pure (true, chosenPrivate message before) := by
    simp [RegistrationNativeIdentityCensorSource.select, StateT.run, sourceTarget, fresh, chosenPrivate]
  rw [promote_run, tree]
  cases censored <;>
    simp only [Bool.false_eq_true, ite_false, ite_true,
      RegistrationNativeIdentityCensorCompiler.select, RegistrationNativeIdentityCensorCompiler.inspect,
      simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      StateT.run_bind, selectSource, pure_bind, simulateQ_pure, StateT.run_pure,
      beq_self_eq_true, chosenMode]


/-- The first selected actual signing call consumes its genuine source query exactly once after the public fresh-message selection. -/
theorem signing (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (message : Pqxdh.Bytes) (mode : Mode) (before : State) (seed : PqxdhJointIdentity.IdentitySeed)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true) (armed : mode.armed = true)
    (modeTarget : mode.target = none) (sourceTarget : before.target = none)
    (fresh : message ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.pool.transcript))
    (found : before.pool.seeds[selected]? = some seed) :
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected selected message).run mode)).run before =
      pure (((if censored then some placeholder else some (joint.sign seed message)), chosenMode message mode),
        {chosenPrivate message before with
          pool := PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message))) (some (joint.sign seed message)) before.pool
          canonical := some (joint.sign seed message)}) := by
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [prepare joint selected placeholder censored message mode before role armed modeTarget sourceTarget fresh]
  simp only [pure_bind, StateT.run_get, simulateQ_pure, StateT.run_pure,
    chosenMode, and_self, ite_true, StateT.run_lift, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind]
  cases censored with
  | false =>
    simp only [Bool.false_eq_true, ite_false, RegistrationNativeIdentityCensorSource.implementation]
    rw [RegistrationNativeIdentityCensorSource.omitted_source joint selected message (chosenPrivate message before) seed found rfl]
    simp only [pure_bind, chosenPrivate]
  | true =>
    simp only [ite_true]
    rw [RegistrationNativeIdentityCensorSource.censored_omitted joint selected placeholder message (chosenPrivate message before) seed found rfl]
    simp only [pure_bind, chosenPrivate]


private theorem same_macro (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (message : Pqxdh.Bytes) (mode : Mode) (before : State) (seed : PqxdhJointIdentity.IdentitySeed)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true) (armed : mode.armed = true)
    (modeTarget : mode.target = none) (sourceTarget : before.target = none)
    (fresh : message ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.pool.transcript))
    (found : before.pool.seeds[selected]? = some seed) :
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected selected message).run mode)).run before =
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected selected message).run (chosenMode message mode))).run
      (chosenPrivate message before) := by
  rw [signing joint selected placeholder censored message mode before seed role armed modeTarget sourceTarget fresh found]
  cases censored with
  | false =>
    have again := RegistrationNativeIdentityCensorSignSource.real joint selected message (chosenMode message mode)
      (chosenPrivate message before) seed rfl rfl role found
    simpa only [Bool.false_eq_true, ite_false, chosenMode, chosenPrivate] using again.symm
  | true =>
    have again := RegistrationNativeIdentityCensorSignSource.censored joint selected message placeholder (chosenMode message mode)
      (chosenPrivate message before) seed rfl rfl role found
    simpa only [ite_true, chosenMode, chosenPrivate] using again.symm

section Actual
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

/-- The chosen public message and current metadata are analysis fields; Main and P are untouched. -/
def chosenFull (message : Pqxdh.Bytes)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :=
  ((before.1.1, chosenMode message before.1.2), chosenPrivate message before.2)

private theorem interpret_run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret joint selected placeholder censored work).run before = (do
      let result ← (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
          else RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2
      pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) := rfl

private theorem signing_run (selected : Nat) (placeholder : Ed25519Signature) (handle : Nat) (message : Pqxdh.Bytes) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder
      (.inl (.inl (.inr (.service handle (.sign message)))))).run before =
      (RegistrationNativeIdentityCensorOperational.signing selected handle message).run before := rfl

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
local notation "action(" request ")" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
  (RegistrationNativePlatformIdentityProgram.native
    (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner (Sum.inr request)))

/-- The first actual outgoing callback performs the source selection itself, then has the same complete current reply/native/private/P result as the already-selected entry. -/
theorem current_equal (censored : Bool) (request : registration.Ed25519SigningRequest)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (role : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true)
    (armed : before.1.2.armed = true) (modeTarget : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : TranscriptAuthParts.absSlice request.message ∉ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    (interpret setup.joint selected placeholder censored (action(request))).run before =
      (interpret setup.joint selected placeholder censored (action(request))).run
        (chosenFull (TranscriptAuthParts.absSlice request.message) before) := by
  simp only [interpret_run, chosenFull, RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
  simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_true,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    signing_run, handle]
  rw [same_macro setup.joint selected placeholder censored (TranscriptAuthParts.absSlice request.message)
    before.1.2 before.2 seed role armed modeTarget sourceTarget fresh found]

/-- The complete actual source controller selects its first fresh one-time message at the public guessed bundle, then couples its canonical/placeholder failed-publication suffix. No preselected target is assumed. -/
theorem one_time (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .OneTimeKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (armed : before.1.2.armed = true) (modeTarget : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : PqxdhRefinement.absBytes pending.state.started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    let callback := fun censored query => interpret setup.joint selected placeholder censored
      (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
        (RegistrationNativePlatformIdentityProgram.native
          (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query)))
    let encode := fun censored fields => interpret setup.joint selected placeholder censored
      (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
        (RegistrationNativePlatformIdentityProgram.external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields)))
    Prod.map RegistrationNativeIdentityReadyFailure.observe (RegistrationNativeIdentityCensorOutgoingView.view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (m := StateT (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) ProbComp) (callback false) (encode false) pending).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe (RegistrationNativeIdentityCensorOutgoingView.view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (m := StateT (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) ProbComp) (callback true) (encode true) pending).run before := by
  dsimp only
  obtain ⟨actual, run, _key, _slot, message⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_request_exact pending
  cases RustM.ok.inj (run.symm.trans requested)
  have messageEq : TranscriptAuthParts.absSlice request.message = PqxdhRefinement.absBytes pending.state.started.message.one_time_key :=
    congrArg (List.map PqxdhRefinement.absByte) (by simpa only [BeaconcryptCore.Refinement.RegistrationSigning.signingMessageValues, stage] using message)
  have role : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true := by
    rw [messageEq]
    exact tagged.2.1
  let selectedBefore := chosenFull (PqxdhRefinement.absBytes pending.state.started.message.one_time_key) before
  let callback := fun censored query => interpret setup.joint selected placeholder censored
    (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
      (RegistrationNativePlatformIdentityProgram.native
        (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query)))
  let encode := fun censored fields => interpret setup.joint selected placeholder censored
    (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
      (RegistrationNativePlatformIdentityProgram.external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields)))
  have entry (censored : Bool) :
      (RegistrationNativePlatformBeaconPublication.fromEd (m := StateT (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) ProbComp) (callback censored) (encode censored) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromEd (m := StateT (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) ProbComp) (callback censored) (encode censored) pending).run selectedBefore := by
    have equal := current_equal setup checks representation created selected index owner placeholder censored request before seed
      handle publicKey role armed modeTarget sourceTarget (messageEq.symm ▸ fresh) found
    rw [messageEq] at equal
    conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
    conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
    simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind]
    rw [equal]
  change Prod.map RegistrationNativeIdentityReadyFailure.observe (RegistrationNativeIdentityCensorOutgoingView.view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (m := StateT (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) ProbComp) (callback false) (encode false) pending).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe (RegistrationNativeIdentityCensorOutgoingView.view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (m := StateT (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) ProbComp) (callback true) (encode true) pending).run before
  rw [entry false, entry true]
  exact RegistrationNativeIdentityCensorSelectedSource.one_time setup checks representation created selected index owner placeholder reserve
    pending request requested stage tagged selectedBefore seed handle publicKey rfl rfl found

end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource.prepare

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource.current_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource.current_equal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSource.one_time
