-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource
/-! Actual non-one-time Ed outgoing calls forward the genuine optional source service in both private interpreters, including rejected public keys and missing rows. Before target selection the source mode has no omitted message. The exact source update appends the current genuine service receipt; Mode and the remaining private state stay unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
abbrev Private := RegistrationNativeIdentityCensorSource.State

def stable (mode : Mode) (before : Private) : Mode × Private :=
  (mode, {before with pool := {before.pool with transcript := []}})

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let reply ← work; pure (reply, before)) := rfl
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (mode : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run mode =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run mode) := rfl

private theorem signing_forward (selected handle : Nat) (message : Pqxdh.Bytes) (mode : Mode)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = false)
    (notTarget : mode.target ≠ some message) :
    (RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode =
      (StateT.lift (RegistrationNativeIdentityCensorOperational.embed
        (.inl (.inl (.inl (.inl (.inr (.service handle (.sign message)))))))) :
        StateT Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec) (Option Ed25519Signature)).run mode := by
  have prepared : (RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run mode = pure ((), mode) := by
    simp only [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, role, Bool.false_eq_true, and_false, ite_false]
  simp only [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind,
    promote_run, prepared, simulateQ_pure,
    pure_bind, StateT.run_get, notTarget, and_false, ite_false]

private def answer (joint : PqxdhJointIdentity.Primitives) (handle : Nat) (message : Pqxdh.Bytes) (before : Private) :
    Option Ed25519Signature := (before.pool.seeds[handle]?).map fun seed => joint.sign seed message

private def after (joint : PqxdhJointIdentity.Primitives) (handle : Nat) (message : Pqxdh.Bytes) (before : Private) : Private :=
  {before with pool := PqxdhDynamicIdentityPool.record (.inr (.service handle (.sign message))) (answer joint handle message before) before.pool}

private theorem source_forward (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (message : Pqxdh.Bytes) (mode : Mode) (before : Private)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = false) (notTarget : mode.target ≠ some message) :
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)).run before =
      pure ((answer joint handle message before, mode), after joint handle message before) := by
  rw [signing_forward selected handle message mode role notTarget]
  cases censored <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, lift_apply, bind_pure_comp,
      simulateQ_map, RegistrationNativeIdentityCensorOperational.embed,
      simulateQ_spec_query, RegistrationNativeIdentityCensorSource.censored,
      RegistrationNativeIdentityCensorSource.implementation, RegistrationNativeIdentityCensorSource.protocol,
      RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
      PqxdhDynamicIdentityPool.poolImpl, PqxdhJointIdentity.primitiveReply, map_apply,
      StateT.run, map_pure, answer, after] <;> rfl

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

section Actual
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (request : registration.Ed25519SigningRequest)
variable (placeholder : Ed25519Signature)
local notation "message" => TranscriptAuthParts.absSlice request.message
local notation "action" => RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
  (RegistrationNativePlatformIdentityProgram.native
    (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      setup mlSource index owner (Sum.inr request)))

private noncomputable def expected
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    RegistrationSigningShared.SignReply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource) := by
  classical
  exact if request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519 then
    (RegistrationAuthenticationShared.openedBytes ((answer setup.joint owner.identity.handle message before.2).map fun signature => signature.toList ++ message),
      ((RegistrationNativePlatformIdentityCtxEdOutgoing.updated index message (answer setup.joint owner.identity.handle message before.2) before.1.1, before.1.2),
        after setup.joint owner.identity.handle message before.2))
  else (.None, before)

private theorem normalized (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (held : before.1.2.target = none)
    (currentRole : RegistrationNativeIdentitySigningRole.oneTime message = false) :
    (interpret setup.joint selected placeholder censored action).run before = pure (expected setup index owner request before) := by
  rw [interpret_run, RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
  by_cases publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519
  · simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_true,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    rw [operational_sign, source_forward setup.joint selected owner.identity.handle placeholder censored message before.1.2 before.2 currentRole
      (by simp only [held, ne_eq, reduceCtorEq, not_false_eq_true])]
    simp only [pure_bind, expected, publicKey, ite_true]
    cases answer setup.joint owner.identity.handle message before.2 <;> rfl
  · simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_false,
      simulateQ_pure, StateT.run_pure, pure_bind, expected]

/-- Non-one-time outgoing signing forwards the genuine source request identically in real and private-censored executions, even with a missing row or rejected public key. -/
theorem outgoing
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (held : before.1.2.target = none)
    (currentRole : RegistrationNativeIdentitySigningRole.oneTime message = false) :
    (interpret setup.joint selected placeholder false action).run before =
      (interpret setup.joint selected placeholder true action).run before := by
  rw [normalized setup checks representation created selected index owner request placeholder false before held currentRole,
    normalized setup checks representation created selected index owner request placeholder true before held currentRole]

/-- A genuine forwarded signature can append its literal service receipt, while Mode, hash, target, canonical signature, framing and generated seeds stay exact. -/
theorem frame (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (held : before.1.2.target = none)
    (currentRole : RegistrationNativeIdentitySigningRole.oneTime message = false)
    (result : RegistrationSigningShared.SignReply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored action).run before)) :
    stable result.2.1.2 result.2.2 = stable before.1.2 before.2 := by
  rw [normalized setup checks representation created selected index owner request placeholder censored before held currentRole,
    support_pure, Set.mem_singleton_iff] at supported
  subst result
  unfold expected
  split <;> rfl
/-- A forwarded non-one-time service cannot make a fresh one-time target message enter the actual successful signing history. This uses the literal current request/reply record, including missing rows and failed packing. -/
theorem fresh (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (held : before.1.2.target = none)
    (currentRole : RegistrationNativeIdentitySigningRole.oneTime message = false)
    (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (prior : target ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (result : RegistrationSigningShared.SignReply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored action).run before)) :
    target ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected result.2.2.pool.transcript) := by
  have different : target ≠ message := by
    intro equal
    rw [equal, currentRole] at targetRole
    cases targetRole
  rw [normalized setup checks representation created selected index owner request placeholder censored before held currentRole,
    support_pure, Set.mem_singleton_iff] at supported
  subst result
  unfold expected
  split
  · change target ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected (after setup.joint owner.identity.handle message before.2).pool.transcript)
    change target ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected
      (before.2.pool.transcript ++ [⟨.inr (.service owner.identity.handle (.sign message)), answer setup.joint owner.identity.handle message before.2⟩]))
    rw [RegistrationNativeIdentityHistory.append_history]
    cases signature : answer setup.joint owner.identity.handle message before.2 <;>
      by_cases same : owner.identity.handle = selected <;>
      simpa [RegistrationNativeIdentityHistory.history, RegistrationNativeIdentityHistory.entry,
        same, PqxdhJointIdentity.signedMessages, PqxdhJointIdentity.requestEvent,
        different, Ne.symm different] using prior
  · exact prior

/-- A previously signed one-time message remains in the actual successful history through every forwarded role-separated prekey or PQ callback. -/
theorem stale (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (held : before.1.2.target = none)
    (currentRole : RegistrationNativeIdentitySigningRole.oneTime message = false)
    (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (prior : target ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (result : RegistrationSigningShared.SignReply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored action).run before)) :
    target ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected result.2.2.pool.transcript) := by
  have different : target ≠ message := by
    intro equal
    rw [equal, currentRole] at targetRole
    cases targetRole
  rw [normalized setup checks representation created selected index owner request placeholder censored before held currentRole,
    support_pure, Set.mem_singleton_iff] at supported
  subst result
  unfold expected
  split
  · change target ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected (after setup.joint owner.identity.handle message before.2).pool.transcript)
    change target ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected
      (before.2.pool.transcript ++ [⟨.inr (.service owner.identity.handle (.sign message)), answer setup.joint owner.identity.handle message before.2⟩]))
    rw [RegistrationNativeIdentityHistory.append_history]
    cases signature : answer setup.joint owner.identity.handle message before.2 <;>
      by_cases same : owner.identity.handle = selected <;>
      simpa [RegistrationNativeIdentityHistory.history, RegistrationNativeIdentityHistory.entry,
        same, PqxdhJointIdentity.signedMessages, PqxdhJointIdentity.requestEvent,
        different, Ne.symm different] using prior
  · exact prior

end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource.frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource.fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource.stale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource.stale
