-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdForwardSource

/-! After a one-time target is fixed, every different-handle or different-message signing call forwards the actual genuine optional service. A different selected-handle one-time message deactivates the internal token. Current source replies and full Main/private/P states agree; only the literal genuine source receipt may append. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOtherSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
abbrev Private := RegistrationNativeIdentityCensorSource.State

noncomputable def modeAfter (selected handle : Nat) (message : Pqxdh.Bytes) (before : Mode) : Mode := by
  classical
  exact if handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message then
    {before with active := false} else before

private theorem modeAfter_target (selected handle : Nat) (message : Pqxdh.Bytes) (before : Mode) :
    (modeAfter selected handle message before).target = before.target := by
  unfold modeAfter
  split <;> rfl

def stable (mode : Mode) (before : Private) : Mode × Private :=
  ({mode with active := false}, {before with pool := {before.pool with transcript := []}})

private theorem prepare (selected handle : Nat) (message target : Pqxdh.Bytes) (before : Mode)
    (held : before.target = some target) (other : handle ≠ selected ∨ target ≠ message) :
    (RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run before =
      pure ((), modeAfter selected handle message before) := by
  rw [RegistrationNativeIdentityCensorCompiler.prepare_selected selected handle message target before held]
  by_cases eligible : handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message
  · have different : target ≠ message := other.resolve_left (fun denied => denied eligible.1)
    simp only [eligible, modeAfter, held]
    simp [different]
  · simp only [eligible, ite_false, modeAfter]

private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run before) := rfl

private theorem signing_forward (selected handle : Nat) (message target : Pqxdh.Bytes) (mode : Mode)
    (held : mode.target = some target) (other : handle ≠ selected ∨ target ≠ message) :
    (RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode =
      (StateT.lift (RegistrationNativeIdentityCensorOperational.embed
        (.inl (.inl (.inl (.inl (.inr (.service handle (.sign message)))))))) :
        StateT Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec) (Option Ed25519Signature)).run
          (modeAfter selected handle message mode) := by
  have notSuppressed : ¬ (handle = selected ∧ (modeAfter selected handle message mode).target = some message) := by
    intro same
    have equal : target = message := Option.some.inj (held.symm.trans ((modeAfter_target selected handle message mode).symm.trans same.2))
    exact other.elim (fun denied => denied same.1) (fun denied => denied equal)
  simp only [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, promote_run,
    prepare selected handle message target mode held other, simulateQ_pure, pure_bind, StateT.run_get,
    notSuppressed, ite_false]

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let reply ← work; pure (reply, before)) := rfl
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private def answer (joint : PqxdhJointIdentity.Primitives) (handle : Nat) (message : Pqxdh.Bytes) (before : Private) :
    Option Ed25519Signature := (before.pool.seeds[handle]?).map fun seed => joint.sign seed message
private def after (joint : PqxdhJointIdentity.Primitives) (handle : Nat) (message : Pqxdh.Bytes) (before : Private) : Private :=
  {before with pool := PqxdhDynamicIdentityPool.record (.inr (.service handle (.sign message))) (answer joint handle message before) before.pool}

private theorem source_forward (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (message target : Pqxdh.Bytes) (mode : Mode) (before : Private)
    (held : mode.target = some target) (other : handle ≠ selected ∨ target ≠ message) :
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)).run before =
      pure ((answer joint handle message before, modeAfter selected handle message mode), after joint handle message before) := by
  rw [signing_forward selected handle message target mode held other]
  cases censored <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, lift_apply, bind_pure_comp,
      simulateQ_map, RegistrationNativeIdentityCensorOperational.embed, simulateQ_spec_query,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol, RegistrationNativeIdentityMainSource.implementation,
      PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
      PqxdhJointIdentity.primitiveReply, map_apply, StateT.run, map_pure, answer, after] <;> rfl

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
      ((RegistrationNativePlatformIdentityCtxEdOutgoing.updated index message (answer setup.joint owner.identity.handle message before.2) before.1.1,
        modeAfter selected owner.identity.handle message before.1.2), after setup.joint owner.identity.handle message before.2))
  else (.None, before)

private theorem normalized (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (target : Pqxdh.Bytes)
    (held : before.1.2.target = some target) (other : owner.identity.handle ≠ selected ∨ target ≠ message) :
    (interpret setup.joint selected placeholder censored action).run before = pure (expected setup selected index owner request before) := by
  rw [interpret_run, RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
  by_cases publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519
  · simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_true,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    rw [operational_sign, source_forward setup.joint selected owner.identity.handle placeholder censored message target before.1.2 before.2 held other]
    simp only [pure_bind, expected, publicKey, ite_true]
    cases answer setup.joint owner.identity.handle message before.2 <;> rfl
  · simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_false,
      simulateQ_pure, StateT.run_pure, pure_bind, expected]

/-- Different handles and different messages forward the literal source service in both interpreters, including every missing-row and public-key rejection path. -/
theorem outgoing
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (target : Pqxdh.Bytes)
    (held : before.1.2.target = some target) (other : owner.identity.handle ≠ selected ∨ target ≠ message) :
    (interpret setup.joint selected placeholder false action).run before =
      (interpret setup.joint selected placeholder true action).run before := by
  rw [normalized setup checks representation created selected index owner request placeholder false before target held other,
    normalized setup checks representation created selected index owner request placeholder true before target held other]

/-- Only the current active flag and the literal appended source transcript may change; target, physical hash state, canonical memo, framing and generated seeds remain exact. -/
theorem frame (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (target : Pqxdh.Bytes)
    (held : before.1.2.target = some target) (other : owner.identity.handle ≠ selected ∨ target ≠ message)
    (result : RegistrationSigningShared.SignReply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored action).run before)) :
    stable result.2.1.2 result.2.2 = stable before.1.2 before.2 := by
  rw [normalized setup checks representation created selected index owner request placeholder censored before target held other,
    support_pure, Set.mem_singleton_iff] at supported
  subst result
  unfold expected
  split
  · unfold stable modeAfter
    split <;> rfl
  · rfl

/-- Another key or message cannot activate the selected callback's public publication stop. -/
theorem inactive (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (target : Pqxdh.Bytes)
    (held : before.1.2.target = some target) (other : owner.identity.handle ≠ selected ∨ target ≠ message)
    (wasInactive : before.1.2.active = false)
    (result : RegistrationSigningShared.SignReply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored action).run before)) :
    result.2.1.2.active = false := by
  rw [normalized setup checks representation created selected index owner request placeholder censored before target held other,
    support_pure, Set.mem_singleton_iff] at supported
  subst result
  unfold expected
  split
  · unfold modeAfter
    split
    · rfl
    · exact wasInactive
  · exact wasInactive
end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOtherSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOtherSource.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOtherSource.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOtherSource.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOtherSource.frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOtherSource.inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOtherSource.inactive
