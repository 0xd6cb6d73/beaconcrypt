-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource
/-! Requests under another opaque identity handle never select or suppress a signature, even before any target exists. Their literal optional source reply preserves the complete public Mode and all private state except the attempted signing transcript. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdNonselectedSource
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
    (other : handle ≠ selected) :
    (RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode =
      (StateT.lift (RegistrationNativeIdentityCensorOperational.embed
        (.inl (.inl (.inl (.inl (.inr (.service handle (.sign message)))))))) :
        StateT Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec) (Option Ed25519Signature)).run mode := by
  have prepared : (RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run mode = pure ((), mode) := by
    simp [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, other]
  simp only [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind,
    promote_run, prepared, simulateQ_pure,
    pure_bind, StateT.run_get, other, false_and, ite_false]

private def answer (joint : PqxdhJointIdentity.Primitives) (handle : Nat) (message : Pqxdh.Bytes) (before : Private) :
    Option Ed25519Signature := (before.pool.seeds[handle]?).map fun seed => joint.sign seed message

private def after (joint : PqxdhJointIdentity.Primitives) (handle : Nat) (message : Pqxdh.Bytes) (before : Private) : Private :=
  {before with pool := PqxdhDynamicIdentityPool.record (.inr (.service handle (.sign message))) (answer joint handle message before) before.pool}

private theorem source_forward (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (message : Pqxdh.Bytes) (mode : Mode) (before : Private)
    (other : handle ≠ selected) :
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)).run before =
      pure ((answer joint handle message before, mode), after joint handle message before) := by
  rw [signing_forward selected handle message mode other]
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
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
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
    (other : owner.identity.handle ≠ selected) :
    (interpret setup.joint selected placeholder censored action).run before = pure (expected setup index owner request before) := by
  rw [interpret_run, RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
  by_cases publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519
  · simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_true,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    rw [operational_sign, source_forward setup.joint selected owner.identity.handle placeholder censored message before.1.2 before.2 other]
    simp only [pure_bind, expected, publicKey, ite_true]
    cases answer setup.joint owner.identity.handle message before.2 <;> rfl
  · simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_false,
      simulateQ_pure, StateT.run_pure, pure_bind, expected]

/-- A different opaque handle forwards its genuine optional source reply in both interpretations before or after selection. -/
theorem outgoing
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (other : owner.identity.handle ≠ selected) :
    (interpret setup.joint selected placeholder false action).run before =
      (interpret setup.joint selected placeholder true action).run before := by
  rw [normalized setup checks representation created selected index owner request placeholder false before other,
    normalized setup checks representation created selected index owner request placeholder true before other]

/-- A genuine forwarded signature can append its literal service receipt, while Mode, hash, target, canonical signature, framing and generated seeds stay exact. -/
theorem frame (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (other : owner.identity.handle ≠ selected)
    (result : RegistrationSigningShared.SignReply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored action).run before)) :
    stable result.2.1.2 result.2.2 = stable before.1.2 before.2 := by
  rw [normalized setup checks representation created selected index owner request placeholder censored before other,
    support_pure, Set.mem_singleton_iff] at supported
  subst result
  unfold expected
  split <;> rfl

end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdNonselectedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdNonselectedSource.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdNonselectedSource.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdNonselectedSource.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdNonselectedSource.frame
