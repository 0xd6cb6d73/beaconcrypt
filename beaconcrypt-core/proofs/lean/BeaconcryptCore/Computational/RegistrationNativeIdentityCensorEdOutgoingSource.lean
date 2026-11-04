-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSignSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdOutgoing

/-! The actual full native outgoing Ed callback closes against the real and private-censored marker interpreters. The current reply is packed by the original frontend, its actual owner-history append is retained, and every other Main/P/private-source field has an exact operational receipt. Canonical source data occurs only in this private realization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
variable {n : Nat} {I KemSK Platform Value : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

abbrev Main := RegistrationNativeIdentityMain.State n KemSK mlSource × Platform
abbrev Full := (Main (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource) × Mode) × RegistrationNativeIdentityCensorSource.State

noncomputable def interpret (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource Value) :
    StateT (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) ProbComp Value := fun before => do
  let result ← (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
    ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2
  pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))

private theorem interpret_run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource Value)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret joint selected placeholder censored work).run before = (do
      let result ← (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
          else RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2
      pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) := rfl

def after (selected : Nat) (index : Nat) (message : Pqxdh.Bytes)
    (canonical delivered : Ed25519Signature) (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :=
  ((RegistrationNativePlatformIdentityCtxEdOutgoing.updated index message (some delivered) before.1.1,
    {before.1.2 with active := true}), {before.2 with
      pool := PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message))) (some canonical) before.2.pool
      canonical := some canonical})

private theorem signing_run (selected : Nat) (placeholder : Ed25519Signature) (handle : Nat) (message : Pqxdh.Bytes) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder
      (.inl (.inl (.inr (.service handle (.sign message)))))).run before =
      (RegistrationNativeIdentityCensorOperational.signing selected handle message).run before := rfl

def view (placeholder : Ed25519Signature)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :=
  ((RegistrationNativePlatformIdentityCtxHistoryView.view placeholder before.1.1, before.1.2), before.2)

private theorem after_view (selected index : Nat) (message : Pqxdh.Bytes) (canonical placeholder : Ed25519Signature)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    view placeholder (after selected index message canonical canonical before) =
      view placeholder (after selected index message canonical placeholder before) := by
  unfold view after
  rw [RegistrationNativePlatformIdentityCtxEdOutgoing.projected_append placeholder canonical placeholder index message before.1.1]

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

/-- The canonical actual source call is followed by the literal actual frontend openedBytes and owner-history write. -/
theorem real (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (modeTarget : before.1.2.target = some message) (sourceTarget : before.2.target = some message)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (found : before.2.pool.seeds[selected]? = some seed) :
    (interpret setup.joint selected placeholder false action).run before =
      pure (RegistrationAuthenticationShared.openedBytes (some ((setup.joint.sign seed message).toList ++ message)),
        after selected index message (setup.joint.sign seed message) (setup.joint.sign seed message) before) := by
  rw [interpret_run, RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
  simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_true, Bool.false_eq_true, ite_false,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [signing_run, handle]
  rw [RegistrationNativeIdentityCensorSignSource.real setup.joint selected message before.1.2 before.2 seed modeTarget sourceTarget role found]
  simp only [pure_bind, after]

/-- The private-censored actual frontend receives only its placeholder but keeps the same source receipt and actual non-history Main/P state. -/
theorem censored (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (modeTarget : before.1.2.target = some message) (sourceTarget : before.2.target = some message)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (found : before.2.pool.seeds[selected]? = some seed) :
    (interpret setup.joint selected placeholder true action).run before =
      pure (RegistrationAuthenticationShared.openedBytes (some (placeholder.toList ++ message)),
        after selected index message (setup.joint.sign seed message) placeholder before) := by
  rw [interpret_run, RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
  simp only [RegistrationNativePlatformIdentityCtxEdOutgoing.expected, publicKey, ite_true,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [signing_run, handle]
  rw [RegistrationNativeIdentityCensorSignSource.censored setup.joint selected message placeholder before.1.2 before.2 seed modeTarget sourceTarget role found]
  simp only [pure_bind, after]
/-- Erasing only the appended native signature slot couples the exact real/private-censored poststates. The distinct current replies remain available to their actual Core continuations. -/
theorem state_coupling (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (modeTarget : before.1.2.target = some message) (sourceTarget : before.2.target = some message)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (found : before.2.pool.seeds[selected]? = some seed) :
    (fun result => view placeholder result.2) <$> (interpret setup.joint selected placeholder false action).run before =
      (fun result => view placeholder result.2) <$> (interpret setup.joint selected placeholder true action).run before := by
  rw [real setup checks representation created selected index owner request placeholder before seed handle publicKey modeTarget sourceTarget role found,
    censored setup checks representation created selected index owner request placeholder before seed handle publicKey modeTarget sourceTarget role found]
  simp only [map_pure, after_view]
end Actual

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource.real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource.real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource.censored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource.censored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource.state_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource.state_coupling
