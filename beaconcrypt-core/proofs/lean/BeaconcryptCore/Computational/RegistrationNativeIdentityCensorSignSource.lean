-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource

/-! A selected executable signing macro closes against either the real or private-censored source interpreter at the same literal call. Both interpreters retain the same canonical source receipt and generated-key table. The source seed and canonical reply occur only in this private realization; the executable marker uses a public handle/message and its zero-challenger-call interpretation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSignSource
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorSource (State)

private theorem prepared (selected : Nat) (message : Pqxdh.Bytes) (before : Mode)
    (target : before.target = some message) (role : RegistrationNativeIdentitySigningRole.oneTime message = true) :
    (RegistrationNativeIdentityCensorOperational.promote
      (RegistrationNativeIdentityCensorCompiler.prepare selected selected message)).run before =
      pure ((), {before with active := true}) := by
  have original := RegistrationNativeIdentityCensorCompiler.prepare_selected selected selected message message before target
  have projected := congrArg (simulateQ RegistrationNativeIdentityCensorOperational.embed) original
  change simulateQ RegistrationNativeIdentityCensorOperational.embed
    ((RegistrationNativeIdentityCensorCompiler.prepare selected selected message).run before) = _
  simpa only [role, and_self, ite_true, target, beq_self_eq_true, simulateQ_pure] using projected

private theorem marker (selected : Nat) (message : Pqxdh.Bytes) (before : Mode)
    (target : before.target = some message) (role : RegistrationNativeIdentitySigningRole.oneTime message = true) :
    (RegistrationNativeIdentityCensorOperational.signing selected selected message).run before = (do
      let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query (.inr (.omitted selected message)) :
        OracleComp RegistrationNativeIdentityCensorOperational.Spec (Option Ed25519Signature))
      pure (reply, {before with active := true})) := by
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, prepared selected message before target role, pure_bind]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, target, and_self, ite_true, StateT.run_lift]
  rfl

/-- The actual real source realization returns its canonical signature and records that exact request before the frontend continuation. -/
theorem real (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (message : Pqxdh.Bytes)
    (mode : Mode) (before : State) (seed : PqxdhJointIdentity.IdentitySeed)
    (modeTarget : mode.target = some message) (sourceTarget : before.target = some message)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true) (found : before.pool.seeds[selected]? = some seed) :
    (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected selected message).run mode)).run before =
      pure ((some (joint.sign seed message), {mode with active := true}), {before with
        pool := PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message))) (some (joint.sign seed message)) before.pool
        canonical := some (joint.sign seed message)}) := by
  rw [marker selected message mode modeTarget role]
  simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorSource.implementation,
    StateT.run_bind, RegistrationNativeIdentityCensorSource.omitted_source joint selected message before seed found sourceTarget,
    pure_bind, simulateQ_pure, StateT.run_pure]

/-- The private-censored realization delivers only the known placeholder while retaining the identical canonical receipt and private source poststate. -/
theorem censored (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (message : Pqxdh.Bytes) (placeholder : Ed25519Signature)
    (mode : Mode) (before : State) (seed : PqxdhJointIdentity.IdentitySeed)
    (modeTarget : mode.target = some message) (sourceTarget : before.target = some message)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true) (found : before.pool.seeds[selected]? = some seed) :
    (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      ((RegistrationNativeIdentityCensorOperational.signing selected selected message).run mode)).run before =
      pure ((some placeholder, {mode with active := true}), {before with
        pool := PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message))) (some (joint.sign seed message)) before.pool
        canonical := some (joint.sign seed message)}) := by
  rw [marker selected message mode modeTarget role]
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    RegistrationNativeIdentityCensorSource.censored_omitted joint selected placeholder message before seed found sourceTarget,
    pure_bind, simulateQ_pure, StateT.run_pure]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSignSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSignSource.real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSignSource.real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSignSource.censored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSignSource.censored
