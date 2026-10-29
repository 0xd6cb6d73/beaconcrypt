-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceStartup

/-! Actual generated public startup derives the initial internal live-session and memo-correctness invariants. Neither is added to public eligibility or supplied as a startup security premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupFresh
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

/-- Every actual startup outcome keeps its separate private root memo unchanged. -/
theorem roots_frame (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (before : RegistrationNativePublicInterpreter.State n KemSK)
    (result : Option (RegistrationNativePublicStartup.Started source) × RegistrationNativePublicInterpreter.State n KemSK)
    (supported : result ∈ support ((RegistrationNativePublicSourceEffects.close setup seed scalar
      (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run before)) :
    result.2.roots = before.roots := by
  rw [RegistrationNativePublicStartupFrame.start_world, RegistrationNativePublicSourceEffects.close_world, support_map] at supported
  obtain ⟨inner, _possible, equal⟩ := supported
  cases equal
  rfl

private theorem sessions_empty (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (before after : PqxdhRecordLiftWorld.State n)
    (started : RegistrationNativePublicStartup.Started source)
    (supported : (some started, after) ∈ support
      ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run before)) :
    started.frontend.server.sessions = [] := by
  simp only [RegistrationNativePublicStartupFrame.startup, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨constructed, _built, continued⟩ := supported
  cases built : constructed.1.1 with
  | none => simp only [built, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at continued; cases continued.1
  | some created =>
      simp only [built, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨generated, _sampled, continued⟩ := continued
      cases sampled : generated.1 with
      | none => simp only [sampled, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at continued; cases continued.1
      | some credential =>
          simp only [sampled, StateT.run_bind, mem_support_bind_iff, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at continued
          obtain ⟨installed, _installed, hashed, _hashed, equal, _world⟩ := continued
          subst started
          rfl

/-- Every actual successful generated source startup establishes empty live sessions and a correct None root memo for the entire subsequent adaptive execution. -/
theorem start_invariants (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (started : RegistrationNativePublicStartup.Started source) (after : RegistrationNativePublicInterpreter.State n KemSK)
    (supported : (some started, after) ∈ support ((RegistrationNativePublicSourceEffects.close setup seed scalar
      (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run
        (RegistrationNativePublicInterpreter.initial : RegistrationNativePublicInterpreter.State n KemSK))) :
    RegistrationNativePublicSourceState.Live started.frontend after ∧
      RegistrationNativePublicSourceState.MemoCorrect setup seed scalar after.roots := by
  have roots := roots_frame setup source seed scalar ensureInit identityIndex serverKeyId _ _ supported
  rw [RegistrationNativePublicStartupFrame.start_world, RegistrationNativePublicSourceEffects.close_world, support_map] at supported
  obtain ⟨⟨reply, world⟩, reached, equal⟩ := supported
  simp only [Prod.mk.injEq] at equal
  obtain ⟨replyEq, afterEq⟩ := equal
  subst reply
  have empty := sessions_empty setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) _ world started reached
  constructor
  · intro ready member
    simp only [empty, List.not_mem_nil] at member
  · intro message root stored
    rw [roots] at stored
    change (none : Option PqxdhSecretInputKdf.RootOutput) = some root at stored
    cases stored

end BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupFresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupFresh.roots_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupFresh.roots_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupFresh.start_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupFresh.start_invariants
