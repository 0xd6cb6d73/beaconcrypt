-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupWorld

/-! Closing the actual public generated startup with literal private roots and reconstructing its successful frontend yields the concrete seeded native startup. Every constructor, ML-generation and pin-initialization branch retains its source probability and actual counted World work. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceStartup
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicSourceStartupWorld (observe privateAt initialized)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

/-- The actual private closure of public challenge-identity startup restores exactly the original seeded native initial state, including all source refusals and counted dummy draws. -/
theorem start_source (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    observe setup source seed scalar identityIndex serverKeyId <$>
      (RegistrationNativePublicSourceEffects.close setup seed scalar
        (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run
          (RegistrationNativePublicInterpreter.initial : RegistrationNativePublicInterpreter.State n KemSK) =
      RegistrationNativeSeedStart.start setup source ensureInit identityIndex serverKeyId seed := by
  rw [RegistrationNativePublicStartupFrame.start_world, RegistrationNativePublicSourceEffects.close_world]
  simp only [Functor.map_map, RegistrationNativePublicStartupFrame.startup, StateT.run_bind,
    map_bind, RegistrationNativeSeedStart.start, RegistrationNativePublicInterpreter.initial]
  apply bind_congr
  intro constructed
  cases built : constructed.1.1 with
  | none =>
      simp only [built, RegistrationNativeSeedConstruct.replace, Option.map_none,
        RegistrationNativeSeedStart.finish, StateT.run_pure, map_pure, observe, Option.map_none]
  | some dummy =>
      simp only [built, RegistrationNativeSeedConstruct.replace, Option.map_some,
        RegistrationNativeSeedStart.finish, StateT.run_bind, map_bind]
      apply bind_congr
      intro generated
      cases sampled : generated.1 with
      | none => simp only [StateT.run_pure, map_pure, observe, Option.map_none]
      | some credential =>
          have nativeEq := RegistrationNativePublicSourceStartupWorld.initialize_source setup source seed scalar identityIndex serverKeyId credential generated.2
          simp only [initialized, StateT.run_bind, StateT.run_pure, map_bind, map_pure, privateAt,
            RegistrationNativePublicInterpreter.initial] at nativeEq ⊢
          exact nativeEq

end BeaconcryptCore.Computational.RegistrationNativePublicSourceStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceStartup.start_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceStartup.start_source
