-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceProgram
import BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupFresh

/-! The complete source correspondence starts from the actual generated startup. Its live-root, scalar-mask and controller conditions are consequences of that startup, rather than additional public eligibility conditions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupGood
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

/-- Every successful actual closed startup establishes all internal conditions of the whole adaptive source theorem. -/
theorem start_good (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selected : Nat) (started : RegistrationNativePublicStartup.Started source)
    (after : RegistrationNativePublicInterpreter.State n KemSK)
    (supported : (some started, after) ∈ support ((RegistrationNativePublicSourceEffects.close setup seed scalar
      (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run
        RegistrationNativePublicInterpreter.initial)) :
    RegistrationNativePublicSourceProgram.Good setup seed scalar selected (started.frontend, after) := by
  have roots := RegistrationNativePublicSourceStartupFresh.start_invariants setup source seed scalar ensureInit
    identityIndex serverKeyId started after supported
  have raw := RegistrationNativePublicSourceSupport.simulate_support
    (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
    ((RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId
      (setup.joint.publicKeys seed)).run RegistrationNativePublicInterpreter.initial) (some started, after) supported
  obtain ⟨empty, records, _counter⟩ := RegistrationNativePublicInvariantStartup.start_fields setup
    ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) _ after started raw
  have metadata := RegistrationNativePublicInvariantStartup.start_good setup ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed) _ after started raw
  refine ⟨roots.1, roots.2, ?_, ?_, records⟩
  · rw [empty]
    intro index owner found
    simp only [List.getElem?_nil] at found
    cases found
  · exact (RegistrationNativePublicInvariantOwners.restored_holds scalar started.frontend.beacons).mp metadata.1

end BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupGood

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupGood.start_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupGood.start_good
