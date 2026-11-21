-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicInvariantFinish
import BeaconcryptCore.Computational.RegistrationNativePublicStartup

/-! Successful public-reference startup constructs an empty owner roster and empty local record-request ledger literally. The receipt follows the actual constructor and mandatory Server ML continuations followed by pure full-pin construction and does not assume startup success or an initialized metadata invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicInvariantStartup
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicStartup (Started start)
open RegistrationNativePublicInterpreter (State)
open RegistrationNativePublicInvariantOwners (Coherent)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every actually successful public startup has its literal empty owner/record metadata and zero parsed-accept counter. -/
theorem start_fields (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (before after : State n KemSK) (started : Started source)
    (supported : (some started, after) ∈ support
      ((start setup source ensureInit identityIndex serverKeyId identity).run before)) :
    started.frontend.beacons = [] ∧ started.frontend.environment.recordRequests = [] ∧
      started.frontend.parsedAccepts = 0 := by
  simp only [start, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨constructed, _created, continued⟩ := supported
  cases created : constructed.1.1 with
  | none =>
      simp only [created, StateT.run_pure, mem_support_pure_iff] at continued
      cases continued
  | some created =>
      simp only [created, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨generated, _sampled, continued⟩ := continued
      cases credential : generated.1 with
      | none =>
          simp only [credential, StateT.run_pure, mem_support_pure_iff] at continued
          cases continued
      | some credential =>
          simp only [credential, StateT.run_bind, mem_support_bind_iff] at continued
          obtain ⟨initialized, _installed, returned⟩ := continued
          simp only [StateT.run_pure, mem_support_pure_iff] at returned
          cases returned
          exact ⟨rfl, rfl, rfl⟩

/-- Coherence and record-request emptiness are derived from successful startup, ready for the complete adaptive client induction. -/
theorem start_good (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (before after : State n KemSK) (started : Started source)
    (supported : (some started, after) ∈ support
      ((start setup source ensureInit identityIndex serverKeyId identity).run before)) :
    Coherent started.frontend.beacons ∧ started.frontend.environment.recordRequests = [] := by
  obtain ⟨empty, records, _counter⟩ := start_fields setup ensureInit identityIndex serverKeyId identity before after started supported
  refine ⟨?_, records⟩
  rw [empty]
  intro index owner found
  simp only [List.getElem?_nil] at found
  cases found

end BeaconcryptCore.Computational.RegistrationNativePublicInvariantStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantStartup.start_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantStartup.start_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantStartup.start_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantStartup.start_good
