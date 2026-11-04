-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedCoverage

/-! Actual startup and every complete original typed callback derive the combined live-key, cached-history and successful-generation provenance needed by adaptive protected-origin coverage. These source invariants do not assume an origin or forgery conclusion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaBirthProvenance (Provenance)
open RegistrationNativeMldsaTableStop (Safe State callback)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : Source)

structure Holds (credential : Credential (handleSource source)) (fallback : Credential source)
    (before : State (n := n) (KemSK := KemSK) source) : Prop where
  safe : Safe source credential fallback before
  provenance : Provenance source before.2

private theorem evaluated {Answer : Type}
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Answer)
    (before : Pool source) (good : Provenance source before) (result : Answer × Pool source)
    (supported : result ∈ support (RegistrationNativeMldsaTableProgram.evaluate source work before)) :
    Provenance source result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (RegistrationNativeMldsaTableProgram.handler source) (Provenance source)
    (fun query current previous output reached => (RegistrationNativeMldsaBirthProvenance.step source query current previous output reached).1)
    work before good result supported

/-- Every reached complete callback preserves live private credentials, exact cached native receipts and actual successful-birth provenance together. -/
theorem step (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source)) (fallback : Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State (n := n) (KemSK := KemSK) source)
    (good : Holds source credential fallback before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) source)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before)) :
    Holds source credential fallback result.2 := by
  refine ⟨RegistrationNativeMldsaTableStop.step_safe source setup checks wire route representation created credential fallback query before result good.safe supported, ?_⟩
  change result ∈ support ((fun inner => (inner.1.1, (inner.1.2, inner.2))) <$>
    RegistrationNativeMldsaTableProgram.runState source
      (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query) before.1 before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact evaluated source _ before.2 good.provenance inner reached

/-- Actual successful startup derives every protected-cut source invariant from the empty private table. -/
theorem initialized (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : Aeneas.Std.U64)
    (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (startup : started ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKid) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ started.1) :
    ∃ fallback, Holds source initial.credential fallback (initial.state, started.2) := by
  obtain ⟨fallback, safe⟩ := RegistrationNativeMldsaTableStop.initialized source setup ensureInit identityIndex serverKid started startup initial member
  exact ⟨fallback, safe, RegistrationNativeMldsaBirthProvenance.program source _ started startup⟩

/-- Arbitrary adaptive original typed continuations retain the actual initialized protected-cut invariant. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source)) (fallback : Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State (n := n) (KemSK := KemSK) source)
    (good : Holds source credential fallback before) (result : Value × State (n := n) (KemSK := KemSK) source)
    (supported : result ∈ support ((simulateQ (callback source setup checks wire route representation created credential) work).run before)) :
    Holds source credential fallback result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (callback source setup checks wire route representation created credential)
    (Holds source credential fallback)
    (fun query current previous => step source setup checks wire route representation created credential fallback query current previous)
    work before good result supported

end BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant.program
