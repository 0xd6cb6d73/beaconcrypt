-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame
/-! Actual generated startup never allocates a protected record seed or uses a protected record role. Constructor, ML generation, Server initialization and the real shared pin hash retain these fields on every outcome, without resetting the reached cache or counters. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupFields
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I}
private def fields (before : PqxdhRecordLiftWorld.State n) := (before.used, before.seeds)

private theorem sampled (work : ProbComp A) (before : PqxdhRecordLiftWorld.State n)
    (result : A × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.sampled work).run before)) : fields result.2 = fields before := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨actual, _possible, equal⟩ := supported
  cases equal
  rfl

private theorem install (created : PqxdhLiveServerConstruction.Created Unit) (before : PqxdhRecordLiftWorld.State n)
    (result : Unit × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.initializeServer created).run before)) : fields result.2 = fields before := by
  simp only [PqxdhRecordLiftWorld.initializeServer, StateT.run] at supported
  split at supported <;> rw [mem_support_pure_iff] at supported <;> cases supported <;> rfl

private theorem hash (bytes : Pqxdh.Bytes) (before : PqxdhRecordLiftWorld.State n)
    (result : (PqxdhRecordLiftInterface.EnvEffects n).Range (.inr (.hash bytes)) × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before)) : fields result.2 = fields before := by
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨actual, called, equal⟩ := supported
  cases equal
  exact sampled _ (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) before) actual called

/-- Every actual startup branch preserves the complete protected role-use and seed fields. -/
theorem startup_fields (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (before : PqxdhRecordLiftWorld.State n)
    (result : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run before)) :
    (result.2.used, result.2.seeds) = (before.used, before.seeds) := by
  simp only [RegistrationNativePublicStartupFrame.startup, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨constructed, built, supported⟩ := supported
  have constructedFields := sampled _ before constructed built
  cases made : constructed.1.1 with
  | none =>
    simp only [made, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact constructedFields
  | some created =>
    simp only [made, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨generated, called, supported⟩ := supported
    have generatedFields := sampled _ constructed.2 generated called
    cases born : generated.1 with
    | none =>
      simp only [born, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact generatedFields.trans constructedFields
    | some credential =>
      simp only [born, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨installed, initialized, digest, hashed, supported⟩ := supported
      have installedFields := install _ generated.2 installed initialized
      have hashedFields := hash (absBytes credential.publicKey) installed.2 digest hashed
      rw [StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact hashedFields.trans (installedFields.trans (generatedFields.trans constructedFields))

/-- Actual cold initialization leaves every protected role unused and its private seed table empty, at the real warmed hash cache. -/
theorem initialized (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (result : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run
      PqxdhRecordLiftWorld.initial)) :
    result.2.seeds = PqxdhRecordLiftLazyTable.initial ∧ ∀ slot role, result.2.used slot role = false := by
  have kept := startup_fields setup source ensureInit identityIndex serverKeyId identity PqxdhRecordLiftWorld.initial result supported
  refine ⟨congrArg Prod.snd kept, ?_⟩
  have unused := congrArg Prod.fst kept
  intro slot role
  exact congrFun (congrFun unused slot) role

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupFields.startup_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupFields.startup_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupFields.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupFields.initialized
