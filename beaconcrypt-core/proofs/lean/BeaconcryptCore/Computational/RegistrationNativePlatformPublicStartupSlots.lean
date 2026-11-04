-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame
/-! Actual generated startup preserves the preexisting private record-seed cache and role-use map while retaining its real ML-pin hash cache and all counted draws. Cold source startup therefore derives the empty private record state required by the materialization coupling. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupSlots
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I}

private def fields (before : PqxdhRecordLiftWorld.State n) := (before.used, before.seeds)

private theorem sampled (work : ProbComp A) (before : PqxdhRecordLiftWorld.State n)
    (result : A × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.sampled work).run before)) :
    fields result.2 = fields before := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨value, _actual, rfl⟩ := supported
  rfl

private theorem initialize_fields (created : PqxdhLiveServerConstruction.Created Unit)
    (before : PqxdhRecordLiftWorld.State n) (result : Unit × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.initializeServer created).run before)) :
    fields result.2 = fields before := by
  cases present : before.server <;>
    simp only [PqxdhRecordLiftWorld.initializeServer, StateT.run, present, mem_support_pure_iff] at supported <;>
    cases supported <;> rfl

private theorem hash (bytes : Pqxdh.Bytes) (before : PqxdhRecordLiftWorld.State n)
    (result : CtxRomAuth.CtxDigest × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before)) :
    fields result.2 = fields before := by
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨middle, drawn, rfl⟩ := supported
  exact sampled _ (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) before) middle drawn

/-- Every actual generated-startup outcome preserves the same private record slots; its shared ML-pin hash and uniform/counter effects remain literal. -/
theorem startup (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (before : PqxdhRecordLiftWorld.State n)
    (result : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run before)) :
    result.2.used = before.used ∧ result.2.seeds = before.seeds := by
  simp only [RegistrationNativePublicStartupFrame.startup, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨constructed, built, continued⟩ := supported
  have constructedFields := sampled _ before constructed built
  cases present : constructed.1.1 with
  | none =>
    simp only [present, StateT.run_pure, mem_support_pure_iff] at continued
    cases continued
    exact Prod.mk.inj constructedFields
  | some created =>
    simp only [present, StateT.run_bind, mem_support_bind_iff] at continued
    obtain ⟨generated, called, continued⟩ := continued
    have generatedFields := sampled _ _ generated called
    cases credential : generated.1 with
    | none =>
      simp only [credential, StateT.run_pure, mem_support_pure_iff] at continued
      cases continued
      exact Prod.mk.inj (generatedFields.trans constructedFields)
    | some key =>
      simp only [credential, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, mem_support_pure_iff] at continued
      obtain ⟨installed, installation, hashed, hashedRun, rfl⟩ := continued
      exact Prod.mk.inj ((hash _ _ hashed hashedRun).trans
        ((initialize_fields _ _ installed installation).trans (generatedFields.trans constructedFields)))

/-- The initialized source material experiment starts with unused private record slots and no cached record seed, without resetting its warmed shared hash cache. -/
theorem cold (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (result : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run PqxdhRecordLiftWorld.initial)) :
    (∀ slot role, result.2.used slot role = false) ∧ result.2.seeds = PqxdhRecordLiftLazyTable.initial := by
  have exactFields := startup setup source ensureInit identityIndex serverKeyId identity _ result supported
  exact ⟨fun slot role => congrFun (congrFun exactFields.1 slot) role, exactFields.2⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupSlots

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupSlots.startup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupSlots.startup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupSlots.cold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupSlots.cold
