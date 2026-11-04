-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotEffects
/-! The real noninstalling source effects retain the exact Server handle observer and all actual mutable source replies and states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerEffects
open PqxdhDeploymentInterface (Handle)
open RegistrationNativePlatformRecordPartnerSnapshotHandles (update)
open RegistrationNativePlatformPairedPublicationFree (Allowed Quiet)
open RegistrationNativePlatformPublicSlotEffects (effects)
variable {n : Nat} {KemSK S A : Type}
local notation "serverHandler" => RegistrationNativePlatformRecordPartnerSnapshotHandles.handler (n := n) (KemSK := KemSK) PqxdhRecordLiftInterface.Role.server

/-- Each literal noninstalling source operation preserves the actual Server receipt handles. -/
theorem query_neutral (query : (RegistrationNativePlatformEffectCompiler.Spec n).Domain)
    (allowed : Allowed query) (before : List Handle) :
    (simulateQ serverHandler (effects query)).run before=
      (fun reply=>(reply,before)) <$> effects query := by
  cases query with
  | inl query=>
    rcases query with coin|capability
    · simp only [effects,RegistrationNativePairedCompile.effects,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerSnapshotHandles.handler,StateT.run,update];rfl
    · cases capability
      case installServer keyId binding kernel=>exact (allowed .server rfl).elim
      case installBeacon owner shell kernel=>exact (allowed .beacon rfl).elim
      all_goals simp only [effects,RegistrationNativePairedCompile.effects,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerSnapshotHandles.handler,StateT.run,update];rfl
  | inr coin=>simp only [effects,RegistrationNativePairedCompile.effects,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerSnapshotHandles.handler,StateT.run,update];rfl

/-- All adaptive stateful noninstalling source continuations preserve this exact observer. -/
theorem program_neutral (work : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) A)
    (allowed : work.AllQueriesSatisfy Allowed) (before : List Handle) :
    (simulateQ serverHandler (simulateQ effects work)).run before=
      (fun reply=>(reply,before)) <$> simulateQ effects work := by
  induction work using OracleComp.inductionOn with
  | pure value=>simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
    rw [query_neutral query allowed.1 before,bind_map_left]
    apply bind_congr
    intro reply
    exact ih reply (allowed.2 reply)

/-- The actual returned source state remains paired with its unchanged receipt prefix. -/
theorem state_neutral (work : StateT S (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (quiet : Quiet work) (sourceBefore : S) (before : List Handle) :
    (simulateQ serverHandler (simulateQ effects (work.run sourceBefore))).run before=
      (fun reply=>(reply,before)) <$> simulateQ effects (work.run sourceBefore) :=
  program_neutral _ (quiet sourceBefore) before
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerEffects.query_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerEffects.query_neutral

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerEffects.program_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerEffects.program_neutral

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerEffects.state_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerEffects.state_neutral
