-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontendProgress
import BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun

/-! The original material-demand allowance supplies the fresh selected-slot room internally throughout the complete known108-byte native frontend. The exact source equation retains every original ledger/frontend/chronological result and every reached World, signing, KEM and selective-service state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectRun
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (seeds : RegistrationNativeG3AuditedWorld.Seeds n)

/-- Every original bounded adaptive native continuation has its literal direct flag/108-byte table service source, with no per-prefix room supplied by the caller. -/
theorem program_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (count : Nat) (bounded : work.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) count)
    (before : State n KemSK ProviderState) (room : before.1.1.keys.next + count ≤ n) :
    (simulateQ (RegistrationNativeG3MaterializedLocal.handler true table seeds setup codec route wire sign seed scalar candidate provider) work).run before =
      (simulateQ (RegistrationNativeG3MaterializedDirectFrontend.handler table setup codec route wire sign seed scalar candidate provider seeds) work).run before := by
  induction work using OracleComp.inductionOn generalizing count before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have affordable : before.1.1.keys.next + (if RegistrationNativePublicCaps.IsDemand query then 1 else 0) ≤ n := by
        split_ifs with counted
        · have positive := bounded.1.resolve_left (not_not.mpr counted)
          omega
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [RegistrationNativeG3MaterializedDirectFrontend.query_source table setup codec route wire sign seed scalar candidate provider seeds query before affordable]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro result supported
      have grown := RegistrationNativeG3MaterializedDirectFrontendProgress.query_progress setup codec route wire sign seed scalar candidate provider
        table seeds query before result supported
      have tailRoom : result.2.1.1.keys.next + (if RegistrationNativePublicCaps.IsDemand query then count - 1 else count) ≤ n := by
        split_ifs at grown ⊢ with counted
        · have positive := bounded.1.resolve_left (not_not.mpr counted)
          omega
        · omega
      exact ih result.1 _ (bounded.2 result.1) result.2 tailRoom

/-- The complete initialized original-ledger chronology derives every direct-service source/capacity certificate from original Respects and the genuine cold allocator. -/
theorem cold_run_source (budget : PqxdhDeploymentInterface.Budget)
    (table : Slot (budget.cap 4 + budget.cap 5) → Material)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds (budget.cap 4 + budget.cap 5))
    (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (bounded : RegistrationNativeInterface.Respects budget work)
    (front : RegistrationNativePublicFrontend.State source)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State (budget.cap 4 + budget.cap 5) KemSK ProviderState)
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    (simulateQ (RegistrationNativeG3MaterializedLocal.handler true table seeds setup codec route wire sign seed scalar candidate provider)
      (RegistrationNativeG2Trace.program
        (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front))).run
          (RegistrationNativeG3AuditTraceRun.cold frame ∅, world) =
      (simulateQ (RegistrationNativeG3MaterializedDirectFrontend.handler table setup codec route wire sign seed scalar candidate provider seeds)
        (RegistrationNativeG2Trace.program
          (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front))).run
            (RegistrationNativeG3AuditTraceRun.cold frame ∅, world) := by
  apply program_source
  · apply RegistrationNativeG2Trace.program_bound
    exact RegistrationNativePublicCaps.run_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work budget bounded front
  · simp only [RegistrationNativeG3AuditTraceRun.cold, RegistrationNativeHiddenService.initial, Nat.zero_add]
    exact le_rfl

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectRun.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectRun.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectRun.cold_run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectRun.cold_run_source
