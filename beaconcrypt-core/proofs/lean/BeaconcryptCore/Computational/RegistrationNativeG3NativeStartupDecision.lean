-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginal
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric

/-! A pure ledger decision forgets only the complete startup context and trace after the unchanged executable client finishes. The original open retained client reads none of the independently billed startup metric coordinates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupDecision
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def decision {source : RegistrationNativeMldsa.Source}
    (observe : Value × RegistrationNativeLedger.State → Bool)
    (result : RegistrationNativeG3NativeStartupUniformValue.Result source n Value) : Bool :=
  match result.2 with
  | none => false
  | some actual => observe actual.1.1

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (serverKeyId : U64) (selectedOwner selectedAccept : Nat)
  (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (observe : Value × RegistrationNativeLedger.State → Bool)

noncomputable def continuation (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State n) :
    OracleComp (RegistrationNativeOpenKey.Spec KemSK) Bool :=
  match initialized.1 with
  | none => pure false
  | some born =>
      RegistrationNativeOpenKey.client setup.source (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
        (RegistrationNativeOpenRetained.client setup wire route (RegistrationNativeMldsa.owned source born.credential)
          ((observe ∘ Prod.fst) <$>
            RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source born.credential)
              selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode
              (adversary ⟨setup.joint.publicKeys seed, born.credential.publicKey, serverKeyId⟩) born.frontend)
          { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 })

/-- The final full-value observer is exactly the original ledger-only continuation of the same successful or failed startup. -/
theorem after_decision (context : RegistrationNativeG3NativeStartupAlias.Context source n) :
    decision observe <$> RegistrationNativeG3NativeStartupUniformValue.after setup checks wire source route serverKeyId
      selectedOwner selectedAccept bounds mode adversary context =
      continuation setup checks wire source route serverKeyId selectedOwner selectedAccept bounds mode adversary observe
        context.seed context.scalar (context.initialized.1.map RegistrationNativeHiddenStartup.Started.native, context.initialized.2) := by
  cases initialized : context.initialized.1 with
  | none => simp only [RegistrationNativeG3NativeStartupUniformValue.after, continuation, initialized, Option.map_none, map_pure, decision]
  | some born =>
      simp only [RegistrationNativeG3NativeStartupUniformValue.after, continuation, initialized, Option.map_some,
        Functor.map_map, RegistrationNativeG3NativeCheckedUniformSource.openProgram, RegistrationNativeG3NativeStartupFields.word_eval]
      rw [← RegistrationNativeG3NativeStartupMarginal.client_map]
      apply congrArg (RegistrationNativeOpenKey.client setup.source _ _)
      have erased := congrArg (Functor.map (observe ∘ Prod.fst)) (RegistrationNativeG2Trace.program_erase (n := n) (KemSK := KemSK)
        (RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source born.native.credential)
          selectedOwner selectedAccept (setup.dh.publicKey context.scalar) serverKeyId bounds mode
          (adversary ⟨setup.joint.publicKeys context.seed, born.native.credential.publicKey, serverKeyId⟩) born.native.frontend)
        RegistrationNativeG2Trace.initial)
      simp only [Functor.map_map] at erased
      simp only [RegistrationNativeOpenRetained.client, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
        RegistrationNativeG3NativeUniformAuditBound.ordinary, RegistrationNativePublicInterpreter.initial, decision]
      have closed := congrArg (fun program =>
        (simulateQ (RegistrationNativeOpenRetained.compiler setup wire route
          (RegistrationNativeMldsa.owned source born.native.credential)) program).run'
          (RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear
            (RegistrationNativeG3NativeUniformAuditBound.ordinary context.initialized.2)))) erased
      simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
        RegistrationNativeG2Trace.program, RegistrationNativeG3NativeUniformAuditBound.ordinary,
        Function.comp_def] using closed

/-- The original executable continuation does not inspect erased startup accounting coordinates. -/
theorem continuation_mask (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State n) :
    continuation setup checks wire source route serverKeyId selectedOwner selectedAccept bounds mode adversary observe seed scalar initialized =
      continuation setup checks wire source route serverKeyId selectedOwner selectedAccept bounds mode adversary observe seed scalar
        (initialized.1, RegistrationNativeG3MetricWorld.mask initialized.2) := by
  unfold continuation
  cases initialized.1 with
  | none => rfl
  | some born =>
      apply congrArg (RegistrationNativeOpenKey.client setup.source _ _)
      exact RegistrationNativeG3RetainedMetric.client_input setup wire route (RegistrationNativeMldsa.owned source born.credential) _ _

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupDecision
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupDecision.after_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupDecision.after_decision
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupDecision.continuation_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupDecision.continuation_mask
