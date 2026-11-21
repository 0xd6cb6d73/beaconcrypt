-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupDecision

/-! Both complete candidate-independent decision clients factor through the same seed, scalar and startup coin prefix, with only unread accounting fields normalized. The full client keeps all context and trace until the pure final ledger observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginalProgram
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeG3NativeStartupDecision (decision continuation)
open RegistrationNativeG3NativeStartupUniformValue (coins)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (observe : Value × RegistrationNativeLedger.State → Bool)

noncomputable def actual : OracleComp (RegistrationNativeOpenKey.Spec KemSK) Bool := do
  let seed ← simulateQ coins PqxdhJointIdentity.sampleSeed
  let scalar ← simulateQ coins PqxdhJointGapDh.sampleScalar
  let initialized ← simulateQ coins (Prod.map (Option.map RegistrationNativeHiddenStartup.Started.native) RegistrationNativeG3MetricWorld.mask <$>
    RegistrationNativeG3MaterializedStartup.startup (n := n) setup wire route source ensureInit identityIndex serverKeyId seed)
  continuation setup checks wire source route serverKeyId selectedOwner selectedAccept bounds mode adversary observe seed scalar initialized

noncomputable def reference : OracleComp (RegistrationNativeOpenKey.Spec KemSK) Bool := do
  let seed ← simulateQ coins PqxdhJointIdentity.sampleSeed
  let scalar ← simulateQ coins PqxdhJointGapDh.sampleScalar
  let initialized ← simulateQ coins (Prod.map id RegistrationNativeG3MetricWorld.mask <$>
    (RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)).run
      (PqxdhRecordLiftWorld.initial (n := n)))
  continuation setup checks wire source route serverKeyId selectedOwner selectedAccept bounds mode adversary observe seed scalar initialized

/-- The complete full-value native client has this same pure ledger marginal after actual startup. -/
theorem actual_source :
    decision observe <$> RegistrationNativeG3NativeStartupUniformValue.program (n := n) setup checks wire source route ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary =
      actual (n := n) setup checks wire source route ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary observe := by
  unfold RegistrationNativeG3NativeStartupUniformValue.program RegistrationNativeG3NativeStartupAlias.prior actual
  simp only [simulateQ_bind, simulateQ_pure, pure_bind, bind_assoc, map_bind,
    RegistrationNativeG3NativeStartupDecision.after_decision, simulateQ_map, bind_map_left]
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  apply bind_congr
  intro initialized
  exact RegistrationNativeG3NativeStartupDecision.continuation_mask setup checks wire source route serverKeyId selectedOwner selectedAccept bounds mode adversary observe
    seed scalar (initialized.1.map RegistrationNativeHiddenStartup.Started.native, initialized.2)

/-- The old executable startup client's original ledger decision factors through the same normalized reference startup prefix. -/
theorem reference_source :
    RegistrationNativeOpenKeyStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary observe =
      reference (n := n) setup checks wire source route ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary observe := by
  unfold RegistrationNativeOpenKeyStartup.client reference
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  unfold RegistrationNativeOpenRetainedStartup.client RegistrationNativeOpenRetainedStartup.start
  rw [RegistrationNativeG3NativeStartupMarginal.client_prefix]
  simp only [simulateQ_map, bind_map_left]
  apply bind_congr
  intro initialized
  have masked := RegistrationNativeG3NativeStartupDecision.continuation_mask setup checks wire source route serverKeyId selectedOwner selectedAccept bounds mode adversary observe seed scalar initialized
  cases found : initialized.1 with
  | none =>
      simp only [continuation, found, Prod.map_def, id_eq, RegistrationNativeOpenKey.client, RegistrationNativeOpenKey.phaseClient,
        simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
  | some born =>
      simpa only [continuation, found, Prod.map_def, id_eq, PqxdhJointGapDh.challenge] using masked

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginalProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginalProgram.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginalProgram.actual_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginalProgram.reference_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginalProgram.reference_source
