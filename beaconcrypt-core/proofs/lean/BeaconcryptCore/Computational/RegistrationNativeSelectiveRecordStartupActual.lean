-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup

/-! Literal startup factoring of the cold actual guarded selective native program. Pointwise reductions after startup receive the entire reached World state, including the actual shared ML-pin hash cache, counters, role-use state and any startup effects. The thin local state starts at its actual initializer; the World is never reset. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartupActual
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveRecordStartup (program outcome)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

/-- The complete cold actual program splits at the literal successful/failed native startup and continues with the entire reached World state. -/
theorem actual_start (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    RegistrationNativeRecordPackage.actual setup (RegistrationNativeWire.ledgerCodec wire) route
      (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary) =
      (do
        let initialized ← (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
          (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run PqxdhRecordLiftWorld.initial
        match initialized.1 with
        | none => pure none
        | some born =>
            (fun result => some (PqxdhRegistrationJointServerBirth.encode born.created,
              result.1.1.1, (result.1.1.2, result.1.2))) <$>
              (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
                (RegistrationNativeSelectiveHiddenInterpreter.run setup checks wire source born.native.credential seed scalar candidate provider
                  selectedOwner selectedAccept serverKeyId bounds mode
                  (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩)
                  born.native.frontend (RegistrationNativeSelectiveHiddenInterpreter.initial providerState))).run initialized.2) := by
  simp only [RegistrationNativeRecordPackage.actual, program, RegistrationNativeSelectiveHiddenStartup.program,
    simulateQ_map, StateT.run_map, Functor.map_map, simulateQ_bind, StateT.run_bind, map_bind]
  apply bind_congr
  rintro ⟨_ | born, reached⟩
  · simp only [simulateQ_pure, StateT.run_pure, map_pure, outcome, Option.map_none]
  · simp only [bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
    rfl

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartupActual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartupActual.actual_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartupActual.actual_start
