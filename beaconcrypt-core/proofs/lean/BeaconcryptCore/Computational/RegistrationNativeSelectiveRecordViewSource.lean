-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup

/-! The native all-random endpoint retains the permitted origin map, original ledger and actual produced-frame view through the literal effectful startup. Only the cursor and private CTX implementation fields remain outside the permitted observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

/-- The full allowed record view of the actual all-random native entropy execution has the same literal origin observation. -/
theorem ideal_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode) :
    RegistrationNativeRecordPackage.ctx modes setup (RegistrationNativeWire.ledgerCodec wire) route
      (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary) =
      (fun result => RegistrationNativeRecordPackage.nativeView result.1 result.2.base.produced) <$>
        RegistrationNativeSelectiveEntropyStartup.run modes id setup checks wire route source ensureInit identityIndex serverKeyId
          seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary PqxdhRecordLiftIdeal.CtxPrivate.initial := by
  rw [RegistrationNativeRecordPackage.ctx_source]
  simp only [RegistrationNativeSelectiveRecordStartup.program, RegistrationNativeSelectiveEntropyStartup.run,
    CborRawRecordOriginFlatten.interpret, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSource.ideal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSource.ideal_source
