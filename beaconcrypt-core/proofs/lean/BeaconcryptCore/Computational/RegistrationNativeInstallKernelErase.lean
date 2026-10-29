-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerMap

/-! Erasing only the chronological kernel observer commutes with every actual original raw and secrecy callback, and with the complete adaptive full-ledger execution. The same physical control slots, provider state, shared World cache and private service state are retained. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelErase
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveInstallKernel (State typed)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (selectedOwner selectedAccept : Nat)
local notation "monitored" => typed (source := source) setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
local notation "plain" => RegistrationNativeSelectiveAllocation.typed (source := source) setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
local notation "project" => Prod.map id (Prod.snd : State n KemSK ProviderState Secret source → _)

/-- Every actual full ledger callback projects the same reached monitored kernel state to its literal original selective callback. -/
theorem full (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK ProviderState Secret source) :
    Prod.map id project <$>
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds monitored query).run before =
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds plain query).run (project before) :=
  RegistrationNativeTargetLedgerMap.full Prod.snd monitored plain
    (RegistrationNativeSelectiveInstallKernel.typed_erase setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept)
    setup.source.crypto wire serverKeyId bounds query before

/-- The entire original adaptive run retains precisely its full ledger and reached physical private state after erasing chronology. -/
theorem run (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK ProviderState Secret source) :
    Prod.map id project <$> RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds monitored mode work before =
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds plain mode work before.2 := by
  simpa only [RegistrationNativeFullCompiler.run, Prod.map_apply, id_eq] using
    RegistrationNativeTargetStateMap.program project
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds monitored)
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds plain)
      (full setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept serverKeyId bounds)
      (RegistrationNativeInterface.asModeO mode work) (RegistrationNativeLedger.empty, before)

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelErase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelErase.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelErase.full
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelErase.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelErase.run
