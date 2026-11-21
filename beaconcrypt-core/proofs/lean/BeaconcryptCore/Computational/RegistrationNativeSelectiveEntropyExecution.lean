-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative

/-! The stateful thin-backend closure commutes with every adaptive actual raw frontend program and its unchanged full original secrecy ledger. This source statement precedes the allocation correspondence needed to identify its Beacon routing with the older entropy interface. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State)
open RegistrationNativeSelectiveEntropyEffects (close close_run pure_source bind_source)
variable {n : Nat} {ι KemSK ProviderState Index Value : Type} {base : OracleSpec ι} {spec : OracleSpec Index}
variable {source : RegistrationNativeMldsa.Source}

/-- Closing the concrete frontend preserves arbitrary adaptive raw continuations and both full local states. -/
theorem close_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (implementation : QueryImpl spec (RegistrationNativePublicFrontend.M n KemSK source)) (work : OracleComp spec Value) :
    close setup wire sign seed scalar candidate provider (simulateQ implementation work) =
      simulateQ (fun query => close setup wire sign seed scalar candidate provider (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, pure_source]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_source]
      congr 1
      funext reply
      exact ih reply

/-- The raw adapter and complete actual typed frontend close to the same actual native query interpreter. -/
theorem raw_program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (work : OracleComp RegistrationNativeInterface.Spec Value) (before : State n KemSK ProviderState source) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider)
        ((simulateQ (RegistrationNativeHiddenEnvironmentRaw.frontend setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept (setup.dh.publicKey scalar)) work).run before.1)).run before.2 =
      (simulateQ (RegistrationNativeSelectiveEntropyNative.handler setup checks wire source credential seed scalar candidate provider
        selectedOwner selectedAccept) work).run before := by
  rw [← close_run, close_program]
  rfl

/-- The thin native original ledger execution is exactly its stateful raw World source, including the original private test and fresh draws. -/
theorem run_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativePublicFrontend.State source)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      RegistrationNativeSelectiveHiddenInterpreter.run setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
        serverKeyId bounds mode work frontend before =
      (simulateQ (RegistrationNativeSelectiveEntropyNative.handler setup checks wire source credential seed scalar candidate provider
        selectedOwner selectedAccept)
        (RegistrationNativeLedger.wrap setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds
          (RegistrationNativeInterface.asModeO mode work))).run (frontend, before) := by
  unfold RegistrationNativeSelectiveHiddenInterpreter.run RegistrationNativePublicFrontend.run
  rw [RegistrationNativeFullCompiler.compile, RegistrationNativeRawAdapter.compile, ← QueryImpl.simulateQ_compose]
  exact raw_program setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept _ (frontend, before)

end BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution.close_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution.close_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution.raw_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution.raw_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution.run_source
