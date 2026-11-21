-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath

/-! The concrete monitored typed kernel is the same execution as closing the original Word frontend under its chronological observer. The full original ledger and private interpreter state are retained by the explicit final reassociation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option quotPrecheck false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedProgram
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer
local notation "frontend" => RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
local notation "observedFrontend" => (RegistrationNativeSecretWordFrontendTrace.handler.mapStateTBase frontend).flattenStateT

/-- The concrete monitored callback kernel is exactly the two actual stateful interpreters, with no execution equality supplied by a caller. -/
theorem typed_eq : RegistrationNativeSecretWordTargetTracedSource.typed (n := n) (source := source)
    setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey =
      ((implementation).mapStateTBase observedFrontend).flattenStateT := by
  funext query before
  rcases before with ⟨⟨front, trace⟩, privateState⟩
  change (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
    (simulateQ implementation ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((frontend query).run front)).run trace)).run privateState =
      (((implementation).mapStateTBase observedFrontend).flattenStateT query).run ((front, trace), privateState)
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rw [simulateQ_map, StateT.run_map]
  simp only [Functor.map_map]

/-- The actual complete original Word program and its actual observer close into the same monitored full-ledger kernel. -/
theorem run_source (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeSecretWordMessage.State source) (trace : RegistrationNativeSecretWordFrontendTrace.State)
    (privateState : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    (fun result => (result.1.1.1.1, (result.1.1.1.2, ((result.1.1.2, result.1.2), result.2)))) <$>
      (simulateQ implementation ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
        (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
          serverKeyId bounds mode work before)).run trace)).run privateState =
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (RegistrationNativeSecretWordTargetTracedSource.typed setup checks wire route sign input inside provider outer
          selectedOwner selectedAccept publicPrekey) mode work ((before, trace), privateState) := by
  rw [RegistrationNativeSecretWordFrontend.run]
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    RegistrationNativeSecretWordFrontendTrace.handler frontend
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) before trace]
  rw [simulateQ_map, StateT.run_map]
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    implementation observedFrontend (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) (before, trace) privateState]
  rw [RegistrationNativeFullCompiler.compile_run, typed_eq setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey]
  simp only [Functor.map_map]
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedProgram.typed_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedProgram.typed_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedProgram.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedProgram.run_source
