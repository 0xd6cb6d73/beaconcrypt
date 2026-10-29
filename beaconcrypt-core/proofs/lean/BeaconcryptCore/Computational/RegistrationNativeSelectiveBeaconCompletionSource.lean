-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconOrigin

/-! The actual Beacon terminal completion binds its original paired service result before applying the owner phase transition. The exact current owner, outer environment, thin private state and shared World are retained by the source diagram. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Reader Response Secret Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp)) (codec : Codec Reader Response)

abbrev Result (n : Nat) (KemSK ProviderState Secret Value : Type) :=
  (((Value × RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) × CborRecordWorldClient.Shell) ×
    PqxdhRecordLiftProtocol.Control n) × Secret

noncomputable def execute (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret) : ProbComp (Result n KemSK ProviderState Secret Value) :=
  CborRawRecordOriginFlatten.interpret service codec route
    ((simulateQ (RegistrationNativeSelectiveMaterialSource.closedLocal setup wire sign seed scalar candidate provider) work).run before)
      shell world secret

local notation "run" => execute setup wire route sign seed scalar candidate provider service codec

theorem pure_source (value : Value) (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (shell : CborRecordWorldClient.Shell) (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    run (pure value) before shell world secret = pure ((((value, before), shell), world), secret) := by
  simp only [execute, simulateQ_pure, StateT.run_pure, CborRawRecordOriginFlatten.interpret_pure]

theorem bind_source (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (next : Value → OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Next)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    run (work >>= next) before shell world secret =
      (run work before shell world secret >>= fun middle =>
        run (next middle.1.1.1.1) middle.1.1.1.2 middle.1.1.2 middle.1.2 middle.2) := by
  simp only [execute, simulateQ_bind, StateT.run_bind, CborRawRecordOriginFlatten.interpret_bind]


theorem map_source {Mapped : Type} (f : Value → Mapped)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    run (f <$> work) before shell world secret =
      (fun middle => ((((f middle.1.1.1.1, middle.1.1.1.2), middle.1.1.2), middle.1.2), middle.2)) <$>
        run work before shell world secret := by
  simp only [execute, simulateQ_map, StateT.run_map,
    RegistrationNativeHiddenEnvironmentWorld.interpret_map]

/-- The original completion AST binds the same paired result before settling the current owner. -/
theorem complete_source (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (env : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) setup.source owner ready).run current).run env) = (do
      let completed ← simulateQ (RegistrationBeaconReferenceFinish.service (n := n) (KemSK := KemSK))
        (RegistrationNativePairedBeaconService.admitted setup.source owner.worldOwner owner.pin.binding.identity_key_id
          ready.descriptor ready.reference)
      ((RegistrationBeaconReferenceCompletion.after (RegistrationBeaconReferenceCompiler.effect (n := n) (KemSK := KemSK)) owner completed).run current).run env) := by
  simp only [RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left]
  apply bind_congr
  intro completed
  cases completed with
  | fail error => rfl
  | div => rfl
  | ok completed => cases completed <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource.pure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource.pure_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource.bind_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource.bind_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource.complete_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource.map_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource.map_source
