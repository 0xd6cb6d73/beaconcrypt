-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialAdmitted

/-! Concrete execution of the original public material controller through its actual selective demand, current environment and cursor/Protocol/private World. Bind and map preserve every reached state coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialExecution
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeSelectiveMaterialService (Local handler)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Reader Response Secret Value Next : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp)) (codec : Codec Reader Response)

abbrev Result (n : Nat) (Auxiliary KemSK ProviderState Secret Value : Type) :=
  (((Value × Local n Auxiliary KemSK ProviderState) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret

noncomputable def execute (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value)
    (before : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) : ProbComp (Result n Auxiliary KemSK ProviderState Secret Value) :=
  CborRawRecordOriginFlatten.interpret service codec route
    ((simulateQ (handler setup wire sign seed scalar candidate provider) work).run before) shell control secret

theorem pure_source (value : Value) (before : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    execute setup wire route sign seed scalar candidate provider service codec (pure value) before shell control secret =
      pure ((((value, before), shell), control), secret) := by
  simp only [execute, simulateQ_pure, StateT.run_pure, CborRawRecordOriginFlatten.interpret_pure]

theorem bind_source (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value)
    (next : Value → OracleComp (RegistrationNativePairedServerService.PublicSpec n) Next)
    (before : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    execute setup wire route sign seed scalar candidate provider service codec (work >>= next) before shell control secret =
      (execute setup wire route sign seed scalar candidate provider service codec work before shell control secret >>= fun result =>
        execute setup wire route sign seed scalar candidate provider service codec (next result.1.1.1.1)
          result.1.1.1.2 result.1.1.2 result.1.2 result.2) := by
  simp only [execute, simulateQ_bind, StateT.run_bind, CborRawRecordOriginFlatten.interpret_bind]

end BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialExecution.pure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialExecution.pure_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialExecution.bind_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialExecution.bind_source
