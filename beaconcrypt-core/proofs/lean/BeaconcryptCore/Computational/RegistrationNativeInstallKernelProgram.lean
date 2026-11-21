-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace
import BeaconcryptCore.Computational.RegistrationNativeTargetStateMap

/-! The complete actual typed program retains the same chronological trace beside its full physical runtime. The source map is a literal state reassociation, so final installation ordinals and private hidden slots are observed jointly rather than reconstructed from separate marginals. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelProgram
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveInstallKernel (State typed)
open RegistrationNativeInstallRuntimeTrace (Runtime callback runtime attach)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def split (before : State n KemSK ProviderState Secret source) :
    RegistrationNativePublicFrontend.State source × Runtime n KemSK ProviderState Secret :=
  (before.2.1.1.1.1, runtime before)

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (selectedOwner selectedAccept : Nat)
local notation "monitored" => typed (source := source) setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
local notation "original" => RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
local notation "closed" => QueryImpl.flattenStateT (QueryImpl.mapStateTBase (callback setup wire sign seed scalar candidate provider service codec route) original)

/-- One exact actual callback retains its full frontend, trace and private runtime under a bijective reassociation. -/
theorem query (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK ProviderState Secret source) :
    Prod.map id split <$> (monitored request).run before = (closed request).run (split before) := by
  rw [RegistrationNativeInstallRuntimeTrace.typed_source, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [Functor.map_map, split, attach, RegistrationNativeInstallRuntimeTrace.runtime,
    RegistrationNativeInstallRuntime.runtime, RegistrationNativeInstallRuntime.attach, Prod.map_def, id_eq]

/-- The entire adaptive typed execution retains its original complete trace and hidden physical state in the same supported outcome. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State n KemSK ProviderState Secret source) :
    Prod.map id split <$> (simulateQ monitored work).run before =
      (simulateQ closed work).run (split before) :=
  RegistrationNativeTargetStateMap.program split monitored closed
    (query setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept) work before

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelProgram.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelProgram.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelProgram.program
