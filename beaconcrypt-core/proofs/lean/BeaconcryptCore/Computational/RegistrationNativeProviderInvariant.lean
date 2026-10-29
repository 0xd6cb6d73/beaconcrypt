-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderSource

/-! Pending coherence and the empty local record-request field hold under every concrete provider source. Their proof uses the actual open frontend support projection, so candidate providers, failures and arbitrary original-ledger sampling introduce no new public eligibility condition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderInvariant
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (FrontState execute)
open RegistrationNativePublicInvariantMetadata (Good)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem program_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : FrontState n KemSK ProviderState source) (result : Value × FrontState n KemSK ProviderState source)
    (valid : Good before.1)
    (supported : result ∈ support
      ((execute setup wire route sign seed scalar provider
        (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey)
          work)).run before)) : Good result.2.1 :=
  RegistrationNativePublicInvariantRun.program_good setup checks wire sign selectedOwner selectedAccept publicPrekey
    work before.1 (result.1, result.2.1) valid
    (RegistrationNativeProviderSource.observed_support setup wire route sign seed scalar provider _ before result supported)

/-- The actual full original ledger preserves coherence and exact local record metadata under any provider. -/
theorem run_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : FrontState n KemSK ProviderState source)
    (result : (Value × RegistrationNativeLedger.State) × FrontState n KemSK ProviderState source)
    (valid : Good before.1)
    (supported : result ∈ support
      ((execute setup wire route sign seed scalar provider
        (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey)
          (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work))).run before)) : Good result.2.1 :=
  program_good setup checks wire route sign seed scalar provider selectedOwner selectedAccept publicPrekey _ before result valid supported

/-- Successful actual startup internally supplies the metadata invariant for every supported complete provider-source ledger outcome. -/
theorem initialized_run_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (initial afterStart : RegistrationNativePublicInterpreter.State n KemSK)
    (started : RegistrationNativePublicStartup.Started source)
    (initialized : (some started, afterStart) ∈ support
      ((RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId identity).run initial))
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeProviderInterpreter.State n KemSK ProviderState)
    (result : (Value × RegistrationNativeLedger.State) × FrontState n KemSK ProviderState source)
    (supported : result ∈ support
      ((execute setup wire route (RegistrationNativeMldsa.owned source started.credential) seed scalar provider
        (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source
          (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicPrekey)
          (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work))).run (started.frontend, before))) :
    Good result.2.1 :=
  run_good setup checks wire route (RegistrationNativeMldsa.owned source started.credential) seed scalar provider
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work (started.frontend, before) result
    (RegistrationNativePublicInvariantStartup.start_good setup ensureInit identityIndex serverKeyId identity initial afterStart started initialized)
    supported

end BeaconcryptCore.Computational.RegistrationNativeProviderInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderInvariant.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderInvariant.program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderInvariant.run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderInvariant.run_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderInvariant.initialized_run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderInvariant.initialized_run_good
