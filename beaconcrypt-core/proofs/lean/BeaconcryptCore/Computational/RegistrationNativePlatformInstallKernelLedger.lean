-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelServer
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeaconStep
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelFreeStep
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStep
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallLedgerPath
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallStep
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles
/-! The literal shared-platform Server build pairs its retained descriptor with the same returned physical peer, after every source and allocator outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformSelectiveInstallKernel (State)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativePlatformInstallKernelStorage (Valid events slots Selected)
open RegistrationNativeInstallStep (RoleStep)
open RegistrationNativeInstallTypedEntry (entry)
open BeaconcryptCore.Refinement
variable {Value : Type}
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "sign" => RegistrationNativeMldsa.owned source credential
local notation "actual" => RegistrationNativePlatformSelectiveInstallKernel.typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route

local notation "native" => RegistrationNativeRawAdapter.handler canonical actual
local notation "selected" => Selected setup seed scalar candidate
local notation "invariant" => RegistrationNativeInstallLedger.Holds events slots Valid selected

/-- Every original actual typed native callback supplies its same-reply installation ordinal and selected hidden-origin receipt. -/
theorem typed_receipts (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK ProviderState Platform Secret source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK ProviderState Platform Secret source)
    (prior : Valid before) (supported : result ∈ support ((actual query).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    RoleStep role (events before) (events result.2) (entry query result.1) (slots result.2) selected := by
  have free (quiet : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5) :=
    RegistrationNativePlatformInstallKernelFreeStep.step setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query quiet before result supported role
  cases query with
  | inl coin => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])
  | inr query => cases query with
    | build handle application =>
        exact RegistrationNativePlatformInstallKernelServer.build_step setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route role handle application before result supported
    | finish index packet =>
        exact RegistrationNativePlatformInstallKernelBeaconStep.finish setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route role index packet before prior result supported
    | create edPin mlPin keyId => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])
    | bundle owner => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])
    | accept packet => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])
    | hmac key message => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])
    | hash bytes => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])
    | serverSend keyId plaintext => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])
    | serverRaw raw => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])
    | beaconSend owner plaintext => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])
    | beaconRaw owner raw => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])


/-- Literal raw parsing preserves validity and every already hidden physical handle under the actual kernel. -/
theorem raw_storage (query : RegistrationNativeInterface.Spec.Domain)
    (before : State n KemSK ProviderState Platform Secret source)
    (result : RegistrationNativeInterface.Spec.Range query × State n KemSK ProviderState Platform Secret source)
    (prior : Valid before) (supported : result ∈ support ((native query).run before)) :
    RegistrationNativeInstallLedger.Storage slots Valid before result.2 :=
  RegistrationNativeInstallRawStorage.raw actual canonical slots Valid
    (RegistrationNativePlatformInstallKernelStorage.typed_storage setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route)
    query before result prior supported

/-- The actual raw callback's complete failed or successful poststate supplies the same original ledger-entry receipt. -/
theorem raw_receipts (query : RegistrationNativeInterface.Spec.Domain)
    (before : State n KemSK ProviderState Platform Secret source)
    (result : RegistrationNativeInterface.Spec.Range query × State n KemSK ProviderState Platform Secret source)
    (prior : Valid before) (supported : result ∈ support ((native query).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    RoleStep role (events before) (events result.2) ⟨.inl query, result.1⟩ (slots result.2) selected :=
  RegistrationNativeInstallRawStep.raw actual canonical events slots Valid selected
    (typed_receipts setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route)
    query before result prior supported role

/-- Every actual original full-ledger callback preserves successful installation ordinals and the physical hidden-slot association. -/
theorem full_step (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK ProviderState Platform Secret source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK ProviderState Platform Secret source))
    (prior : invariant before)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto canonical serverKeyId bounds actual query).run before)) :
    invariant result.2 :=
  RegistrationNativeInstallLedger.full_step native events slots Valid selected
    (raw_storage setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route)
    (raw_receipts setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route)
    setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) serverKeyId bounds query before result prior supported

/-- The installation association holds at every prefix of the same actual original full-ledger path, starting with empty chronology. -/
theorem path (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (before : State n KemSK ProviderState Platform Secret source)
    {after : RegistrationNativeLedger.State × State n KemSK ProviderState Platform Secret source} {entries : List RegistrationNativeInterface.Entry}
    (prior : Valid before) (empty : events before = [])
    (actualPath : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto canonical serverKeyId bounds actual)
      (RegistrationNativeLedger.empty, before) entries after) : invariant after :=
  RegistrationNativeInstallLedger.path native events slots Valid selected
    (raw_storage setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route)
    (raw_receipts setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route)
    setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) serverKeyId bounds actualPath
    (RegistrationNativeInstallLedger.initial events slots Valid selected before prior empty)

/-- The complete original ordinary or publication-mode run derives the same actual native installation invariant. -/
theorem run (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK ProviderState Platform Secret source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK ProviderState Platform Secret source))
    (prior : Valid before) (empty : events before = [])
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical serverKeyId bounds actual mode work before)) :
    invariant result.2 :=
  RegistrationNativeInstallLedger.run native events slots Valid selected
    (raw_storage setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route)
    (raw_receipts setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route)
    setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) serverKeyId bounds
    (RegistrationNativeInterface.asModeO mode work) before result prior empty supported

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.typed_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.typed_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.raw_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.raw_storage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.raw_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.raw_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.full_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.full_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger.run
