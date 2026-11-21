-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelMaterialStep
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelFreeStep
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStep
import BeaconcryptCore.Computational.RegistrationNativeInstallLedgerPath
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelInitial

/-! Every actual guarded native callback supplies its original raw successful-handle receipt. Complete original ledger execution therefore preserves the installation ordinal and physical hidden-slot association at every same-execution prefix, with no caller-owned installer, source-game or target-origin premise. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveInstallKernel (State typed)
open RegistrationNativeInstallKernelStorage (Valid events slots Selected)
open RegistrationNativeInstallTypedEntry (entry)
open RegistrationNativeInstallStep (RoleStep)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (selectedOwner selectedAccept : Nat)
local notation "actual" => typed (source := source) setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
local notation "native" => RegistrationNativeRawAdapter.handler wire actual
local notation "selected" => Selected setup seed scalar candidate
local notation "invariant" => RegistrationNativeInstallLedger.Holds events slots Valid selected

/-- Every original actual typed native callback supplies its same-reply installation ordinal and selected hidden-origin receipt. -/
theorem typed_receipts (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK ProviderState Secret source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK ProviderState Secret source)
    (prior : Valid before) (supported : result ∈ support ((actual query).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    RoleStep role (events before) (events result.2) (entry query result.1) (slots result.2) selected := by
  have free (quiet : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5) :=
    RegistrationNativeInstallKernelFreeStep.step setup checks wire sign seed scalar candidate provider service codec route
      selectedOwner selectedAccept query quiet before result supported role
  cases query with
  | inl coin => exact free (by constructor <;> simp [RegistrationNativeRawAdapter.kind])
  | inr query => cases query with
    | build handle application =>
        exact RegistrationNativeInstallKernelMaterialStep.build setup checks wire sign seed scalar candidate provider service codec route
          selectedOwner selectedAccept role handle application before result supported
    | finish index packet =>
        exact RegistrationNativeInstallKernelMaterialStep.finish setup checks wire sign seed scalar candidate provider service codec route
          selectedOwner selectedAccept role index packet before prior result supported
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
    (before : State n KemSK ProviderState Secret source)
    (result : RegistrationNativeInterface.Spec.Range query × State n KemSK ProviderState Secret source)
    (prior : Valid before) (supported : result ∈ support ((native query).run before)) :
    RegistrationNativeInstallLedger.Storage slots Valid before result.2 :=
  RegistrationNativeInstallRawStorage.raw actual wire slots Valid
    (RegistrationNativeInstallKernelStorage.typed_storage setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept)
    query before result prior supported

/-- The actual raw callback's complete failed or successful poststate supplies the same original ledger-entry receipt. -/
theorem raw_receipts (query : RegistrationNativeInterface.Spec.Domain)
    (before : State n KemSK ProviderState Secret source)
    (result : RegistrationNativeInterface.Spec.Range query × State n KemSK ProviderState Secret source)
    (prior : Valid before) (supported : result ∈ support ((native query).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    RoleStep role (events before) (events result.2) ⟨.inl query, result.1⟩ (slots result.2) selected :=
  RegistrationNativeInstallRawStep.raw actual wire events slots Valid selected
    (typed_receipts setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept)
    query before result prior supported role

/-- Every actual original full-ledger callback preserves successful installation ordinals and the physical hidden-slot association. -/
theorem full_step (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK ProviderState Secret source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK ProviderState Secret source))
    (prior : invariant before)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds actual query).run before)) :
    invariant result.2 :=
  RegistrationNativeInstallLedger.full_step native events slots Valid selected
    (raw_storage setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept)
    (raw_receipts setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept)
    setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query before result prior supported

/-- The installation association holds at every prefix of the same actual original full-ledger path, starting with empty chronology. -/
theorem path (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (before : State n KemSK ProviderState Secret source)
    {after : RegistrationNativeLedger.State × State n KemSK ProviderState Secret source} {entries : List RegistrationNativeInterface.Entry}
    (prior : Valid before) (empty : events before = [])
    (actualPath : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds actual)
      (RegistrationNativeLedger.empty, before) entries after) : invariant after :=
  RegistrationNativeInstallLedger.path native events slots Valid selected
    (raw_storage setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept)
    (raw_receipts setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept)
    setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds actualPath
    (RegistrationNativeInstallLedger.initial events slots Valid selected before prior empty)

/-- The complete original ordinary or publication-mode run derives the same actual native installation invariant. -/
theorem run (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK ProviderState Secret source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK ProviderState Secret source))
    (prior : Valid before) (empty : events before = [])
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds actual mode work before)) :
    invariant result.2 :=
  RegistrationNativeInstallLedger.run native events slots Valid selected
    (raw_storage setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept)
    (raw_receipts setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept)
    setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds
    (RegistrationNativeInterface.asModeO mode work) before result prior empty supported

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.typed_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.typed_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.raw_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.raw_storage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.raw_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.raw_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.full_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.full_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.path
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger.run
