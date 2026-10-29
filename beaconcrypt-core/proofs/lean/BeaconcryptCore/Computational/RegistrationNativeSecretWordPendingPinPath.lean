-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath

/-! The actual original Word typed, raw and complete ledger source preserves the strong pending-pin invariant. Initialization discharges the invariant from the actual empty roster at every supported chronological cut. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordPendingPin (Holds)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "typedImpl" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "rawImpl" => RegistrationNativeRawAdapter.handler wire typedImpl

/-- The actual interpreted typed callback preserves the initialized stored-owner pending-pin invariant. -/
theorem typed (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (valid : Holds before.1.beacons)
    (supported : result ∈ support ((typedImpl query).run before)) :
    Holds result.2.1.beacons := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  apply RegistrationNativeSecretWordPendingPinFrontend.typed_keeps setup checks wire sign selectedOwner selectedAccept publicPrekey query before.1 reached.1 valid
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst called

private theorem program_preserves {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (StateT (State n KemSK source) ProbComp))
    (step : ∀ query before result, Holds before.1.beacons →
      result ∈ support ((implementation query).run before) → Holds result.2.1.beacons)
    (work : OracleComp spec Value) (before : State n KemSK source) (result : Value × State n KemSK source)
    (valid : Holds before.1.beacons)
    (supported : result ∈ support ((simulateQ implementation work).run before)) :
    Holds result.2.1.beacons :=
  OracleComp.simulateQ_run_preserves_inv_of_query implementation
    (fun current => Holds current.1.beacons)
    (fun query current prior reached called => step query current reached prior called) work before valid result supported

/-- Every raw adapter path preserves the same actual pending-pin invariant. -/
theorem raw (query : RegistrationNativeInterface.Spec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeInterface.Spec.Range query × State n KemSK source)
    (valid : Holds before.1.beacons)
    (supported : result ∈ support ((rawImpl query).run before)) :
    Holds result.2.1.beacons :=
  program_preserves typedImpl
    (typed setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey)
    (RegistrationNativeRawAdapter.adapter wire query) before result valid supported

/-- A complete original ledger callback retains the pending-pin invariant through all private secrecy draws and internal sends. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (valid : Holds before.2.1.beacons)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl query).run before)) :
    Holds result.2.2.1.beacons := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  exact program_preserves rawImpl
    (raw setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey)
    _ before.2 reached valid called

/-- Every same-execution chronological prefix retains the actual stored-owner pending pin. -/
theorem path (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × State n KemSK source}
    {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl) before entries after)
    (valid : Holds before.2.1.beacons) :
    Holds after.2.1.beacons :=
  RegistrationNativeSecretWordTargetPath.preserves _
    (fun current => Holds current.2.1.beacons)
    (fun query current result prior reached => full setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
      serverKeyId bounds query current result prior reached) path valid

/-- Every actual original prefix starts coherent from the empty roster and retains the actual stored-owner pending pin. -/
theorem initialized (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (before : State n KemSK source) (empty : before.1.beacons = [])
    {entries : List RegistrationNativeInterface.Entry}
    {after : RegistrationNativeLedger.State × State n KemSK source}
    (supported : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl)
      (RegistrationNativeLedger.empty, before) entries after) : Holds after.2.1.beacons := by
  apply path setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds supported
  intro index owner found
  rw [empty, List.getElem?_nil] at found
  cases found

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath.typed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath.raw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath.full
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath.path
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath.initialized
