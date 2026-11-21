-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendSlots
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath

/-! Existing session identities persist backwards through the exact interpreted typed, raw and full native ledger callbacks. The chronological path theorem retains the same actual intermediate states under arbitrary outer key replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordSessionSlots (Preserves)
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

/-- Interpreting the actual public Word callback preserves every surviving old slot. -/
theorem typed (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typedImpl query).run before)) :
    Preserves before.1.server.sessions result.2.1.server.sessions := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  apply RegistrationNativeSecretWordFrontendSlots.query setup checks wire sign selectedOwner selectedAccept publicPrekey query before.1 reached.1
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst called

private theorem program_preserves {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (StateT (State n KemSK source) ProbComp))
    (step : ∀ query before result, result ∈ support ((implementation query).run before) →
      Preserves before.1.server.sessions result.2.1.server.sessions)
    (work : OracleComp spec Value) (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ implementation work).run before)) :
    Preserves before.1.server.sessions result.2.1.server.sessions := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query implementation
    (fun current => Preserves before.1.server.sessions current.1.server.sessions)
    (fun query current prior next reached => RegistrationNativeSecretWordSessionSlots.trans _ _ _ prior
      (step query current next reached)) work before _ result supported
  exact RegistrationNativeSecretWordSessionSlots.refl _

/-- Every raw adapter path retains the same surviving old session values. -/
theorem raw (query : RegistrationNativeInterface.Spec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeInterface.Spec.Range query × State n KemSK source)
    (supported : result ∈ support ((rawImpl query).run before)) :
    Preserves before.1.server.sessions result.2.1.server.sessions := by
  exact program_preserves typedImpl
    (typed setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey)
    (RegistrationNativeRawAdapter.adapter wire query) before result supported

/-- A complete original ledger callback preserves each surviving old session, including secrecy coin/send programs. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl query).run before)) :
    Preserves before.2.1.server.sessions result.2.2.1.server.sessions := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  exact program_preserves rawImpl
    (raw setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey)
    _ before.2 reached called

/-- The same chronological original path transports a surviving Ready back to its earlier existing slot. -/
theorem path (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × State n KemSK source}
    {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl) before entries after) :
    Preserves before.2.1.server.sessions after.2.1.server.sessions := by
  apply RegistrationNativeSecretWordTargetPath.preserves _
    (fun current => Preserves before.2.1.server.sessions current.2.1.server.sessions)
    (fun query current result prior reached => RegistrationNativeSecretWordSessionSlots.trans _ _ _ prior
      (full setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
        serverKeyId bounds query current result reached)) path
  exact RegistrationNativeSecretWordSessionSlots.refl _

end BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource.typed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource.raw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource.full
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource.path
