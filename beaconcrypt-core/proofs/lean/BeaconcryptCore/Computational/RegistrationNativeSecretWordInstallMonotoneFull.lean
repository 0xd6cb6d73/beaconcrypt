-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotone
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath

/-! The original full-ledger source preserves all earlier installation ordinals through arbitrary later typed, raw and private secrecy callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotoneFull
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetTracedSource (State)
open RegistrationNativeSecretWordInstallOrdinals (messages)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem program_extension {Index Private Result : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (StateT Private ProbComp))
    (values : Private → List Message)
    (step : ∀ query before result, result ∈ support ((implementation query).run before) →
      ∃ added, values result.2 = values before ++ added)
    (work : OracleComp spec Result) (before : Private) (result : Result × Private)
    (supported : result ∈ support ((simulateQ implementation work).run before)) :
    ∃ added, values result.2 = values before ++ added := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨[], (List.append_nil _).symm⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      obtain ⟨head, first⟩ := step query before middle called
      obtain ⟨tail, last⟩ := ih middle.1 middle.2 continued
      exact ⟨head ++ tail, by rw [last, first, List.append_assoc]⟩

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "typedImpl" => RegistrationNativeSecretWordTargetTracedSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "rawImpl" => RegistrationNativeRawAdapter.handler wire typedImpl
local notation "fullImpl" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl

private theorem raw (role : PqxdhRecordLiftInterface.Role) (query : RegistrationNativeInterface.Spec.Domain)
    (before : State n KemSK source) (result : RegistrationNativeInterface.Spec.Range query × State n KemSK source)
    (supported : result ∈ support ((rawImpl query).run before)) :
    ∃ added, messages role result.2.1.2.events = messages role before.1.2.events ++ added := by
  apply program_extension typedImpl (fun current => messages role current.1.2.events)
    (fun request first reached called => RegistrationNativeSecretWordInstallMonotone.typed setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey role request first reached called) (RegistrationNativeRawAdapter.adapter wire query) before result
  simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose] using supported

/-- Every complete original ledger callback extends each role's successful descriptor list. -/
theorem full (role : PqxdhRecordLiftInterface.Role) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((fullImpl query).run before)) :
    ∃ added, messages role result.2.2.1.2.events = messages role before.2.1.2.events ++ added := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  exact program_extension rawImpl (fun current => messages role current.1.2.events)
    (raw setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey role)
    _ before.2 reached called

/-- The actual original chronological suffix retains every earlier successful descriptor at its original ordinal. -/
theorem path (role : PqxdhRecordLiftInterface.Role)
    {before after : RegistrationNativeLedger.State × State n KemSK source}
    {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path fullImpl before entries after) :
    ∃ added, messages role after.2.1.2.events = messages role before.2.1.2.events ++ added := by
  apply RegistrationNativeSecretWordTargetPath.preserves fullImpl
    (fun current => ∃ added, messages role current.2.1.2.events = messages role before.2.1.2.events ++ added)
    (fun query first result prior called => by
      obtain ⟨head, firstEq⟩ := prior
      obtain ⟨tail, lastEq⟩ := full setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds role query first result called
      exact ⟨head ++ tail, by rw [lastEq, firstEq, List.append_assoc]⟩) actual
  exact ⟨[], (List.append_nil _).symm⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotoneFull
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotoneFull.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotoneFull.full
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotoneFull.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotoneFull.path
