-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedSource
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerMap
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger

/-! Actual monitored full-ledger execution supplies both its literal monitored path and the projected original path. Original target metadata may use only these same-execution cuts; no path is chosen from a separately projected marginal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetTracedSource (State project)
open RegistrationNativeSecretWordTargetPath (Path)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "traced" => RegistrationNativeSecretWordTargetTracedSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "plain" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "traceFull" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds traced
local notation "plainFull" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds plain
local notation "projectFull" => Prod.map id (project (n := n) (KemSK := KemSK) (source := source))

/-- Every full actual callback erases only the monitor, retaining its literal original ledger and complete source state. -/
theorem full (query : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State × State n KemSK source) :
    Prod.map id projectFull <$> (traceFull query).run before = (plainFull query).run (projectFull before) :=
  RegistrationNativeTargetLedgerMap.full project traced plain
    (RegistrationNativeSecretWordTargetTracedSource.typed_source setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey)
    setup.source.crypto wire serverKeyId bounds query before

/-- Every actual monitored full path projects at each original callback, preserving all of its chronological source cuts. -/
theorem path {before after : RegistrationNativeLedger.State × State n KemSK source}
    {entries : List RegistrationNativeInterface.Entry} (actual : Path traceFull before entries after) :
    Path plainFull (projectFull before) entries (projectFull after) := by
  apply RegistrationNativeSecretWordTargetPathMap.map traceFull plainFull projectFull _ actual
  intro query current result called
  have mapped := Set.mem_image_of_mem (Prod.map id projectFull) called
  rw [← support_map, full setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds] at mapped
  exact mapped

/-- A supported original monitored full run supplies the same literal path and its pointwise original source projection. -/
theorem run (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK source)
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds traced mode work before)) :
    Path traceFull (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2 ∧
      Path plainFull (RegistrationNativeLedger.empty, project before) observed.2.1.transcript (projectFull observed.2) := by
  obtain ⟨entries, actual⟩ := RegistrationNativeSecretWordTargetPath.program traceFull
    (RegistrationNativeInterface.asModeO mode work) (RegistrationNativeLedger.empty, before) observed supported
  have recorded := RegistrationNativeSecretWordTargetPath.records traceFull (fun current => current.1.transcript)
    (fun query current result called => by
      have mapped := Set.mem_image_of_mem (Prod.map id projectFull) called
      rw [← support_map, full setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds] at mapped
      exact RegistrationNativeSecretWordTargetLedger.step_trace setup checks wire route sign input inside provider outer
        selectedOwner selectedAccept publicPrekey serverKeyId bounds query (projectFull current) (Prod.map id projectFull result) mapped) actual
  simp only [RegistrationNativeLedger.empty, List.nil_append] at recorded
  rw [← recorded] at actual
  exact ⟨actual, path setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds actual⟩
/-- Dropping only the chronological observer commutes with the actual complete original full-ledger run. -/
theorem erase_run (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK source) :
    Prod.map id projectFull <$> RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds traced mode work before =
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds plain mode work (project before) := by
  simpa only [RegistrationNativeFullCompiler.run, Prod.map_apply, id_eq] using
    RegistrationNativeTargetStateMap.program projectFull traceFull plainFull
      (full setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds)
      (RegistrationNativeInterface.asModeO mode work) (RegistrationNativeLedger.empty, before)

/-- Every actual monitored path records exactly its own original callback list in the unchanged native ledger. -/
theorem records {before after : RegistrationNativeLedger.State × State n KemSK source}
    {entries : List RegistrationNativeInterface.Entry} (actual : Path traceFull before entries after) :
    after.1.transcript = before.1.transcript ++ entries := by
  have projected := path setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds actual
  have recorded := RegistrationNativeSecretWordTargetPath.records plainFull (fun current => current.1.transcript)
    (fun query current result called => RegistrationNativeSecretWordTargetLedger.step_trace setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey serverKeyId bounds query current result called) projected
  simpa only [Prod.map_def, id_eq] using recorded

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath.full
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath.path
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath.erase_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath.erase_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedPath.records
