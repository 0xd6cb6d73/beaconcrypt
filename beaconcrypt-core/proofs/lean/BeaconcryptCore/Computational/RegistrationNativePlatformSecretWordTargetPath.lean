-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathConcat
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerMap
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal

/-! The current common-state Word interpreter has a literal raw/full-ledger chronological path. Erasure drops only its trace coordinate, retaining persistent platform and private provider state. Original ledger entries and every intermediate supported callback are derived from the same run. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativePlatformSecretWordExecution (TracedState drop typed traced)
open RegistrationNativeSecretWordTargetPath (Path)
variable {n : Nat} {I KemSK Front A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (controller : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT Front (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "traceFull" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
  (traced setup wire route sign input inside provider outer controller)
local notation "plainFull" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
  (typed setup wire route sign input inside provider outer controller)
local notation "projectFull" => Prod.map id (drop (Front := Front) (n := n) (KemSK := KemSK))

/-- Every full current callback erases only the trace, with its original ledger and common/private states intact. -/
theorem full (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × TracedState Front n KemSK) :
    Prod.map id projectFull <$> (traceFull query).run before = (plainFull query).run (projectFull before) :=
  RegistrationNativeTargetLedgerMap.full drop _ _
    (RegistrationNativePlatformSecretWordExecution.traced_source setup wire route sign input inside provider outer controller)
    setup.source.crypto wire serverKeyId bounds query before

/-- Trace erasure applies pointwise to every intermediate source cut. -/
theorem path {before after : RegistrationNativeLedger.State × TracedState Front n KemSK}
    {entries : List RegistrationNativeInterface.Entry} (actual : Path traceFull before entries after) :
    Path plainFull (projectFull before) entries (projectFull after) := by
  apply RegistrationNativeSecretWordTargetPathMap.map traceFull plainFull projectFull _ actual
  intro query current result called
  have mapped := Set.mem_image_of_mem (Prod.map id projectFull) called
  rw [← support_map, full setup wire route sign input inside provider outer controller serverKeyId bounds] at mapped
  exact mapped

/-- Actual full calls append exactly their original query and actual reply to the same ledger. -/
theorem records {before after : RegistrationNativeLedger.State × TracedState Front n KemSK}
    {entries : List RegistrationNativeInterface.Entry} (actual : Path traceFull before entries after) :
    after.1.transcript = before.1.transcript ++ entries :=
  RegistrationNativeSecretWordTargetPath.records traceFull (fun current => current.1.transcript)
    (fun query current result called => RegistrationNativeLedgerJournal.handler_records _ setup.source.crypto
      (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query current result called) actual

/-- A supported current raw run supplies its literal transcript path and the pointwise trace-erased path. -/
theorem run (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : TracedState Front n KemSK)
    (result : RegistrationNativeEvents.Observed A (TracedState Front n KemSK))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (traced setup wire route sign input inside provider outer controller) mode work before)) :
    Path traceFull (RegistrationNativeLedger.empty, before) result.2.1.transcript result.2 ∧
      Path plainFull (RegistrationNativeLedger.empty, drop before) result.2.1.transcript (projectFull result.2) := by
  obtain ⟨entries, actual⟩ := RegistrationNativeSecretWordTargetPath.program traceFull
    (RegistrationNativeInterface.asModeO mode work) (RegistrationNativeLedger.empty, before) result supported
  have recorded := records setup wire route sign input inside provider outer controller serverKeyId bounds actual
  simp only [RegistrationNativeLedger.empty, List.nil_append] at recorded
  rw [← recorded] at actual
  exact ⟨actual, path setup wire route sign input inside provider outer controller serverKeyId bounds actual⟩

/-- No continuation is changed when the same complete raw execution drops its proof trace. -/
theorem erase_run (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : TracedState Front n KemSK) :
    Prod.map id projectFull <$> RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (traced setup wire route sign input inside provider outer controller) mode work before =
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (typed setup wire route sign input inside provider outer controller) mode work (drop before) := by
  simpa only [RegistrationNativeFullCompiler.run, Prod.map_apply, id_eq] using
    RegistrationNativeTargetStateMap.program projectFull traceFull plainFull
      (full setup wire route sign input inside provider outer controller serverKeyId bounds)
      (RegistrationNativeInterface.asModeO mode work) (RegistrationNativeLedger.empty, before)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath.full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath.records

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath.erase_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath.erase_run
