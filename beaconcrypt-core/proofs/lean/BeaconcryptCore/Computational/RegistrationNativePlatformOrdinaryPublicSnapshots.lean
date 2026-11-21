-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformKemInitializedJournal

/-! Public acceptance-ordinal snapshots instrument one actual dynamic-writer native run. Private prefix events never choose the stopping point; erasure preserves the full source state and every stopped program retains the original resource contract. This structural bridge alone does not prove the native actual-publication primitive reduction. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeInterface (FullSpec asModeO queryClass)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)


variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => RegistrationNativeLedger.State × (Native × Platform)
local notation "typed" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

/-- Count every publicly visible raw accept attempt, including parse/authentication failures. -/
def attempts (journal : PqxdhDeploymentSessionSnapshot.Journal FullSpec) : Nat :=
  journal.countP (fun entry => queryClass entry.1 = (3 : Fin 14))

def stopAt (ordinal : Nat) (journal : PqxdhDeploymentSessionSnapshot.Journal FullSpec) : Prop := ordinal < attempts journal
instance (ordinal : Nat) : DecidablePred (stopAt ordinal) := fun journal => Nat.decLt ordinal (attempts journal)

omit primitives in
/-- The public ordinal selector makes no primitive request and never consults a private ownership/failure event. -/
theorem stopAt_empty (ordinal : Nat) : ¬ stopAt ordinal [] := by simp [stopAt, attempts]

def defaults : (query : FullSpec.Domain) → FullSpec.Range query
  | .inl (.inl coin) => (0 : Fin (coin + 1))
  | .inl (.inr (.create _ _ _)) => none
  | .inl (.inr (.bundle _)) => none
  | .inl (.inr (.accept _)) => none
  | .inl (.inr (.build _ _)) => none
  | .inl (.inr (.finish _ _)) => none
  | .inl (.inr (.hmac _ _)) => PqxdhSecretInputKdf.zeroSalt
  | .inl (.inr (.hash _)) => List.Vector.replicate 64 0
  | .inl (.inr (.serverSend _ _)) => none
  | .inl (.inr (.serverRaw _)) => .None
  | .inl (.inr (.beaconSend _ _)) => none
  | .inl (.inr (.beaconRaw _ _)) => .None
  | .inr (.test _ _ _) => none
  | .inr (.fresh _ _) => none

noncomputable def full : QueryImpl FullSpec (StateT Whole ProbComp) :=
  RegistrationNativeFullCompiler.handler setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    created.server.server.metadata.sender bounds typed

noncomputable def run (count : Nat) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : Native) :=
  PqxdhDeploymentSessionSnapshots.run
    (full setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds created credential)
    (fun ordinal : Fin count => stopAt ordinal.val) (asModeO mode work) (RegistrationNativeLedger.empty, (before, previous))

/-- Erasing every receipt retains the actual full Native ledger, shared allocator state, private pool, counters and all later callbacks. -/
theorem erase_full (count : Nat) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : Native) :
    (fun result => (result.1, result.2.native)) <$> run setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds mode previous created credential count work before =
      RegistrationNativeFullCompiler.run setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) created.server.server.metadata.sender bounds typed mode work (before, previous) :=
  PqxdhDeploymentSessionSnapshots.erase _ _ _ _

/-- The simultaneous public-prefix instrumentation erases to the literal chosen runtime, retaining its original value, ledger and both actual native/platform poststates. -/
theorem erase_native (count : Nat) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : Native) :
    (fun result => (((result.1, result.2.native.1), result.2.native.2.1), result.2.native.2.2)) <$>
      run setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode previous created credential count work before =
      ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous) := by
  let reindex : Value × Whole → ((Value × RegistrationNativeLedger.State) × Native) × Platform :=
    fun result => (((result.1, result.2.1), result.2.2.1), result.2.2.2)
  have moved := congrArg (fun distribution => reindex <$> distribution)
    (erase_full setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds mode previous created credential count work before)
  rw [RegistrationNativeFullCompiler.compile_run] at moved
  have packed := congrArg (fun execution => execution.run (before, previous))
    (RegistrationNativePlatformPackedState.simulate_pack
      (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer)
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        created.server.server.metadata.sender bounds mode work))
  change ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous)) =
      (simulateQ typed (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        created.server.server.metadata.sender bounds mode work)).run (before, previous) at packed
  rw [← packed] at moved
  simp only [Functor.map_map] at moved
  change (fun result => (((result.1, result.2.native.1), result.2.native.2.1), result.2.native.2.2)) <$>
      run setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode previous created credential count work before =
      id <$> ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous) at moved
  simpa only [id_map] using moved

/-- Every selected acceptance receipt is the same exact one-prefix marginal of the single source execution. -/
theorem project (count : Nat) (target : Fin count) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : Native) :
    (fun result => (result.1, PqxdhDeploymentSessionSnapshots.project target result.2)) <$>
      run setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode previous created credential count work before =
      PqxdhDeploymentSessionSnapshot.run
        (full setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds created credential)
        (stopAt target.val) (asModeO mode work) (RegistrationNativeLedger.empty, (before, previous)) :=
  PqxdhDeploymentSessionSnapshots.project_run _ _ _ _ _

/-- The private event is measured only after selecting a public ordinal; it does not select the stopping callback. The explicit acceptance-position sum needs no independence. -/
theorem captured_bound (count : Nat) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : Native)
    (event : Whole → Prop) :
    Pr{let result ← (run setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode previous created credential count work before)}[
      ∃ target snapshot, result.2.captured target = some snapshot ∧ event snapshot.2] ≤
      ∑ target : Fin count, Pr{let result ← ((simulateQ
        (full setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds created credential)
        (PqxdhDeploymentServerAuthEmbed.freeze defaults (stopAt target.val) (asModeO mode work))).run (RegistrationNativeLedger.empty, (before, previous)))}[event result.2] := by
  classical
  apply le_trans (prEvent_exists_le _ _) _
  apply Finset.sum_le_sum
  intro target _
  exact PqxdhDeploymentSessionSnapshots.captured_le_frozen _ defaults _ target (asModeO mode work) _ (stopAt_empty target.val) event

omit primitives in
/-- Every public stopped native program preserves the complete original raw budget coordinate, including fresh messages. -/
theorem stopped_respects (ordinal : Nat) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work) (kind : Fin 14) :
    (PqxdhDeploymentServerAuthEmbed.freeze defaults (stopAt ordinal) (asModeO mode work)).IsQueryBoundP
      (fun query => queryClass query = kind) (budget.cap kind) :=
  PqxdhDeploymentCausalPublication.freeze_query_bound defaults (stopAt ordinal) (asModeO mode work) _ _
    (RegistrationNativeInterface.asModeO_bound budget work bounded kind) []

/-- Complete initialized private snapshot family. The adversary still receives only its original startup public value and raw callback replies. -/
noncomputable def initialized (count : Nat) : ProbComp (Option
    (RegistrationNativeExperiment.Initial n KemSK source × (Value × PqxdhDeploymentSessionSnapshots.State (Fin count) FullSpec Whole))) := do
  let born ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match born with
  | none => pure none
  | some initial => (fun result => some (initial, result)) <$>
      (run setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode previous
        initial.created initial.credential count (adversary initial.public) initial.state)

/-- Erasing every initialized receipt retains the literal source profile's original event, full native poststate and actual shared platform poststate. -/
theorem initialized_erase (count : Nat)
    (event : RegistrationNativeEvents.Observed Value Native → Bool) :
    (fun outcome => match outcome with
      | none => (false, previous)
      | some (_initial, result) => (event (result.1, (result.2.native.1, result.2.native.2.1)), result.2.native.2.2)) <$>
      initialized (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        bounds mode adversary previous count =
      ((RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary event).run previous) := by
  simp only [initialized, map_bind, RegistrationNativePlatformOrdinaryExperiment.profile, StateT.run_bind,
    StateT.run_lift, bind_assoc, pure_bind]
  apply bind_congr
  intro born
  cases born with
  | none => simp only [map_pure, StateT.run_pure]
  | some initial =>
    have erased := erase_native setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds mode previous initial.created initial.credential count (adversary initial.public) initial.state
    have observed := congrArg (fun distribution =>
      (fun result : ((Value × RegistrationNativeLedger.State) × Native) × Platform =>
        (event (result.1.1.1, (result.1.1.2, result.1.2)), result.2)) <$> distribution) erased
    simpa only [Functor.map_map, StateT.run_map] using observed

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.stopAt_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.stopAt_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.erase_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.erase_full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.erase_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.erase_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.captured_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.captured_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.stopped_respects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.stopped_respects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.initialized_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots.initialized_erase
