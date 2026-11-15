-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.RegistrationNativeStageTrace

/-! The selected dynamic-writer runtime authentication-origin exception is exactly the existence of a protected successful callback without prior same-key unsigned issuance in its actual same-execution journal. The journal is private analysis state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeMldsaOriginEvent (Bad)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK V Platform E : Type} {base : OracleSpec ι} {source : Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

def BadCalls (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) : Prop :=
  ∃ call ∈ calls, Bad source server call.query call.before.1 call.reply

noncomputable def flagged (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) : Bool := by
  classical
  exact calls.any fun call => decide (Bad source server call.query call.before.1 call.reply)

/-- The journal flag is exactly existence of an actual protected unsigned-origin failure cut. -/
theorem flagged_iff (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) :
    flagged server calls = true ↔ BadCalls server calls := by
  classical
  simp only [flagged, List.any_eq_true, decide_eq_true_eq, BadCalls]

/-- The same single exception covers every protected successful Beacon finish, using its actual earlier signing prefix. -/
theorem finish_issued (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (good : ¬ BadCalls server calls) (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes)
    (before after : Whole)
    (member : (⟨.inr (.finish index (some packet)), before, .ok (some application), after⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ calls)
    (current : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : before.1.beacons[index]? = some current) (phase : current.phase = .initSent pending oneTime)
    (keyProtected : pending.binding.server_pin.public_key = server.publicKey) :
    MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key) (RegistrationNativeMldsaShared.nativeProject before.1))) := by
  by_contra absent
  exact good ⟨_, member, .finish index packet application before.1 current pending oneTime found phase keyProtected absent⟩

variable (source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (server : Credential source)
local notation "implementation" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created server
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativePlatformOrdinaryExperiment.handler

noncomputable def project (before : Whole × List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) : Whole × Bool := (before.1, flagged server before.2)

/-- The exact source journal transports the protected-origin flag jointly with the complete native and platform state. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : Whole × List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) :
    Prod.map id (project source server) <$> (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run before =
      (simulateQ (RegistrationNativePlatformOrdinaryMldsaOriginSource.handler source setup checks wire route representation created view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer server) work).run (project source server before) := by
  classical
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [RegistrationNativeStageTrace.handler, RegistrationNativePlatformOrdinaryMldsaOriginSource.handler, project,
    flagged, List.any_append, List.any_cons, List.any_nil, Bool.or_false, RegistrationNativePlatformOrdinaryKemClientJournal.actual,
    StateT.run, Functor.map_map, Prod.map, id_eq]

variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V) (previous : Platform)

noncomputable def game (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) : ProbComp Bool := by
  classical
  exact do
    let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKid
    match initialized with
    | none => pure false
    | some initial => (fun result => @decide (flagged initial.credential result.2.2 = true ∨ CacheHasCollision result.2.1.1.server.world.world.1.primitive.2) (Classical.propDecidable _)) <$>
        (simulateQ (RegistrationNativeStageTrace.handler
          (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential
            view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer))
          (adversary initial.public)).run ((initial.state, previous), [])

/-- The initialized private source journal retains its origin flag and literal final cache jointly. -/
theorem game_exact (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) :
    game (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous ensureInit identityIndex serverKid =
      RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.badGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous ensureInit identityIndex serverKid := by
  classical
  unfold game RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.badGame
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some initial =>
      have same := congrArg (fun distribution => (fun result => @decide (result.2.2 = true ∨ CacheHasCollision result.2.1.1.server.world.world.1.primitive.2) (Classical.propDecidable _)) <$> distribution)
        (program source setup checks wire route representation initial.created view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer initial.credential (adversary initial.public) ((initial.state, previous), []))
      simpa only [Functor.map_map, Prod.map, id_eq, project, flagged, List.any_nil] using same

/-- The complete corrected source journal charges its protected-origin-or-final-collision union once. -/
theorem typed (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (game (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous
      ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous
        ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (cap + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous ensureInit identityIndex serverKeyId)) := by
  rw [game_exact]
  exact RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.typed source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous adversary cap bounded ensureInit identityIndex serverKeyId

/-- The complete corrected source journal charges its protected-origin-or-final-collision union once. -/
theorem compiled (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (game (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
      previous ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
        previous ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId)) := by
  rw [game_exact]
  exact RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.compiled source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous bounds mode adversary budget bounded ensureInit identityIndex serverKeyId

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.flagged_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.flagged_iff


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.finish_issued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.finish_issued

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.game_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.game_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal.compiled
