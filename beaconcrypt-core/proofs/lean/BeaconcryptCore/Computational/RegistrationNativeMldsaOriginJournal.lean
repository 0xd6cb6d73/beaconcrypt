-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity
import BeaconcryptCore.Computational.RegistrationNativeStageTrace

/-! The original authentication-origin exception is exactly the existence of a protected successful callback without prior same-key unsigned issuance in its actual same-execution journal. The journal is private analysis state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeMldsaOriginEvent (Bad)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι} {source : Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def BadCalls (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)) : Prop :=
  ∃ call ∈ calls, Bad source server call.query call.before call.reply

noncomputable def flagged (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)) : Bool := by
  classical
  exact calls.any fun call => decide (Bad source server call.query call.before call.reply)

/-- The journal flag is exactly existence of an actual protected unsigned-origin failure cut. -/
theorem flagged_iff (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)) :
    flagged server calls = true ↔ BadCalls server calls := by
  classical
  simp only [flagged, List.any_eq_true, decide_eq_true_eq, BadCalls]

/-- The same single exception covers every protected successful Beacon finish, using its actual earlier signing prefix. -/
theorem finish_issued (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native))
    (good : ¬ BadCalls server calls) (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes)
    (before after : Native)
    (member : (⟨.inr (.finish index (some packet)), before, .ok (some application), after⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) ∈ calls)
    (current : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : before.beacons[index]? = some current) (phase : current.phase = .initSent pending oneTime)
    (keyProtected : pending.binding.server_pin.public_key = server.publicKey) :
    MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key) (RegistrationNativeMldsaShared.nativeProject before))) := by
  by_contra absent
  exact good ⟨_, member, .finish index packet application before current pending oneTime found phase keyProtected absent⟩

variable (source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (server : Credential source)
local notation "implementation" => RegistrationNativeExperiment.handler setup checks wire route representation created source server
attribute [local irreducible] RegistrationNativeExperiment.handler

noncomputable def project (before : Native × List (Call RegistrationNativeRawAdapter.TypedSpec Native)) : Native × Bool := (before.1, flagged server before.2)

/-- The exact source journal transports to the original native marker jointly with the complete native state. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : Native × List (Call RegistrationNativeRawAdapter.TypedSpec Native)) :
    Prod.map id (project source server) <$> (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run before =
      (simulateQ (RegistrationNativeMldsaOriginSource.handler source setup checks wire route representation created server) work).run (project source server before) := by
  classical
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [RegistrationNativeStageTrace.handler, RegistrationNativeMldsaOriginSource.handler, project,
    flagged, List.any_append, List.any_cons, List.any_nil, Bool.or_false, StateT.run, Functor.map_map, Prod.map, id_eq]

variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)

noncomputable def game (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) : ProbComp Bool := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKid
  match initialized with
  | none => pure false
  | some initial => (fun result => flagged initial.credential result.2.2) <$>
      (simulateQ (RegistrationNativeStageTrace.handler
        (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential))
        (adversary initial.public)).run (initial.state, [])

/-- Complete effectful startup and arbitrary original adaptive callbacks give exactly the original source bad-marker distribution. -/
theorem game_exact (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) :
    game (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKid =
      RegistrationNativeMldsaOriginSecurity.badGame (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKid := by
  unfold game RegistrationNativeMldsaOriginSecurity.badGame
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some initial =>
      have same := congrArg (fun distribution => (fun result => result.2.2) <$> distribution)
        (program source setup checks wire route representation initial.created initial.credential (adversary initial.public) (initial.state, []))
      simpa only [Functor.map_map, Prod.map, id_eq, project, flagged, List.any_nil] using same

/-- The unchanged full raw-adversary resource contract supplies exactly budget.create+1 ordinary generated-key targets, in every native mode and through all actual failed source prefixes. -/
theorem compiled (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (game (n := n) source setup checks wire route representation
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (RegistrationNativeMldsaOriginSecurity.collisionGame (n := n) source setup checks wire route representation
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
        ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
          ensureInit identityIndex serverKeyId)) := by
  rw [game_exact]
  exact RegistrationNativeMldsaOriginSecurity.compiled source setup checks wire route representation bounds mode adversary budget bounded ensureInit identityIndex serverKeyId

end BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal.flagged_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal.flagged_iff


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal.finish_issued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal.finish_issued

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal.game_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal.game_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal.compiled
