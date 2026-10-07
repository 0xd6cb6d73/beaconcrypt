-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget
import BeaconcryptCore.Computational.PqxdhDeploymentSecrecy

/-! CE-COMPILE and budget transport for the complete common deployment experiment (CE-3 remainder). The compiled program of a complete-interface adversary in either observation mode is the trial compiler applied to the wrapped adversary, which runs the secrecy layer itself: it records the transcript, draws the hidden bit and the fresh messages with its own coins exactly when the experiment does, and issues each admitted test or fresh message as one native send. Because the draws happen at the same position in both runs, no sampling swap is needed. `compile_full_game` and `compile_full_source` state that the complete experiment equals the merged initialized execution of the compiled program, jointly over the Server's public data, the adversary's output, the whole ledger (transcript, test session and fresh messages), the whole deployment state including the produced frames, and the runtime state, under exactly the two codec contracts of the trial. The budget transport counts one experiment coin per test and one per fresh byte, so the coin cap grows by the tests plus the fresh-message byte budget `bounds.max * qFresh`; every test and fresh message is one Server or Beacon send. The compiled program issues no identity, KEM, prekey or one-time read. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentCompile (Local merge compile)
open PqxdhDeploymentRecordCache (SourceSpec)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl wrap)
open PqxdhDeploymentCompileBudget (commandKind cost unit)
open PqxdhDeploymentInterface (FullSpec FullSuccessSpec ModeSpec Mode Budget FreshBounds queryClass asModeO observeFull)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The compiled source14 program of a complete-interface adversary in a mode: the trial compiler applied to the wrapped adversary. -/
noncomputable def compileFull (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) : OracleComp (SourceSpec KemSK) ((X × Ledger) × Local) :=
  compile setup codec route (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))

/-- The merged outcome of the compiled program of a complete-interface adversary. -/
def mergeFull (outcome : Option (PqxdhRegistrationJointInitializedSchedule.NativeOutcome KemSK ((X × Ledger) × Local)) × A) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A :=
  (outcome.1.map fun result => (result.1, result.2.1.1.1, (result.2.1.1.2, merge result.2.1.2 result.2.2)), outcome.2)

/-- Theorem CE-COMPILE for the complete experiment: under the approved Phase 1 and Phase 2 read-back contracts, the common deployment experiment in either mode, with a generated Server seed, is exactly the initialized source14 native execution of the compiled program with the merged final state, jointly over the constructed Server's public data, the adversary's output, the ledger, the complete deployment state and the runtime state. -/
theorem compile_full_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    mergeFull <$> (PqxdhRegistrationJointInitializedSchedule.native setup codec checks ensureInit identityIndex none
        (compileFull setup codec route bounds mode adversary)).run runtime =
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run
        runtime := by
  rw [PqxdhDeploymentSecrecy.game_wrap, ← PqxdhDeploymentCompileGame.compile_game setup codec checks route ensureInit
    identityIndex phase1 phase2, Functor.map_map]
  apply congrArg (fun f => f <$> _)
  funext outcome
  simp only [mergeFull, PqxdhDeploymentCompileGame.mergeOutcome, Option.map_map]
  rfl

/-- CE-COMPILE for the complete experiment at the level of the initialized source14 execution used by the KEM and root theorems. -/
theorem compile_full_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => mergeFull (result.1.map PqxdhRegistrationJointInitializedSchedule.eraseOutcome, result.2.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
          (compileFull setup codec route bounds mode adversary)).run state =
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit state.1.1.seeds.length bounds mode adversary).run
        state.2 := by
  rw [← compile_full_game setup codec checks route ensureInit state.1.1.seeds.length phase1 phase2 bounds mode
    adversary state.2, ← PqxdhRegistrationJointInitializedSchedule.initialized_native setup codec checks ensureInit none
      (compileFull setup codec route bounds mode adversary) state, Functor.map_map]

/-- Native command classes issued by one complete-interface query of each class: a coin or command issues itself; a test issues at most one coin and one send; a fresh message issues at most `bounds.max` coins and one send. -/
def wrapCost (bounds : FreshBounds) (core : Fin 12) (full : Fin 14) : Nat :=
  if full.val < 12 then (if core.val = full.val then 1 else 0)
  else if full.val = 12 then (if core.val = 0 ∨ core.val = 8 ∨ core.val = 10 then 1 else 0)
  else if core.val = 0 then bounds.max
  else if core.val = 8 ∨ core.val = 10 then 1 else 0

/-- The class of a forwarded coin or command is its native class. -/
theorem queryClass_inl (query : PqxdhDeploymentInterface.Spec.Domain) :
    (queryClass (.inl query)).val = (commandKind query).val := by
  rcases query with coin | command
  · rfl
  · cases command <;> rfl

/-- A uniform message of `length` bytes costs `length` native coins and nothing else. -/
theorem uniformBytes_bound (core : Fin 12) (length : Nat) :
    (PqxdhDeploymentSecrecy.uniformBytes length).IsQueryBoundP (fun query => commandKind query = core)
      (if core.val = 0 then length else 0) := by
  induction length with
  | zero => trivial
  | succ length ih =>
      unfold PqxdhDeploymentSecrecy.uniformBytes
      have first : (PqxdhDeploymentSecrecy.coin 255).IsQueryBoundP (fun query => commandKind query = core)
          (if core.val = 0 then 1 else 0) := by
        unfold PqxdhDeploymentSecrecy.coin
        rw [isQueryBoundP_query_iff]
        intro hit
        have zero : core.val = 0 := by rw [← hit]; rfl
        simp [zero]
      refine IsQueryBoundP.mono (isQueryBoundP_bind (m := (if core.val = 0 then length else 0) + 0) first
        fun _ _ => isQueryBoundP_bind (m := 0) ih fun _ _ => ?_) ?_
      · trivial
      · split <;> omega

/-- The hidden bit costs one native coin and nothing else. -/
theorem drawBit_bound (core : Fin 12) :
    PqxdhDeploymentSecrecy.drawBit.IsQueryBoundP (fun query => commandKind query = core)
      (if core.val = 0 then 1 else 0) := by
  unfold PqxdhDeploymentSecrecy.drawBit PqxdhDeploymentSecrecy.coin
  rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro hit
  have zero : core.val = 0 := by rw [← hit]; rfl
  simp [zero]

/-- A send on a handle costs one Server or one Beacon send and nothing else. -/
theorem send_bound (core : Fin 12) (handle : PqxdhDeploymentInterface.Handle) (plaintext : Pqxdh.Bytes) :
    (PqxdhDeploymentSecrecy.send handle plaintext).IsQueryBoundP (fun query => commandKind query = core)
      (if core.val = 8 ∨ core.val = 10 then 1 else 0) := by
  cases handle with
  | peer keyId =>
      unfold PqxdhDeploymentSecrecy.send
      rw [isQueryBoundP_query_iff]
      intro hit
      have eight : core.val = 8 := by rw [← hit]; rfl
      simp [eight]
  | owner index =>
      unfold PqxdhDeploymentSecrecy.send
      rw [isQueryBoundP_query_iff]
      intro hit
      have ten : core.val = 10 := by rw [← hit]; rfl
      simp [ten]

/-- Every query of the secrecy layer issues at most its class's native commands of each class. -/
theorem wrap_step (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (core : Fin 12) (query : PqxdhDeploymentInterface.Query) (ledger : Ledger) :
    ((ledgerImpl crypto codec serverKid bounds query).run ledger).IsQueryBoundP (fun request => commandKind request = core)
      (wrapCost bounds core (queryClass query)) := by
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro hit
    simp [wrapCost, queryClass_inl, hit]
  · have pureBound : ∀ (value : Option RawCtxSourceSend.Encrypted × Ledger) (bound : Nat),
        (pure value : OracleComp PqxdhDeploymentInterface.Spec _).IsQueryBoundP
          (fun request => commandKind request = core) bound := fun _ _ => trivial
    rcases secrecy with ⟨handle, left, right⟩ | ⟨handle, length⟩
    · have cap : (if core.val = 0 then 1 else 0) + ((if core.val = 8 ∨ core.val = 10 then 1 else 0) + 0) ≤
          wrapCost bounds core (queryClass (.inr (.test handle left right))) := by
        simp only [wrapCost, queryClass]
        split_ifs <;> omega
      simp only [ledgerImpl, StateT.run]
      split
      · split
        · exact IsQueryBoundP.mono (isQueryBoundP_bind (drawBit_bound core) fun _ _ =>
            isQueryBoundP_bind (send_bound core handle _) fun _ _ => pureBound _ 0) cap
        · split
          · exact IsQueryBoundP.mono (isQueryBoundP_bind (send_bound core handle _) fun _ _ => pureBound _ 0)
              (le_trans (by omega) cap)
          · exact pureBound _ _
      · exact pureBound _ _
    · simp only [ledgerImpl, StateT.run]
      split
      · rename_i admitted
        have cap : (if core.val = 0 then length else 0) + ((if core.val = 8 ∨ core.val = 10 then 1 else 0) + 0) ≤
            wrapCost bounds core (queryClass (.inr (.fresh handle length))) := by
          simp only [wrapCost, queryClass]
          split_ifs <;> omega
        exact IsQueryBoundP.mono (isQueryBoundP_bind (uniformBytes_bound core length) fun _ _ =>
          isQueryBoundP_bind (send_bound core handle _) fun _ _ => pureBound _ 0) cap
      · exact pureBound _ _

/-- A mode P adversary run behind `observeFull` makes exactly its own queries, class for class. -/
theorem observe_bound (adversary : OracleComp FullSuccessSpec X) (kind : Fin 14) (bound : Nat)
    (bounded : adversary.IsQueryBoundP (fun query => queryClass query = kind) bound) :
    (simulateQ observeFull adversary).IsQueryBoundP (fun query => queryClass query = kind) bound := by
  induction adversary using OracleComp.inductionOn generalizing bound with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        PqxdhDeploymentSecrecy.observeFull_project, bind_map_left]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨allowed, fun reply => ih _ _ (rest _)⟩

/-- Budgets of either mode carry over to the mode O form of the adversary. -/
theorem asModeO_bound (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (kind : Fin 14) :
    (asModeO mode adversary).IsQueryBoundP (fun query => queryClass query = kind) (budget.cap kind) := by
  cases mode with
  | O => exact respects kind
  | P => exact observe_bound adversary kind (budget.cap kind) (respects kind)

/-- Budget transport through the secrecy layer: the wrapped adversary makes at most `∑ full, wrapCost bounds core full * budget.cap full` native commands of each native class `core`. -/
theorem wrap_bound (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (core : Fin 12) :
    (wrap crypto codec serverKid bounds (asModeO mode adversary)).IsQueryBoundP (fun request => commandKind request = core)
      (∑ full, wrapCost bounds core full * budget.cap full) :=
  FinitePartitionQueryBounds.weighted_bound queryClass (wrapCost bounds core) budget.cap
    (ledgerImpl crypto codec serverKid bounds) (fun request => commandKind request = core) (asModeO mode adversary)
    (asModeO_bound mode adversary budget respects)
    (fun query ledger => wrap_step crypto codec serverKid bounds core query ledger)
    Ledger.empty

/-- Budget transport to source14: the compiled program of a complete-interface adversary that respects `budget` makes at most `∑ core, cost kind core * ∑ full, wrapCost bounds core full * budget.cap full` source14 queries of each kind. This is the `certified` premise of the KEM and root theorems for the compiled program. -/
theorem compile_full_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (kind : SourceKind) :
    (compileFull setup codec route bounds mode adversary).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind)
      (∑ core, cost kind core * ∑ full, wrapCost bounds core full * budget.cap full) :=
  PqxdhDeploymentCompileBudget.compile_bound setup codec route _ _
    (fun core => wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode adversary budget respects core) kind

/-- The compiled program issues no identity, KEM, prekey or one-time field read. -/
theorem compile_full_no_secret_read (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (field : Fin 5) (notKernel : field ≠ 4) :
    (compileFull setup codec route bounds mode adversary).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inr field) 0 := by
  have bound := compile_full_bound setup codec route bounds mode adversary budget respects (.inr field)
  have zero : ∀ core, cost (.inr field) core = 0 := by
    intro core
    fin_cases core <;> simp [cost, unit, notKernel]
  simpa [zero] using bound

end BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.compile_full_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.compile_full_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.compile_full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.compile_full_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.queryClass_inl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.queryClass_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.uniformBytes_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.uniformBytes_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.drawBit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.drawBit_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.send_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.send_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.wrap_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.wrap_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.observe_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.observe_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.asModeO_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.asModeO_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.wrap_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.wrap_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.compile_full_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.compile_full_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.compile_full_no_secret_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy.compile_full_no_secret_read
