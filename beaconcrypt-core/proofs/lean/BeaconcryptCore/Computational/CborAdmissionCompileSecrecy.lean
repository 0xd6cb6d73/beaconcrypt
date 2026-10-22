-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy
import BeaconcryptCore.Computational.CborAdmissionCompileBudget
import BeaconcryptCore.Computational.CborAdmissionCompileGame
import BeaconcryptCore.Computational.PqxdhDeploymentSecrecy

/-! Complete-interface operational simulation for the fixed-codec admission experiment. The existing secrecy ledger runs above the admission compiler, so hidden-bit and fresh-message draws keep their original positions. The equality retains the entire ledger and deployment state; its interpretation under the physical raw CBOR client remains a separate representation obligation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionCompileSecrecy
open PqxdhServerAuthExperiment PqxdhJointIdentity
open CborAdmissionCompiler (Local merge compile)
open PqxdhDeploymentRecordCache (SourceSpec)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl wrap)
open PqxdhDeploymentCompileBudget (commandKind cost unit)
open PqxdhDeploymentCompileSecrecy (wrapCost)
open PqxdhDeploymentInterface (FullSpec FullSuccessSpec ModeSpec Mode Budget FreshBounds queryClass asModeO observeFull)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The unchanged secrecy ledger above the native size-admission handler. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (PqxdhDeploymentSecrecy.State KemSK) ProbComp) :=
  ((CborAdmissionCompiler.nativeHandler setup codec checks route seed).mapStateTBase
    (ledgerImpl setup.source.crypto codec setup.serverKeyId bounds)).flattenStateT

/-- The complete fixed-codec experiment with size admission and a generated Server. -/
noncomputable def game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.State KemSK)) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
      (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
        (simulateQ (handler setup codec checks route created.seed bounds) (asModeO mode adversary)).run
          (Ledger.empty, PqxdhDeploymentNative.initial created)

/-- Ledger flattening retains every draw, query, reply and final ledger. -/
theorem run_wrap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (bounds : FreshBounds)
    (adversary : OracleComp FullSpec X) (state : PqxdhDeploymentNative.State KemSK) :
    (simulateQ (handler setup codec checks route seed bounds) adversary).run (Ledger.empty, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (CborAdmissionCompiler.nativeHandler setup codec checks route seed)
          (wrap setup.source.crypto codec setup.serverKeyId bounds adversary)).run state := by
  rw [wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  simp only [handler]
  exact (id_map _).symm

/-- Initialized ledger execution is the wrapped admission game, jointly with all states. -/
theorem game_wrap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    (game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime =
      (fun outcome => (outcome.1.map fun result => (result.1, result.2.1.1, (result.2.1.2, result.2.2)), outcome.2)) <$>
        (CborAdmissionCompileGame.game setup codec checks route ensureInit identityIndex
          (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))).run runtime := by
  simp only [game, CborAdmissionCompileGame.game, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp only [map_pure, Option.map_none]
  · have wrapped := run_wrap setup codec checks route created.seed bounds (asModeO mode adversary)
      (PqxdhDeploymentNative.initial created)
    simp only [StateT.run] at wrapped
    simp only [wrapped, Functor.map_map, Option.map_some]

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
      (game setup codec checks route ensureInit identityIndex bounds mode adversary).run
        runtime := by
  rw [game_wrap, ← CborAdmissionCompileGame.compile_game setup codec checks route ensureInit
    identityIndex phase1 phase2, Functor.map_map]
  apply congrArg (fun f => f <$> _)
  funext outcome
  simp only [mergeFull, CborAdmissionCompileGame.mergeOutcome, Option.map_map]
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
      (game setup codec checks route ensureInit state.1.1.seeds.length bounds mode adversary).run
        state.2 := by
  rw [← compile_full_game setup codec checks route ensureInit state.1.1.seeds.length phase1 phase2 bounds mode
    adversary state.2, ← PqxdhRegistrationJointInitializedSchedule.initialized_native setup codec checks ensureInit none
      (compileFull setup codec route bounds mode adversary) state, Functor.map_map]

/-- Budget transport to source14: the compiled program of a complete-interface adversary that respects `budget` makes at most `∑ core, cost kind core * ∑ full, wrapCost bounds core full * budget.cap full` source14 queries of each kind. This is the `certified` premise of the KEM and root theorems for the compiled program. -/
theorem compile_full_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (kind : SourceKind) :
    (compileFull setup codec route bounds mode adversary).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind)
      (∑ core, cost kind core * ∑ full, wrapCost bounds core full * budget.cap full) :=
  CborAdmissionCompileBudget.compile_bound setup codec route _ _
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode adversary budget respects core) kind

/-- The compiled program of every complete-interface adversary, in either mode, issues no identity, KEM, prekey or one-time field read; unlike `compile_full_no_secret_read`, no budget is assumed. -/
theorem compile_full_unread (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (field : Fin 5) (notKernel : field ≠ 4) :
    (compileFull setup codec route bounds mode adversary).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inr field) 0 :=
  CborAdmissionCompileBudget.compile_unread setup codec route _ field notKernel

end BeaconcryptCore.Computational.CborAdmissionCompileSecrecy

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.run_wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.run_wrap

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.game_wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.game_wrap

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.compile_full_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.compile_full_game

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.compile_full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.compile_full_source

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.compile_full_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.compile_full_bound

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.compile_full_unread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileSecrecy.compile_full_unread
