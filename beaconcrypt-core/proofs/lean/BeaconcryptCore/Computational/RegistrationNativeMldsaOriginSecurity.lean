-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSource
import BeaconcryptCore.Computational.RegistrationNativeMldsaSecurity

/-! The complete protected unsigned-origin event is stated on literal original native credentials, startup and adaptive callbacks. Exact marker transport discharges its private-table representation before invoking the ordinary primitive EUF reduction. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaOpaque (restore)
open RegistrationNativeMldsaMap (nativeState)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
attribute [local irreducible] RegistrationNativeExperiment.handler

noncomputable def badGame (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) : ProbComp Bool := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKid
  match initialized with
  | none => pure false
  | some initial => (fun result => result.2.2) <$>
      (simulateQ (RegistrationNativeMldsaOriginSource.handler source setup checks wire route representation initial.created initial.credential)
        (adversary initial.public)).run (initial.state, false)

noncomputable def collisionGame (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) : ProbComp Bool := by
  classical
  exact do
    let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKid
    match initialized with
    | none => pure false
    | some initial => (fun result => decide (CacheHasCollision result.2.server.world.world.1.primitive.2)) <$>
        (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
          (adversary initial.public)).run initial.state

/-- The actual original initialized native marker equals the true-count private table marker distribution. -/
theorem bad_game (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) :
    badGame (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKid =
      RegistrationNativeMldsaInitializedCover.badGame (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKid := by
  unfold badGame RegistrationNativeMldsaInitializedCover.badGame
  rw [← RegistrationNativeMldsaTableStart.start source setup ensureInit identityIndex serverKid, bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro initialized supported
  cases current : initialized.1 with
  | none => simp only [current, RegistrationNativeMldsaTableStart.restored, Option.bind_none, RegistrationNativeMldsaInitializedCover.badContinued]
  | some initial =>
      have member : initial ∈ initialized.1 := by rw [current]; rfl
      obtain ⟨key, server, owners⟩ := RegistrationNativeMldsaTableStart.initialized source setup ensureInit identityIndex serverKid initialized supported initial member
      simp only [RegistrationNativeMldsaTableStart.restored, current, Option.bind_some, server.1, Option.map_some,
        RegistrationNativeMldsaMap.initial_public, RegistrationNativeMldsaInitializedCover.badContinued]
      simp only [RegistrationNativeMldsaMap.initial,
        RegistrationNativeMldsaOpaque.restore_live source key initialized.2 initial.credential key server]
      have same := congrArg (fun distribution => (fun result => result.2.2) <$> distribution)
        (RegistrationNativeMldsaOriginSource.program source setup checks wire route representation initial.created initial.credential key
          (adversary initial.public) ((initial.state, initialized.2), false) server owners)
      simpa only [Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaOriginSource.project] using same.symm

private theorem callback_program (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential (RegistrationNativeMldsaOpaque.handleSource source))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource source))
    (pool : RegistrationNativeMldsaOpaque.Pool source) :
    (simulateQ (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential) work).run (before, pool) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        RegistrationNativeMldsaTableProgram.runState source
          (simulateQ (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential) work) before pool := by
  induction work using OracleComp.inductionOn generalizing before pool with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, RegistrationNativeMldsaTableProgram.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        RegistrationNativeMldsaTableProgram.run_bind, map_bind]
      have called : (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential query).run (before, pool) =
          (fun result => (result.1.1, (result.1.2, result.2))) <$> RegistrationNativeMldsaTableProgram.runState source
            (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query) before pool := rfl
      rw [called, bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1.1 middle.1.2 middle.2

/-- The collision charge is the literal original native final shared-cache event. -/
theorem collision_game (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) :
    collisionGame (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKid =
      RegistrationNativeMldsaInitializedCover.collisionGame (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKid := by
  classical
  unfold collisionGame RegistrationNativeMldsaInitializedCover.collisionGame
  rw [← RegistrationNativeMldsaTableStart.start source setup ensureInit identityIndex serverKid, bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro initialized supported
  cases current : initialized.1 with
  | none => simp only [current, RegistrationNativeMldsaTableStart.restored, Option.bind_none, RegistrationNativeMldsaInitializedCover.collisionContinued]
  | some initial =>
      have member : initial ∈ initialized.1 := by rw [current]; rfl
      obtain ⟨key, server, owners⟩ := RegistrationNativeMldsaTableStart.initialized source setup ensureInit identityIndex serverKid initialized supported initial member
      simp only [RegistrationNativeMldsaTableStart.restored, current, Option.bind_some, server.1, Option.map_some,
        RegistrationNativeMldsaMap.initial_public, RegistrationNativeMldsaInitializedCover.collisionContinued]
      simp only [RegistrationNativeMldsaMap.initial,
        RegistrationNativeMldsaOpaque.restore_live source key initialized.2 initial.credential key server]
      have same := congrArg (fun distribution => (fun result => decide (CacheHasCollision result.2.server.world.world.1.primitive.2)) <$> distribution)
        (RegistrationNativeMldsaTableRun.program source setup checks wire route representation initial.created initial.credential key
          (adversary initial.public) initial.state initialized.2 server owners)
      have callback := callback_program source setup checks wire route representation initial.created initial.credential
        (adversary initial.public) initial.state initialized.2
      rw [callback]
      simpa only [Functor.map_map, RegistrationNativeMldsaTableRestore.observe, nativeState] using same.symm

/-- The actual initialized protected native event has one final-cache collision charge and one ordinary primitive EUF advantage per permitted generation attempt. -/
theorem typed (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (badGame (n := n) source setup checks wire route representation adversary
      ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (collisionGame (n := n) source setup checks wire route representation adversary
        ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (cap + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId)) := by
  rw [bad_game, collision_game]
  exact RegistrationNativeMldsaSecurity.typed source setup checks wire route representation adversary cap bounded ensureInit identityIndex serverKeyId

/-- The unchanged full raw-adversary resource contract supplies exactly budget.create+1 ordinary generated-key targets, in every native mode and through all actual failed source prefixes. -/
theorem compiled (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (badGame (n := n) source setup checks wire route representation
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (collisionGame (n := n) source setup checks wire route representation
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
        ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
          ensureInit identityIndex serverKeyId)) := by
  rw [bad_game, collision_game]
  exact RegistrationNativeMldsaSecurity.compiled source setup checks wire route representation bounds mode adversary budget bounded ensureInit identityIndex serverKeyId

end BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity.bad_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity.bad_game

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity.collision_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity.collision_game

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSecurity.compiled
