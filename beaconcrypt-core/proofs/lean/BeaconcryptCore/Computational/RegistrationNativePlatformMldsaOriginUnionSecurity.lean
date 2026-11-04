-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginSource
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRun

/-! The joint corrected protected unsigned-origin failure or final shared-cache collision event is stated on literal original native credentials, startup and adaptive source callbacks with their common external platform state. Exact marker transport discharges its private-table representation before invoking the ordinary primitive EUF reduction. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginUnionSecurity
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaOpaque (restore)
open RegistrationNativeMldsaMap (nativeState)
variable {n : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
variable (previous : Platform)
attribute [local irreducible] RegistrationNativePlatformExperiment.handler

noncomputable def badGame (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) : ProbComp Bool := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKid
  match initialized with
  | none => pure false
  | some initial => (fun result => @decide (result.2.2 = true ∨ CacheHasCollision result.2.1.1.server.world.world.1.primitive.2) (Classical.propDecidable _)) <$>
      (simulateQ (RegistrationNativePlatformMldsaOriginSource.handler source setup checks wire route representation initial.created view failure allocation reserveRegistration reservePeer erased helper writer initial.credential)
        (adversary initial.public)).run ((initial.state, previous), false)

noncomputable def collisionGame (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) : ProbComp Bool := by
  classical
  exact do
    let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKid
    match initialized with
    | none => pure false
    | some initial => (fun result => decide (CacheHasCollision result.1.2.server.world.world.1.primitive.2)) <$>
        ((simulateQ (RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation initial.created source initial.credential
          view failure allocation reserveRegistration reservePeer erased helper writer) (adversary initial.public)).run initial.state).run previous

/-- The actual original initialized native marker equals the true-count private table marker distribution. -/
theorem bad_game (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) :
    badGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKid =
      RegistrationNativePlatformMldsaInitializedUnion.badGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKid := by
  unfold badGame RegistrationNativePlatformMldsaInitializedUnion.badGame
  rw [← RegistrationNativeMldsaTableStart.start source setup ensureInit identityIndex serverKid, bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro initialized supported
  cases current : initialized.1 with
  | none => simp only [current, RegistrationNativeMldsaTableStart.restored, Option.bind_none, RegistrationNativePlatformMldsaInitializedUnion.badContinued]
  | some initial =>
      have member : initial ∈ initialized.1 := by rw [current]; rfl
      obtain ⟨key, server, owners⟩ := RegistrationNativeMldsaTableStart.initialized source setup ensureInit identityIndex serverKid initialized supported initial member
      simp only [RegistrationNativeMldsaTableStart.restored, current, Option.bind_some, server.1, Option.map_some,
        RegistrationNativeMldsaMap.initial_public, RegistrationNativePlatformMldsaInitializedUnion.badContinued]
      simp only [RegistrationNativeMldsaMap.initial,
        RegistrationNativeMldsaOpaque.restore_live source key initialized.2 initial.credential key server]
      have same := congrArg (fun distribution => (fun result => @decide (result.2.2 = true ∨ CacheHasCollision result.2.1.1.server.world.world.1.primitive.2) (Classical.propDecidable _)) <$> distribution)
        (RegistrationNativePlatformMldsaOriginSource.program source setup checks wire route representation initial.created view failure allocation reserveRegistration reservePeer erased helper writer initial.credential key
          (adversary initial.public) (((initial.state, previous), initialized.2), false) server owners)
      simpa only [Functor.map_map, Prod.map, id_eq, RegistrationNativePlatformMldsaOriginSource.project, nativeState] using same.symm

private theorem callback_program (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential (RegistrationNativeMldsaOpaque.handleSource source))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource source))
    (initialP : Platform) (pool : RegistrationNativeMldsaOpaque.Pool source) :
    (simulateQ (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run ((before, initialP), pool) =
      RegistrationNativePlatformMldsaTableCallback.arrange source <$>
        RegistrationNativePlatformMldsaTableProgram.runState source
          (simulateQ (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work) before initialP pool := by
  induction work using OracleComp.inductionOn generalizing before initialP pool with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, RegistrationNativePlatformMldsaTableProgram.run_pure, map_pure]
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        RegistrationNativePlatformMldsaTableProgram.run_bind, map_bind]
      have called : (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run ((before, initialP), pool) =
          RegistrationNativePlatformMldsaTableCallback.arrange source <$> RegistrationNativePlatformMldsaTableProgram.runState source
            (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query) before initialP pool := rfl
      rw [called, bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1.1.1 middle.1.1.2 middle.1.2 middle.2

/-- The collision charge is the literal original native final shared-cache event. -/
theorem collision_game (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) :
    collisionGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKid =
      RegistrationNativePlatformMldsaInitializedUnion.collisionGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKid := by
  classical
  unfold collisionGame RegistrationNativePlatformMldsaInitializedUnion.collisionGame
  rw [← RegistrationNativeMldsaTableStart.start source setup ensureInit identityIndex serverKid, bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro initialized supported
  cases current : initialized.1 with
  | none => simp only [current, RegistrationNativeMldsaTableStart.restored, Option.bind_none, RegistrationNativePlatformMldsaInitializedUnion.collisionContinued]
  | some initial =>
      have member : initial ∈ initialized.1 := by rw [current]; rfl
      obtain ⟨key, server, owners⟩ := RegistrationNativeMldsaTableStart.initialized source setup ensureInit identityIndex serverKid initialized supported initial member
      simp only [RegistrationNativeMldsaTableStart.restored, current, Option.bind_some, server.1, Option.map_some,
        RegistrationNativeMldsaMap.initial_public, RegistrationNativePlatformMldsaInitializedUnion.collisionContinued]
      simp only [RegistrationNativeMldsaMap.initial,
        RegistrationNativeMldsaOpaque.restore_live source key initialized.2 initial.credential key server]
      have same := congrArg (fun distribution => (fun result => decide (CacheHasCollision result.1.2.server.world.world.1.primitive.2)) <$> distribution)
        (RegistrationNativePlatformMldsaTableRun.program source setup checks wire route representation initial.created initial.credential key
          view failure allocation reserveRegistration reservePeer erased helper writer (adversary initial.public) initial.state previous initialized.2 server owners)
      have callback := callback_program source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer initial.created initial.credential
        (adversary initial.public) initial.state previous initialized.2
      rw [callback]
      simpa only [Functor.map_map, RegistrationNativePlatformMldsaTableRestore.observe, RegistrationNativePlatformMldsaTableCallback.arrange, nativeState] using same.symm

/-- The actual initialized protected native event has one final-cache collision charge and one ordinary primitive EUF advantage per permitted generation attempt. -/
theorem typed (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (badGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous
      ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (collisionGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous
        ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (cap + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKeyId)) := by
  rw [bad_game, collision_game]
  exact RegistrationNativePlatformMldsaUnionSecurity.typed source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer previous adversary cap bounded ensureInit identityIndex serverKeyId

/-- The unchanged full raw-adversary resource contract supplies exactly budget.create+1 ordinary generated-key targets, in every native mode and through all actual failed source prefixes. -/
theorem compiled (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (badGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      previous ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (collisionGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
        previous ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId)) := by
  rw [bad_game, collision_game]
  exact RegistrationNativePlatformMldsaUnionSecurity.compiled source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer previous bounds mode adversary budget bounded ensureInit identityIndex serverKeyId

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginUnionSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginUnionSecurity.bad_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginUnionSecurity.bad_game

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginUnionSecurity.collision_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginUnionSecurity.collision_game

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginUnionSecurity.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginUnionSecurity.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginUnionSecurity.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginUnionSecurity.compiled
