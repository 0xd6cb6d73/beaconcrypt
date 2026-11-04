-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks

/-! Actual native ML generation appends a private real-key row before the unchanged source creation suffix. Dynamic restoration preserves every old live handle and maps only the freshly generated opaque credential to its actual source key. Both failed generation and later failed creation prefixes retain their literal state and draw count. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore birth)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaPoolMap (CredentialLive StateLive)
open RegistrationNativeMldsaTableProgram (evaluate runState)
open RegistrationNativeMldsaTableRestore (observe)
variable {n : Nat} {ι KemSK Value Other : Type} {base : OracleSpec ι}
variable (source : Source)

def setWorld {ml : Source} (before : RegistrationNativeExperiment.State n KemSK ml) (world : PqxdhRecordLiftWorld.State n) :
    RegistrationNativeExperiment.State n KemSK ml :=
  { before with server := { before.server with world := { before.server.world with world := (world, before.server.world.world.2) } } }

def advance {ml : Source} (before : RegistrationNativeExperiment.State n KemSK ml) (count : Nat) :
    RegistrationNativeExperiment.State n KemSK ml :=
  setWorld before (RegistrationNativeMldsaCapability.advance .environment before.server.world.world.1 count)

private theorem evaluate_map (observer : Value → Other)
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (pool : Pool source) :
    evaluate source (observer <$> work) pool = Prod.map observer id <$> evaluate source work pool := by
  simp only [evaluate, simulateQ_map, StateT.run_map]
  rfl

/-- The actual generation callback updates the original native World and its private pool with the same source draw receipt. -/
theorem world_generate (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (pool : Pool source) :
    runState source (RegistrationNativeMldsaCreation.world (RegistrationNativeMldsaProgram.call .environment .generate)) before pool =
      (fun generated => let born := birth source pool generated
        ((born.1.1, advance before born.1.2), born.2)) <$>
        RegistrationNativeMldsaCapability.actual source .generate := by
  change evaluate source
    ((fun result => (result.1, setWorld before result.2)) <$>
      (RegistrationNativeMldsaProgram.call .environment .generate).run before.server.world.world.1) pool = _
  rw [evaluate_map]
  change (Prod.map (fun result => (result.1, setWorld before result.2)) id <$>
    runState source (RegistrationNativeMldsaProgram.call .environment .generate) before.server.world.world.1 pool) = _
  rw [RegistrationNativeMldsaTableProgram.generate_source]
  simp only [Functor.map_map]
  rfl

private theorem real_world_generate (before : RegistrationNativeExperiment.State n KemSK source) :
    RegistrationNativeMldsaProgram.evaluate
      ((RegistrationNativeMldsaCreation.world (RegistrationNativeMldsaProgram.call .environment .generate)).run before) =
      (fun generated => (generated.1, advance before generated.2)) <$>
        RegistrationNativeMldsaCapability.actual source .generate := by
  simp only [RegistrationNativeMldsaProgram.evaluate, RegistrationNativeMldsaCreation.world, StateT.run,
    RegistrationNativeMldsaProgram.call, simulateQ_map,
    simulateQ_spec_query, RegistrationNativeMldsaProgram.actual, bind_pure_comp, Functor.map_map]
  rfl

private theorem restore_advance (fallback : Credential source) (pool : Pool source)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (count : Nat) :
    nativeState (restore source fallback pool) (advance before count) =
      advance (nativeState (restore source fallback pool) before) count := rfl

private theorem birth_option (fallback : Credential source) (pool : Pool source) (generated : Option (Credential source) × Nat) :
    (birth source pool generated).1.1.map
      (RegistrationNativeMldsaMap.credential (restore source fallback (birth source pool generated).2)) = generated.1 := by
  rcases generated with ⟨generated, count⟩
  cases generated with
  | none => rfl
  | some credential =>
      simp only [birth, Option.map_some]
      exact congrArg some (RegistrationNativeMldsaOpaque.restore_live source fallback _ _ credential
        (RegistrationNativeMldsaOpaque.birth_live source pool credential count))

/-- A real generated key restores the complete actual creation suffix at the extended private table. -/
theorem restored (fallback : Credential source) (pool : Pool source)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (live : StateLive source pool before) :
    observe source fallback <$> runState source
      (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId) before pool =
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run
          (nativeState (restore source fallback pool) before) := by
  have target := congrFun (RegistrationNativeMldsaCreation.eval_create (n := n) (source := source)
    setup checks representation created edPin mlPin keyId) (nativeState (restore source fallback pool) before)
  simp only [StateT.run]
  rw [← target]
  simp only [RegistrationNativeMldsaProgram.evalState]
  simp only [RegistrationNativeMldsaCreation.create, RegistrationNativeMldsaTableProgram.run_bind,
    map_bind, world_generate, bind_map_left]
  simp only [RegistrationNativeMldsaProgram.evaluate, StateT.run_bind, simulateQ_bind]
  rw [← RegistrationNativeMldsaProgram.evaluate, real_world_generate]
  simp only [bind_map_left]
  apply bind_congr
  intro generated
  rw [RegistrationNativeMldsaTableProgram.run_liftState]
  simp only [Functor.map_map, observe]
  have suffix := RegistrationNativeMldsaGlobalMap.createSuffix_natural
    (restore source fallback (birth source pool generated).2) setup checks representation created
      edPin mlPin keyId (birth source pool generated).1.1 (advance before (birth source pool generated).1.2)
  rw [birth_option source fallback pool generated] at suffix
  have stable := RegistrationNativeMldsaPoolMap.birth_state_restore source fallback pool generated before live
  have count : (birth source pool generated).1.2 = generated.2 := by
    rcases generated with ⟨generated, count⟩
    cases generated <;> rfl
  rw [restore_advance, stable, count] at suffix
  rw [← RegistrationNativeMldsaProgram.evaluate, count]
  have ordinary := RegistrationNativeMldsaProgram.evaluate_lift (source := source)
    ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeMldsaCreation.createSuffix setup edPin mlPin keyId generated.1)).run
        (advance (nativeState (restore source fallback pool) before) generated.2))
  exact suffix.trans ordinary.symm

/-- Each supported creation execution contains its actual source generation draw and the full same-run ordinary suffix. -/
theorem reached (pool : Pool source) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (result : (RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId) before pool)) :
    ∃ generated : Option (Credential source) × Nat,
      generated ∈ support (RegistrationNativeMldsaCapability.actual source .generate) ∧
      result.2 = (birth source pool generated).2 ∧
      result.1 ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeMldsaCreation.createSuffix setup edPin mlPin keyId (birth source pool generated).1.1)).run
          (advance before (birth source pool generated).1.2)) := by
  simp only [RegistrationNativeMldsaCreation.create, RegistrationNativeMldsaTableProgram.run_bind,
    world_generate, mem_support_bind_iff] at supported
  obtain ⟨middle, drawn, continued⟩ := supported
  rw [support_map] at drawn
  obtain ⟨generated, actual, same⟩ := drawn
  cases same
  rw [RegistrationNativeMldsaTableProgram.run_liftState, support_map] at continued
  obtain ⟨answer, possible, same⟩ := continued
  have rows : result.2 = (birth source pool generated).2 := (congrArg Prod.snd same).symm
  have value : result.1 = answer := (congrArg Prod.fst same).symm
  exact ⟨generated, actual, rows, value.symm ▸ possible⟩

private theorem birth_fresh (pool : Pool source) (generated : Option (Credential source) × Nat)
    (credential : Credential (handleSource source)) (member : credential ∈ (birth source pool generated).1.1) :
    CredentialLive source (birth source pool generated).2 credential := by
  rcases generated with ⟨generated, count⟩
  cases generated with
  | none => simp only [birth, Option.not_mem_none] at member
  | some key =>
      have same : (⟨key.publicKey, pool.keys.length⟩ : Credential (handleSource source)) = credential := by simpa only [birth, Option.mem_some_iff] using member
      subst credential
      exact ⟨key, RegistrationNativeMldsaOpaque.birth_live source pool key count⟩

/-- Successful and failed actual creation prefixes preserve reached owned handles in the extended private table. -/
theorem live (pool : Pool source) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (old : StateLive source pool before)
    (result : (RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId) before pool)) :
    StateLive source result.2 result.1.2 := by
  obtain ⟨generated, _drawn, rows, suffix⟩ := reached source pool setup checks representation created
    edPin mlPin keyId before result supported
  rw [rows]
  exact RegistrationNativeMldsaLiveOwners.source_createSuffix source setup checks representation created
    (birth source pool generated).2 edPin mlPin keyId (birth source pool generated).1.1
    (birth_fresh source pool generated) (advance before (birth source pool generated).1.2) result.1
    (RegistrationNativeMldsaPoolMap.birth_owners source pool generated before.beacons old) suffix

/-- Dynamic creation leaves every previously owned credential attached to its same actual real key. -/
theorem key_live (pool : Pool source) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (handle : Credential (handleSource source)) (key : Credential source)
    (old : RegistrationNativeMldsaOpaque.Live source pool handle key)
    (result : (RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId) before pool)) :
    RegistrationNativeMldsaOpaque.Live source result.2 handle key := by
  obtain ⟨generated, _drawn, rows, _suffix⟩ := reached source pool setup checks representation created
    edPin mlPin keyId before result supported
  rw [rows]
  exact RegistrationNativeMldsaOpaque.birth_preserves source pool generated handle key old

end BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.world_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.world_generate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.restored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.reached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.key_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.key_live
