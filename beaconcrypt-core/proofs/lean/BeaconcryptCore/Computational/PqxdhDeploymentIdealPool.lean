-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps
import BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant
import BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget

/-!
# CE-3's compile lemma with the KEM creations reading the challenger's pool (CE-11b, unit U5, route P-a, first layer)

The ideal registration of CE-11b (`PqxdhDeploymentIdealSteps`) creates the KEM key pair of owner `j` from entry `j` of the challenger's pool (`PqxdhDeploymentIdealSteps.createPool`) instead of drawing it, and item 2's ideal world builds its router reservation from the same pool (design-v2 section 8.3, route P-a: pointwise in the pool). The prefix of the second compile lemma therefore needs CE-3's compile lemma with both creates reading the pool: on the deployment side the native handler with the pool create (`deploymentPool`), on the source14 side source14's native handler with the pool create (`revealPool`, through the registration scheduler with the pool create `handlerPool`).

- `simulateQ_congr_none` (generic): two handlers that agree on every query outside a predicate simulate a program that issues no query in the predicate identically.
- `compile_noCreate`: every deployment command other than `create` compiles to a source14 program without a create request, from CE-3's per-kind budget `PqxdhDeploymentCompileBudget.step_bound` (its cost for the create class is zero on every other command). So the pool handler agrees with source14's native handler on every compiled step but the create (`revealPool_agree`, `compiledPool_other`).
- `create_merge_pool`: the pool create commutes with CE-3's merge of the compiled program's local copies (the merge leaves the owner count unchanged); `createPool_support`: every outcome appends one fresh owner.
- `step_merge_pool`, `compile_simulation_pool`: the one-step and whole-program forms of `PqxdhDeploymentCompileStep.step_merge` and `compile_simulation` with the pool handlers.
- `good_create_pool`, `good_step_pool`: the pool create keeps CE-3's invariant `PqxdhDeploymentCompileInvariant.Good`, and so does every pool compiled step (every other command is CE-3's `good_step`).
- `compile_native_pool`: CE-COMPILE at the native level with the pool handlers (`PqxdhDeploymentCompileInvariant.compile_native` for `revealPool` and `deploymentPool`): from an initial native state, merging the compiled program's final local copies into the final source14 state of the pool source14 execution of the compiled program gives the pool deployment execution of the adversary, jointly with the adversary's output, under the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack`.

These are program equalities and invariant facts. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPool
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhLiveKemReservation (Pair)
open PqxdhDeploymentCompile (Local merge compileImpl)
open PqxdhDeploymentCompileStep (compiledImpl Inv)
open PqxdhDeploymentCompileInvariant (Good)
open PqxdhDeploymentIdealSteps (createPool)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### Generic: simulation of a program that issues no query of a kind -/

/-- Two handlers that agree on every query outside a predicate simulate a program that issues no query in the predicate identically. -/
theorem simulateQ_congr_none {ι' α : Type} {spec' : OracleSpec ι'} {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl₁ impl₂ : QueryImpl spec' m) (p : ι' → Prop) [DecidablePred p]
    (agree : ∀ query, ¬ p query → impl₁ query = impl₂ query)
    (work : OracleComp spec' α) (none : work.IsQueryBoundP p 0) :
    simulateQ impl₁ work = simulateQ impl₂ work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at none
      obtain ⟨first, rest⟩ := none
      have outside : ¬ p query := by
        rcases first with outside | impossible
        · exact outside
        · exact absurd impossible (Nat.lt_irrefl 0)
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        agree query outside]
      exact bind_congr fun reply => ih reply (by simpa only [outside, ↓reduceIte] using rest reply)

/-! ### The pool create and the pool handlers -/

section Pool
variable (setup : Setup baseSpec KemSK)

/-- The pool create commutes with CE-3's merge: merging leaves the owner count, hence the pool entry read, unchanged. -/
theorem create_merge_pool (pool : List (Pair KemSK)) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) :
    (createPool setup pool pin keyId).run (merge copies native).native =
      (fun result => (result.1, (merge copies result.2).native)) <$> (createPool setup pool pin keyId).run native := by
  have length : (merge copies native).native.owners.length = native.owners.length := by
    simp only [PqxdhDeploymentCompileRegistration.merge_native, List.length_mapIdx]
  simp only [createPool, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_get, StateT.run_set,
    StateT.run_pure, map_bind, map_pure, length]
  apply bind_congr
  intro identity
  apply bind_congr
  intro prekey
  apply bind_congr
  intro keys
  simp only [PqxdhDeploymentCompileRegistration.merge_native, List.mapIdx_concat]
  cases copies.owners native.owners.length <;> rfl

/-- Every outcome of the pool create appends one fresh owner with the given pin and key ID and returns its index. -/
theorem createPool_support (pool : List (Pair KemSK)) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationSchedule.State KemSK) (result : ℕ × PqxdhRegistrationSchedule.State KemSK)
    (member : result ∈ support ((createPool setup pool pin keyId).run state)) :
    ∃ identity prekey keys, result = (state.owners.length, { state with owners := state.owners ++
      [(⟨⟨identity, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩ : PqxdhRegistrationSchedule.Owner KemSK)] }) := by
  simp only [createPool, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_get, StateT.run_set,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨identity, -, prekey, -, keys, -, rfl⟩ := member
  exact ⟨identity, prekey, keys, rfl⟩

variable (codec : Codec Reader Response) (checks : Checks)

/-- The registration scheduler with the pool create: `PqxdhRegistrationSchedule.handler` with `create` replaced by `createPool`. -/
noncomputable def handlerPool (seed : IdentitySeed) (pool : List (Pair KemSK)) :
    QueryImpl PqxdhRegistrationSchedule.Spec (PqxdhRegistrationSchedule.Game KemSK)
  | .inr (.create pin keyId) => createPool setup pool pin keyId
  | query => PqxdhRegistrationSchedule.handler setup codec checks seed query

/-- Source14's native handler (`PqxdhRegistrationJointRevealSchedule.native`) with the pool create. -/
noncomputable def revealPool (seed : IdentitySeed) (pool : List (Pair KemSK)) :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK) (StateT (PqxdhRegistrationSchedule.State KemSK) ProbComp)
  | .inl query => handlerPool setup codec checks seed pool query
  | .inr request => PqxdhRegistrationJointRevealSchedule.native setup codec checks seed (.inr request)

/-- The native deployment handler (`PqxdhDeploymentNative.handler`) with the pool create. -/
noncomputable def deploymentPool (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (pool : List (Pair KemSK)) :
    QueryImpl PqxdhDeploymentInterface.Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp)
  | .inr (.create pin keyId) => match PqxdhDeploymentInterface.parsePin pin with
      | none => pure none
      | some word => some <$> PqxdhDeploymentNative.onNative (createPool setup pool word keyId)
  | query => PqxdhDeploymentNative.handler setup codec checks route seed query

/-- The compiled handler under the pool source14 handler: CE-3's compiler followed by `revealPool`, on the local copies and the source14 state. -/
noncomputable def compiledPool (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (pool : List (Pair KemSK)) :
    QueryImpl PqxdhDeploymentInterface.Spec (StateT (Local × PqxdhRegistrationSchedule.State KemSK) ProbComp) :=
  ((revealPool setup codec checks seed pool).mapStateTBase (compileImpl setup codec route)).flattenStateT

/-- The pool source14 handler differs from source14's native handler only on creates. -/
theorem revealPool_agree (seed : IdentitySeed) (pool : List (Pair KemSK))
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : ¬ PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = .inl 1) :
    revealPool setup codec checks seed pool query =
      PqxdhRegistrationJointRevealSchedule.native setup codec checks seed query := by
  rcases query with (coin | request) | request
  · rfl
  · cases request with
    | create pin keyId => exact absurd rfl other
    | _ => rfl
  · rfl

/-- Every deployment command other than `create` compiles to a source14 program without a create request (CE-3's per-kind budget at the create class). -/
theorem compile_noCreate (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhDeploymentInterface.Spec.Domain)
    (copies : Local) (other : PqxdhDeploymentCompileBudget.commandKind query ≠ 1) :
    ((compileImpl setup codec route query).run copies).IsQueryBoundP
      (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = .inl 1) 0 := by
  have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 1) query copies
  have zero : PqxdhDeploymentCompileBudget.cost (.inl 1) (PqxdhDeploymentCompileBudget.commandKind query) = 0 := by
    rcases query with coin | command
    · rfl
    · cases command <;> first | rfl | exact absurd rfl other
  rwa [zero] at bound

/-- Every compiled step of a command other than `create` is the same under the pool source14 handler as under source14's native handler. -/
theorem compiledPool_other (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (pool : List (Pair KemSK))
    (query : PqxdhDeploymentInterface.Spec.Domain) (other : PqxdhDeploymentCompileBudget.commandKind query ≠ 1)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (compiledPool setup codec checks route seed pool query).run (copies, native) =
      (compiledImpl setup codec checks route seed query).run (copies, native) := by
  rw [PqxdhDeploymentCompileStep.compiledImpl_run]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (revealPool setup codec checks seed pool) ((compileImpl setup codec route query).run copies)).run native = _
  rw [simulateQ_congr_none (revealPool setup codec checks seed pool)
    (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed) _ (revealPool_agree setup codec checks seed pool)
    _ (compile_noCreate setup codec route query copies other)]

/-- One step of the pool compile lemma (`PqxdhDeploymentCompileStep.step_merge` with the pool handlers): under CE-3's merge invariant, merging after the pool compiled step is the pool deployment step on the merged state. -/
theorem step_merge_pool (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (pool : List (Pair KemSK))
    (query : PqxdhDeploymentInterface.Spec.Domain) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (inv : Inv setup codec copies native) :
    Prod.map id (fun state : Local × PqxdhRegistrationSchedule.State KemSK => merge state.1 state.2) <$>
        (compiledPool setup codec checks route seed pool query).run (copies, native) =
      (deploymentPool setup codec checks route seed pool query).run (merge copies native) := by
  by_cases create : PqxdhDeploymentCompileBudget.commandKind query = 1
  · rcases query with coin | command
    · exact absurd create (by simp [PqxdhDeploymentCompileBudget.commandKind])
    · cases command with
      | create pin keyId =>
          change Prod.map id _ <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
            (simulateQ (revealPool setup codec checks seed pool)
              ((compileImpl setup codec route (.inr (.create pin keyId))).run copies)).run native) = _
          simp only [compileImpl, deploymentPool]
          cases parsed : PqxdhDeploymentInterface.parsePin pin with
          | none =>
              change Prod.map id _ <$> ((fun result => _) <$> (simulateQ (revealPool setup codec checks seed pool)
                (pure (none, copies) : OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK) _)).run native) = _
              simp only [simulateQ_pure, StateT.run_pure, map_pure]
              rfl
          | some word =>
              change Prod.map id _ <$> ((fun result => _) <$> (simulateQ (revealPool setup codec checks seed pool)
                (PqxdhDeploymentCompile.forward (.create word keyId) >>= fun index => pure (some index, _))).run native) =
                (some <$> PqxdhDeploymentNative.onNative (createPool setup pool word keyId)).run (merge copies native)
              simp only [PqxdhDeploymentCompile.forward, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map,
                Functor.map_map, PqxdhDeploymentCompileStep.onNative_run]
              change _ = (fun result => _) <$> (createPool setup pool word keyId).run (merge copies native).native
              rw [create_merge_pool, Functor.map_map]
              rfl
      | _ => exact absurd create (by simp [PqxdhDeploymentCompileBudget.commandKind])
  · rw [compiledPool_other setup codec checks route seed pool query create,
      PqxdhDeploymentCompileStep.step_merge setup codec checks route seed query copies native inv]
    rcases query with coin | command
    · rfl
    · cases command with
      | create pin keyId => exact absurd rfl create
      | _ => rfl

/-- The pool compile simulation (`PqxdhDeploymentCompileStep.compile_simulation` with both creates reading the pool): for any invariant that implies CE-3's merge invariant and is kept by every pool compiled step, merging after the pool source14 execution of the compiled program gives the pool deployment execution of the adversary. -/
theorem compile_simulation_pool {X : Type} (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (pool : List (Pair KemSK)) (good : Local → PqxdhRegistrationSchedule.State KemSK → Prop)
    (sound : ∀ copies native, good copies native → Inv setup codec copies native)
    (preserved : ∀ query copies native, good copies native →
      ∀ result ∈ support ((compiledPool setup codec checks route seed pool query).run (copies, native)),
        good result.2.1 result.2.2)
    (adversary : OracleComp PqxdhDeploymentInterface.Spec X) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (start : good copies native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
        (simulateQ (revealPool setup codec checks seed pool)
          ((simulateQ (compileImpl setup codec route) adversary).run copies)).run native =
      (simulateQ (deploymentPool setup codec checks route seed pool) adversary).run (merge copies native) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  have simulated := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (compiledPool setup codec checks route seed pool) (deploymentPool setup codec checks route seed pool)
    (fun state => good state.1 state.2) (fun state => merge state.1 state.2)
    (fun query state holds result supported => preserved query state.1 state.2 holds result supported)
    (fun query state holds => step_merge_pool setup codec checks route seed pool query state.1 state.2
      (sound state.1 state.2 holds))
    adversary (copies, native) start
  rw [← simulated]
  rfl

/-- The pool create keeps CE-3's invariant (`PqxdhDeploymentCompileInvariant.good_create` with the pool create), with the created pin and key ID appended to the local log. -/
theorem good_create_pool (pool : List (Pair KemSK)) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native)
    (result : Nat × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((createPool setup pool pin keyId).run native)) :
    Good setup codec { copies with log := { copies.log with owners := copies.log.owners ++ [(pin, keyId)] } }
      result.2 := by
  obtain ⟨identity, prekey, keys, rfl⟩ := createPool_support setup pool pin keyId native result supported
  refine ⟨good.keyId, good.installed, good.serverVisible, ?_, ?_, ?_, good.pending, good.accepts⟩
  · simp only [List.length_append, List.length_singleton, good.count]
  · intro index current copied
    obtain ⟨owner, control, associatedData, kernel, found, phase⟩ := good.copied index current copied
    have bound : index < native.owners.length := (List.getElem?_eq_some_iff.mp found).1
    exact ⟨owner, control, associatedData, kernel, by rw [List.getElem?_append_left bound]; exact found, phase⟩
  · intro index owner found
    by_cases bound : index < native.owners.length
    · rw [List.getElem?_append_left bound] at found
      exact PqxdhDeploymentCompileInvariant.ownerShape_extend codec copies.log (pin, keyId) index (good.count ▸ bound)
        owner (good.owners index owner found)
    · have last : index = native.owners.length := by
        have := (List.getElem?_eq_some_iff.mp found).1
        simp only [List.length_append, List.length_singleton] at this
        omega
      subst last
      rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at found
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      refine ⟨pin, keyId, ?_, rfl, rfl⟩
      rw [List.getElem?_append_right (good.count ▸ le_refl _), good.count, Nat.sub_self]
      rfl

/-- Every pool compiled step keeps CE-3's invariant (`PqxdhDeploymentCompileInvariant.good_step` with the pool create), under the approved codec contracts. -/
theorem good_step_pool (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (pool : List (Pair KemSK))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (query : PqxdhDeploymentInterface.Spec.Domain) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native)
    (result : PqxdhDeploymentInterface.Spec.Range query × (Local × PqxdhRegistrationSchedule.State KemSK))
    (supported : result ∈ support ((compiledPool setup codec checks route seed pool query).run (copies, native))) :
    Good setup codec result.2.1 result.2.2 := by
  by_cases create : PqxdhDeploymentCompileBudget.commandKind query = 1
  · rcases query with coin | command
    · exact absurd create (by simp [PqxdhDeploymentCompileBudget.commandKind])
    · cases command with
      | create pin keyId =>
          change result ∈ support ((fun result => (result.1.1, (result.1.2, result.2))) <$>
            (simulateQ (revealPool setup codec checks seed pool)
              ((compileImpl setup codec route (.inr (.create pin keyId))).run copies)).run native) at supported
          rw [support_map] at supported
          obtain ⟨reached, member, rfl⟩ := supported
          simp only [compileImpl] at member
          cases parsed : PqxdhDeploymentInterface.parsePin pin with
          | none =>
              simp only [parsed] at member
              change reached ∈ support ((simulateQ (revealPool setup codec checks seed pool)
                (pure (none, copies) : OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK) _)).run native) at member
              simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
              subst member
              exact good
          | some word =>
              simp only [parsed] at member
              change reached ∈ support ((simulateQ (revealPool setup codec checks seed pool)
                (PqxdhDeploymentCompile.forward (.create word keyId) >>= fun index => pure (some index, _))).run native)
                at member
              simp only [PqxdhDeploymentCompile.forward, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
                StateT.run_map, support_map, Set.mem_image] at member
              obtain ⟨created, createdMember, rfl⟩ := member
              exact good_create_pool setup codec pool word keyId copies native good created createdMember
      | _ => exact absurd create (by simp [PqxdhDeploymentCompileBudget.commandKind])
  · rw [compiledPool_other setup codec checks route seed pool query create] at supported
    exact PqxdhDeploymentCompileInvariant.good_step setup codec checks route seed phase1 phase2 query copies native good
      result supported

/-- CE-COMPILE at the native level with both creates reading the pool (`PqxdhDeploymentCompileInvariant.compile_native` for `revealPool` and `deploymentPool`), under the approved codec contracts: from a native state with the Server key ID, no installed peer, no owner and no pending registration, merging the compiled program's final local copies into the final source14 state of the pool source14 execution of the compiled program gives the pool deployment execution of the adversary from the corresponding initial deployment state, jointly with the adversary's output. -/
theorem compile_native_pool {X : Type} (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (pool : List (Pair KemSK))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (adversary : OracleComp PqxdhDeploymentInterface.Spec X) (native : PqxdhRegistrationSchedule.State KemSK)
    (keyId : native.shared.2.server.identityKeyId = setup.serverKeyId)
    (peers : ∀ kid, native.shared.2.server.server.peers kid = none) (owners : native.owners = [])
    (pending : ∀ session, native.shared.2.pending session = none) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
        (simulateQ (revealPool setup codec checks seed pool)
          (PqxdhDeploymentCompile.compile setup codec route adversary)).run native =
      (simulateQ (deploymentPool setup codec checks route seed pool) adversary).run ⟨native, 0, fun _ => 0, []⟩ := by
  rw [← PqxdhDeploymentCompile.merge_empty]
  exact compile_simulation_pool setup codec checks route seed pool (Good setup codec)
    (PqxdhDeploymentCompileInvariant.good_inv setup codec)
    (good_step_pool setup codec checks route seed pool phase1 phase2) adversary Local.empty native
    (PqxdhDeploymentCompileInvariant.good_initial setup codec native keyId peers owners pending)

end Pool

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPool

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.simulateQ_congr_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.simulateQ_congr_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.create_merge_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.create_merge_pool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.createPool_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.createPool_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.revealPool_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.revealPool_agree

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.compile_noCreate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.compile_noCreate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.compiledPool_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.compiledPool_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.step_merge_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.step_merge_pool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.compile_simulation_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.compile_simulation_pool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.good_create_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.good_create_pool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.good_step_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.good_step_pool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.compile_native_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPool.compile_native_pool
