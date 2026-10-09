-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost

/-!
# The frames, C4 and F4 of the ideal environment (CE-11b, unit U3 remainder)

The parts of CE-11b unit U3 (design-v2 sections 5.2 and 6.3) that `PqxdhDeploymentIdealEnv` left open:

- C2a: `frame_ideal`, the frame of the ideal environment at fixed parameters (`envG`) with startup bound `qInit + 32`, and `frame_idealD`, the frame of the ideal environment of a target (`envGD`, the challenger's parameters drawn at startup) with startup bound `qInit + 32 + (count + 1) * keygenCost + encapsCost` (plan section 48, A2). Both use the first-touch allowance `allowanceG (baseAllowance caps) ceFirstTouch` of plan sections 31, 33 and 35, unchanged, for every command class and every environment state (`PqxdhDeploymentIdealEnvCost.idealStep_bound`, which also covers the allocator's no-room branch at the accept and finish classes).
- C4: `c4_ideal` and `c4_ideal_later`, the instances of `PqxdhDeploymentEnvironment.c4_closed` and `c4_later_closed` at `envGD` with `frame_idealD`.
- F4 on the final split game's own support (`seed_at_install_split`): for every parameter `p`, on every outcome of `gameWith .. splitInit (idealSplit t p)` the seed table holds a slot's seed exactly when the slot carries a hidden install ghost. It is carried from the record world with `envG t p` (`envG_admitted`) along CE-11a's `join` by `lawEq_support` (programs with the same law have the same support).

These are resource bounds and support facts in the existing models; they add no assumption and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (EnvState allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentEnvironmentJoin (merge Good initialized)
open PqxdhDeploymentIdealSteps (SplitBk splitInit)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentIdealEnv (idealStep envG envGD IdealInv)
open LazyOracleDiscard (LawEq)

variable {KemSK : Type}

/-! ### C2a: the frames of the ideal environments -/

section Frames
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}

/-- C2a for the ideal environment at fixed parameters (design-v2 section 6.3, `frame_ideal`): the startup draws at most `qInit + 32` coins (runtime initialization and the Server seed) and every command of the ideal step stays within the first-touch allowance `allowanceG (baseAllowance caps) ceFirstTouch` of its class at every environment state (`PqxdhDeploymentIdealEnvCost.idealStep_bound`). The bound is uniform in the parameters. -/
theorem frame_ideal (caps : KemCaps) (bounded : KemBound setup caps) (t : Target count) (p : Params KemSK count)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (identityIndex : ℕ) (runtime : A) :
    PqxdhRecordLiftInterface.Frame (envG setup codec checks t p ensureInit identityIndex runtime) (qInit + 32)
      (allowanceG (baseAllowance caps) ceFirstTouch) :=
  ⟨PqxdhDeploymentEnvironment.start_bound setup ensureInit qInit initBound identityIndex runtime splitInit,
    fun query state kind => PqxdhDeploymentIdealEnvCost.idealStep_bound setup codec checks caps bounded t p query state
      kind⟩

/-- C2a for the ideal environment of a target (design-v2 section 6.3 and plan section 48, A2, `frame_idealD`): the startup draws at most `qInit + 32 + (count + 1) * keygenCost + encapsCost` coins (the challenger's parameters, `PqxdhDeploymentIdealEnvCost.drawParams_uniform`, then the startup of `envG`) and every command stays within the first-touch allowance of its class at every environment state, at the parameters held in the backend. -/
theorem frame_idealD (caps : KemCaps) (bounded : KemBound setup caps) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (identityIndex : ℕ) (runtime : A) :
    PqxdhRecordLiftInterface.Frame (envGD setup codec checks t ensureInit identityIndex runtime)
      (qInit + 32 + (count + 1) * caps.keygenCost + caps.encapsCost) (allowanceG (baseAllowance caps) ceFirstTouch) := by
  refine ⟨?_, fun query state kind => ?_⟩
  · change (drawParams setup count >>= fun p => PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime
      (fun created => (p, splitInit created))).IsTotalQueryBound _
    exact (isTotalQueryBound_bind (PqxdhDeploymentIdealEnvCost.drawParams_uniform setup caps bounded count) fun p =>
      PqxdhDeploymentEnvironment.start_bound setup ensureInit qInit initBound identityIndex runtime _).mono (by omega)
  · change (Prod.map id (PqxdhDeploymentEnvironmentDraw.withE state.backend.1) <$>
      (idealStep setup codec checks t state.backend.1 query).run (PqxdhDeploymentEnvironmentDraw.dropE state)).IsQueryBoundP
        _ _
    rw [isQueryBoundP_map_iff]
    exact PqxdhDeploymentIdealEnvCost.idealStep_bound setup codec checks caps bounded t state.backend.1 query _ kind

end Frames

/-! ### C4 for the ideal environment of a target -/

section C4
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- C4 for the ideal environment of a target (design-v2 section 6.3, `c4_ideal`; `PqxdhDeploymentEnvironment.c4_closed` with `frame_idealD`): for every adversary respecting the budget `B`, every outcome of the record world with `envGD` has its BLAKE2b routes within `qHash + S + R + qBuild + qFinish` and its record derivations within `S + 51 R`. The startup coins do not enter the bound. -/
theorem c4_ideal (caps : KemCaps) (bounded : KemBound setup caps) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (identityIndex : ℕ) (runtime : A)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (B : PqxdhDeploymentInterface.Budget) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (respects : B.Respects adversary) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) serverKid bounds mode adversary),
      result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
          B.hash + B.sends + B.receives + B.build + B.finish ∧
        result.2.primitive.1.native .kdf ≤ B.sends + 51 * B.receives :=
  PqxdhDeploymentEnvironment.c4_closed setup codec route _ _ _
    (frame_idealD setup codec checks caps bounded t ensureInit qInit initBound identityIndex runtime)
    (PqxdhDeploymentEnvironment.allowanceG_hash _ _ (PqxdhDeploymentEnvironment.baseAllowance_hash caps))
    serverKid bounds mode B adversary respects

/-- Later-mode C4 for the ideal environment of a target (`PqxdhDeploymentEnvironment.c4_later_closed` with `frame_idealD`): every outcome of the two-phase record world with `envGD` has its BLAKE2b routes within `qHash + S + R + qBuild + qFinish + qHash₂` and its record derivations within `S + 51 R`. -/
theorem c4_ideal_later {Out R : Type} (caps : KemCaps) (bounded : KemBound setup caps) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (identityIndex : ℕ) (runtime : A)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (B : PqxdhDeploymentInterface.Budget) (post : PqxdhDeploymentLater.PostBudget)
    (reveal : EnvState KemSK (Params KemSK count × SplitBk) → R)
    (first : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (second : X → R → OracleComp PqxdhDeploymentLater.PostSpec Out)
    (respects : B.Respects first) (laterRespects : ∀ output disclosed, post.Respects (second output disclosed)) :
    ∀ result ∈ support (PqxdhRecordLiftLater.run setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) serverKid bounds mode reveal first second),
      result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
          B.hash + B.sends + B.receives + B.build + B.finish + post.hash ∧
        result.2.primitive.1.native .kdf ≤ B.sends + 51 * B.receives :=
  PqxdhDeploymentEnvironment.c4_later_closed setup codec route _ _ _
    (frame_idealD setup codec checks caps bounded t ensureInit qInit initBound identityIndex runtime)
    (PqxdhDeploymentEnvironment.allowanceG_hash _ _ (PqxdhDeploymentEnvironment.baseAllowance_hash caps))
    serverKid bounds mode B post reveal first second respects laterRespects

end C4

/-! ### F4 on the final split game's own support -/

/-- Programs with the same law have the same support (one inclusion). -/
theorem lawEq_support_subset {α : Type} {mx my : ProbComp α} (h : LawEq mx my) : support mx ⊆ support my := by
  classical
  intro a member
  by_contra outside
  let k : α → ProbComp Bool := fun x => pure (decide (x ∈ support my))
  have law : 𝒟[mx >>= k] = 𝒟[my >>= k] := h Bool k
  have left : false ∈ support (mx >>= k) := by
    simp only [k, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    exact ⟨a, member, by simp [outside]⟩
  have right : false ∉ support (my >>= k) := by simp [k]
  rw [mem_support_iff_evalDist_singleton_ne_zero, law, ← mem_support_iff_evalDist_singleton_ne_zero] at left
  exact right left

/-- Programs with the same law have the same support. -/
theorem lawEq_support {α : Type} {mx my : ProbComp α} (h : LawEq mx my) : support mx = support my :=
  Set.Subset.antisymm (lawEq_support_subset h) (lawEq_support_subset h.symm)

section Seeds
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- Every outcome of the record world with the ideal environment at fixed parameters (`envG`) is admissible: `Good` and `IdealInv` (the generic `PqxdhDeploymentIdealEnv.world_keeps` with `ideal_splits`). -/
theorem envG_admitted (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (envG setup codec checks t p ensureInit identityIndex runtime) setup.serverKeyId bounds mode adversary),
      ∀ value, result.1 = some value → ∃ created, Good created value.2.2 result.2 ∧ IdealInv t value.2.2 result.2 := by
  refine PqxdhDeploymentIdealEnv.world_keeps setup codec route _
    (fun created => PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) (IdealInv t)
    (PqxdhDeploymentIdealEnv.idealInv_stable t)
    (fun created => PqxdhDeploymentIdealEnv.ideal_splits setup codec route checks t p created) ?_ bounds mode adversary
  intro created start started
  have initial := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime _ created start started
  subst initial
  exact ⟨_, rfl, PqxdhDeploymentIdealEnv.idealInv_start t created⟩

/-- F4 on the final split game's own support (design-v2 section 5.2, `seed_at_install`, for every parameter `p`): on every outcome of `gameWith .. splitInit (idealSplit t p)`, the seed table holds a slot's seed exactly when the slot carries a hidden install ghost, the Server ghost (`peer` at coordinates allocated to the slot) or the Beacon ghost (`beacon` at coordinates allocated to the slot). Route: CE-11a's `join` at `envG t p` (whose startup is the split form's, so `born` is `rfl`) gives the final split game the law of the record world with `envG t p` read through `joined`; programs with the same law have the same support (`lawEq_support`); on every outcome of that record world `IdealInv` holds (`envG_admitted`), whose `seeds`, `serverMarks` and `beaconMarks` give the statement at the reassembled state. -/
theorem seed_at_install_split (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ outcome ∈ support ((PqxdhDeploymentBackend.gameWith setup codec route splitInit
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
          adversary).run' runtime),
      ∀ value, outcome = some value → ∀ j,
        (value.2.2.2.seeds j).isSome = true ↔
          ((∃ kid c, value.2.2.2.backend.2.2.peer = some (kid, c) ∧ value.2.2.2.backend.2.1.1 c = some j) ∨
            ∃ c, value.2.2.2.backend.2.2.beacon = some c ∧ value.2.2.2.backend.2.1.1 c = some j) := by
  intro outcome member value found j
  have law := PqxdhDeploymentEnvironmentJoin.join setup codec route splitInit
    (fun created => PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)
    (envG setup codec checks t p ensureInit identityIndex runtime) ensureInit identityIndex runtime rfl (IdealInv t)
    (PqxdhDeploymentIdealEnv.idealInv_stable t) (fun created => PqxdhDeploymentIdealEnv.idealInv_start t created)
    (fun created => PqxdhDeploymentIdealEnv.ideal_splits setup codec route checks t p created) bounds mode adversary
  rw [lawEq_support law, support_map] at member
  obtain ⟨result, resultMember, joinedEq⟩ := member
  rw [found] at joinedEq
  rcases resultFound : result.1 with _ | v
  · simp only [PqxdhDeploymentEnvironmentJoin.joined, resultFound, Option.map_none, reduceCtorEq] at joinedEq
  · simp only [PqxdhDeploymentEnvironmentJoin.joined, resultFound, Option.map_some, Option.some.injEq] at joinedEq
    subst joinedEq
    obtain ⟨_, _, holds⟩ := envG_admitted setup codec route checks t p ensureInit identityIndex runtime bounds mode
      adversary result resultMember v resultFound
    exact (holds.seeds j).trans (or_congr (holds.serverMarks j) (holds.beaconMarks j))

end Seeds

end BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.frame_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.frame_ideal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.frame_idealD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.frame_idealD

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.c4_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.c4_ideal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.c4_ideal_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.c4_ideal_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.lawEq_support_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.lawEq_support_subset

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.lawEq_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.lawEq_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.envG_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.envG_admitted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.seed_at_install_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame.seed_at_install_split
