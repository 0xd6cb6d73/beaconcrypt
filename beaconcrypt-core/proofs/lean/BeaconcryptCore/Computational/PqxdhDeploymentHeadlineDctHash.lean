-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools
import BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame

/-!
# CE-12 D-ct: the World's BLAKE2b birthday term

The BLAKE2b commitment hash is the lazily sampled 512-bit random oracle of the record world (its cache is the World's `primitive.2`, which the reassembled split state shares). `CtxColl cache`: two distinct inputs of the cache with one digest (the generic `CollIn` at the BLAKE2b oracle, `ctxColl_collIn`). This module bounds its probability on the record world with the ideal environment of a target by the birthday term `C(ctxCap, 2)/2^512` (design section 4.6, owner note 1: a deviation from design-v2's linear `H/2^512`, see the design's section 2).

- The potential. The World counts every BLAKE2b call: a capability request charges `effects .hash` before it answers, and a record call charges `native .hash` (`hashCount`, `primCount`). `drawPotential H n C` is the stopped birthday potential: with `n ≤ H` counted calls it is `[CtxColl C] + ((H − n)·|C| + C(H − n, 2))/2^512`, and 0 beyond `H`. `draw_step`: one counted read of the lazily sampled oracle does not raise it in expectation (a miss hits one of `|C|` cached digests with chance `|C|/2^512`, `PqxdhDeploymentHeadlineDctTools.ro_coll`, `ro_size`, and `(b−1)(m+1) + C(b−1, 2) = b·m + C(b, 2) − m`).
- The World's steps. Only the BLAKE2b call of the primitive interpreter touches the cache (`primitive_step`, `primitiveRun_step`, with `expected_countCoin`: the uniform counter is instrumentation); the administrative capabilities and the hidden kernel lookups keep the cache and both counters (`capability_quiet`, `resolve_quiet`, `quiet_step`); the record steps run the primitive interpreter (`serverStep_coll`, `beaconStep_coll`). Hence `world_step_coll`: no World handler query raises the potential in expectation.
- The bound. `world_hash_count` (design c's lemma H): every outcome makes at most `ctxCap` counted calls (`PqxdhDeploymentEnvironment.c4_closed` with the frame `PqxdhDeploymentIdealFrame.frame_idealD`, whose resource premises are `KemBound`, `qInit` and `initBound`). `coll_world`: the probability of a collision is at most `C(ctxCap, 2)/2^512` (`expected_run_bounded`, `chance_le_expected`).

No assumption is used: the bound rests only on the existing modelling of BLAKE2b as the lazily sampled random oracle of the record world.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash
open OracleComp.EvalDist (expectedValue)
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentHeadlineDctTools (size CollIn)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### The collision event and the counted potential -/

/-- Two distinct inputs of the BLAKE2b cache with one digest. -/
def CtxColl (cache : CtxRomAuth.CtxRO.QueryCache) : Prop := ∃ y z d, y ≠ z ∧ cache y = some d ∧ cache z = some d

/-- The collision event is the generic one at the BLAKE2b oracle. -/
theorem ctxColl_collIn (cache : CtxRomAuth.CtxRO.QueryCache) : CtxColl cache ↔ CollIn cache := Iff.rfl

/-- The counted BLAKE2b calls of a primitive state: capability requests and record calls. -/
def primCount (prim : PqxdhRecordLiftWorld.Primitive) : ℕ := prim.1.effects .hash + prim.1.native .hash

/-- The counted BLAKE2b calls of the World. -/
def hashCount (w : PqxdhRecordLiftWorld.State 2) : ℕ := primCount w.primitive

open Classical in
/-- The stopped birthday potential with `H` counted calls allowed, after `n` counted calls on a cache. -/
noncomputable def drawPotential (H n : ℕ) (cache : CtxRomAuth.CtxRO.QueryCache) : ℝ≥0∞ :=
  if n ≤ H then
    (if CtxColl cache then 1 else 0) +
      (((H - n : ℕ) : ℝ≥0∞) * size cache + ((H - n).choose 2 : ℝ≥0∞)) * (2 ^ 512 : ℝ≥0∞)⁻¹
  else 0

/-- The stopped birthday potential of a primitive state. -/
noncomputable def primPotential (H : ℕ) (prim : PqxdhRecordLiftWorld.Primitive) : ℝ≥0∞ :=
  drawPotential H (primCount prim) prim.2

/-- The stopped birthday potential of the World. -/
noncomputable def collPotential (H : ℕ) (w : PqxdhRecordLiftWorld.State 2) : ℝ≥0∞ := primPotential H w.primitive

/-- One counted read of the lazily sampled BLAKE2b oracle does not raise the stopped birthday potential in expectation: a miss hits one of `|C|` cached digests with chance `|C|/2^512`, and `(b-1)(m+1) + C(b-1,2) = b·m + C(b,2) - m`. -/
theorem draw_step (H n : ℕ) (cache : CtxRomAuth.CtxRO.QueryCache) (query : CtxRomAuth.CtxRO.Domain) :
    expectedValue ((CtxRomAuth.ctxRandomOracle query).run cache) (fun r => drawPotential H (n + 1) r.2) ≤
      drawPotential H n cache := by
  classical
  by_cases room : n + 1 ≤ H
  · obtain ⟨b, hb⟩ : ∃ b, H - n = b + 1 := ⟨H - n - 1, by omega⟩
    have hb' : H - (n + 1) = b := by omega
    have expand : ∀ r : CtxRomAuth.CtxDigest × CtxRomAuth.CtxRO.QueryCache, drawPotential H (n + 1) r.2 =
        (if CtxColl r.2 then 1 else 0) + size r.2 * ((b : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹) +
          (b.choose 2 : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹ := by
      intro r
      simp only [drawPotential, room, ↓reduceIte, hb']
      ring
    simp only [expand]
    rw [OracleComp.EvalDist.expectedValue_add, OracleComp.EvalDist.expectedValue_add,
      OracleComp.EvalDist.expectedValue_mul_const]
    have coll := PqxdhDeploymentHeadlineDctTools.ro_coll cache query
    have sized := PqxdhDeploymentHeadlineDctTools.ro_size cache query
    have constant : expectedValue ((CtxRomAuth.ctxRandomOracle query).run cache)
        (fun _ => (b.choose 2 : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹) ≤ (b.choose 2 : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹ :=
      OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl
    rw [CtxRomAuth.ctxDigest_card] at coll
    simp only [drawPotential, show n ≤ H by omega, ↓reduceIte, hb]
    calc _ ≤ ((if CtxColl cache then 1 else 0) + size cache * ((2 : ℝ≥0∞) ^ 512)⁻¹) +
          (size cache + 1) * ((b : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹) + (b.choose 2 : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹ := by
          gcongr
          · simp only [Nat.cast_pow, Nat.cast_ofNat] at coll
            exact coll
      _ = (if CtxColl cache then 1 else 0) +
          (((b + 1 : ℕ) : ℝ≥0∞) * size cache + ((b + 1).choose 2 : ℝ≥0∞)) * (2 ^ 512 : ℝ≥0∞)⁻¹ := by
          rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.cast_add, Nat.cast_add, Nat.cast_one]
          ring
  · have zero : ∀ r : CtxRomAuth.CtxDigest × CtxRomAuth.CtxRO.QueryCache, drawPotential H (n + 1) r.2 = 0 := by
      intro r
      simp only [drawPotential, room, ↓reduceIte]
    simp only [zero]
    exact le_trans (OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl) zero_le

/-! ### The primitive interpreter -/

section Primitive
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- The uniform counter is pure instrumentation: an expectation of the counted run's value is the expectation of the run. -/
theorem expected_countCoin {Y : Type} (work : ProbComp Y) (count : ℕ) (f : Y → ℝ≥0∞) :
    expectedValue ((simulateQ PqxdhRecordLiftWorld.countCoin work).run count) (fun r => f r.1) =
      expectedValue work f := by
  have same := congrArg (fun m => expectedValue m f) (PqxdhRecordLiftWorld.countCoin_forget work count)
  simp only [OracleComp.EvalDist.expectedValue_map] at same
  exact same

/-- One call of the World's primitive interpreter does not raise the stopped birthday potential in expectation: only the BLAKE2b call touches the cache, and it raises the counted calls by one. -/
theorem primitive_step (H : ℕ) (query : RawCtxMixedOwner.NativeSpec.Domain) (prim : PqxdhRecordLiftWorld.Primitive) :
    expectedValue ((PqxdhRecordLiftWorld.primitives setup codec query).run prim) (fun r => primPotential H r.2) ≤
      primPotential H prim := by
  change expectedValue ((simulateQ PqxdhRecordLiftWorld.countCoin
    ((PqxdhDeploymentNative.primitives setup codec query).run ((), prim.2))).run prim.1.uniform >>= fun result =>
      pure (result.1.1, ({ prim.1 with uniform := result.2, native := (Function.update prim.1.native
        (RawCtxMixedOwner.callKind query) (prim.1.native (RawCtxMixedOwner.callKind query) + 1)) }, result.1.2.2)))
    (fun r => primPotential H r.2) ≤ _
  rw [OracleComp.EvalDist.expectedValue_bind]
  simp only [OracleComp.EvalDist.expectedValue_pure]
  simp only [primPotential, primCount]
  rw [expected_countCoin ((PqxdhDeploymentNative.primitives setup codec query).run ((), prim.2)) prim.1.uniform
    (fun r => drawPotential H (prim.1.effects .hash + Function.update prim.1.native
      (RawCtxMixedOwner.callKind query) (prim.1.native (RawCtxMixedOwner.callKind query) + 1) .hash) r.2.2)]
  by_cases hashing : RawCtxMixedOwner.callKind query = .hash
  · rcases query with request | (sealing | (opening | (bytes | frame)))
    all_goals simp only [RawCtxMixedOwner.callKind, reduceCtorEq] at hashing
    simp only [RawCtxMixedOwner.callKind, Function.update_self]
    change expectedValue ((RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite
      (RawCtxSourceHkdf.kdfImpl setup.source) (.inr (.inr (.inr (.inl bytes))))).run ((), prim.2)) _ ≤ _
    rw [RawCtxMixedShared.shared_hash, OracleComp.EvalDist.expectedValue_bind]
    simp only [OracleComp.EvalDist.expectedValue_pure]
    rw [← Nat.add_assoc]
    exact draw_step H _ prim.2 ((), bytes)
  · rw [Function.update_of_ne (Ne.symm hashing)]
    refine le_trans (OracleComp.EvalDist.expectedValue_mono_of_support fun r member => le_of_eq ?_)
      (OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl)
    congr 1
    rcases query with request | (sealing | (opening | (bytes | frame)))
    all_goals simp only [RawCtxMixedOwner.callKind, not_true_eq_false] at hashing
    all_goals simp only [PqxdhDeploymentNative.primitives, RawCtxMixedShared.sharedImpl, QueryImpl.compose,
      RawCtxMixedShared.sharedAdapter, simulateQ_pure, simulateQ_spec_query, RawCtxSharedPrimitive.nativeImpl,
      RawCtxSharedPrimitive.openingImpl, RawCtxSourceHkdf.kdfImpl, StateT.run, support_pure,
      Set.mem_singleton_iff] at member
    all_goals change r ∈ support (pure (_, ((), prim.2)) : ProbComp _) at member
    all_goals rw [support_pure, Set.mem_singleton_iff] at member; rw [member]

/-- A whole program on the World's primitive interpreter does not raise the stopped birthday potential in expectation. -/
theorem primitiveRun_step {α : Type} (H : ℕ) (program : OracleComp RawCtxMixedOwner.NativeSpec α)
    (prim : PqxdhRecordLiftWorld.Primitive) :
    expectedValue ((simulateQ (PqxdhRecordLiftWorld.primitives setup codec) program).run prim)
      (fun r => primPotential H r.2) ≤ primPotential H prim :=
  PqxdhDeploymentHeadlineDctTools.expected_run_bounded (PqxdhRecordLiftWorld.primitives setup codec) (fun _ => False)
    (fun _ state => primPotential H state) (fun _ _ => le_rfl) (fun _ _ _ wrong => absurd wrong id)
    (fun query state _ _ => primitive_step setup codec H query state) program 0 (isQueryBoundP_false program 0) prim

end Primitive

/-! ### The World -/

section World
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- A World step that keeps the BLAKE2b cache and the counted calls keeps the potential. -/
theorem quiet_step {α : Type} (H : ℕ) (step : ProbComp (α × PqxdhRecordLiftWorld.State 2))
    (w : PqxdhRecordLiftWorld.State 2)
    (kept : ∀ r ∈ support step, r.2.primitive.2 = w.primitive.2 ∧ hashCount r.2 = hashCount w) :
    expectedValue step (fun r => collPotential H r.2) ≤ collPotential H w := by
  refine le_trans (OracleComp.EvalDist.expectedValue_mono_of_support fun r member => le_of_eq ?_)
    (OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl)
  obtain ⟨cache, count⟩ := kept r member
  change drawPotential H (hashCount r.2) r.2.primitive.2 = drawPotential H (hashCount w) w.primitive.2
  rw [cache, count]

/-- A hidden kernel lookup keeps the BLAKE2b cache and both call counters. -/
theorem resolve_quiet (role : PqxdhRecordLiftInterface.Role) (ref : PqxdhRecordLiftInterface.KernelRef 2)
    (w : PqxdhRecordLiftWorld.State 2) :
    ∀ r ∈ support ((PqxdhRecordLiftWorld.resolve role ref).run w), r.2.primitive.2 = w.primitive.2 ∧
      r.2.primitive.1.native = w.primitive.1.native ∧ r.2.primitive.1.effects = w.primitive.1.effects := by
  intro r member
  cases ref with
  | known known =>
      simp only [PqxdhRecordLiftWorld.resolve, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl, rfl⟩
  | hidden slot =>
      obtain ⟨_, _, _, _, _, _, _, _, _, cache, native, effects⟩ :=
        PqxdhRecordLiftWorld.resolve_hidden_facts role slot w r member
      exact ⟨cache, native, effects⟩

/-- Every administrative capability keeps the BLAKE2b cache and both call counters. -/
theorem capability_quiet (request : (PqxdhRecordLiftInterface.CapabilitySpec 2).Domain)
    (notHash : ∀ bytes, request ≠ .hash bytes) (w : PqxdhRecordLiftWorld.State 2) :
    ∀ r ∈ support ((PqxdhRecordLiftWorld.capability request).run w), r.2.primitive.2 = w.primitive.2 ∧
      r.2.primitive.1.native = w.primitive.1.native ∧ r.2.primitive.1.effects = w.primitive.1.effects := by
  intro r member
  cases request with
  | peerPresent keyId =>
      simp only [PqxdhRecordLiftWorld.capability, StateT.run, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl, rfl⟩
  | ownerPresent owner =>
      simp only [PqxdhRecordLiftWorld.capability, StateT.run, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl, rfl⟩
  | appendOwner sender pin phase =>
      simp only [PqxdhRecordLiftWorld.capability, StateT.run, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl, rfl⟩
  | advanceOwner owner phase =>
      simp only [PqxdhRecordLiftWorld.capability, StateT.run] at member
      split at member
      · split_ifs at member <;>
        · simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          exact ⟨rfl, rfl, rfl⟩
      · simp only [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨rfl, rfl, rfl⟩
  | installServer keyId identity ref =>
      change r ∈ support (PqxdhRecordLiftWorld.installServer keyId identity ref w) at member
      unfold PqxdhRecordLiftWorld.installServer at member
      split at member
      · simp only [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨rfl, rfl, rfl⟩
      · split_ifs at member
        · rw [mem_support_bind_iff] at member
          obtain ⟨resolved, resolvedMember, member⟩ := member
          rw [support_pure, Set.mem_singleton_iff] at member
          subst member
          obtain ⟨cache, native, effects⟩ := resolve_quiet .server ref w resolved resolvedMember
          cases ref <;> exact ⟨cache, native, effects⟩
        · simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          exact ⟨rfl, rfl, rfl⟩
  | installBeacon owner shell ref =>
      change r ∈ support (PqxdhRecordLiftWorld.installBeacon owner shell ref w) at member
      unfold PqxdhRecordLiftWorld.installBeacon at member
      split_ifs at member
      · rw [mem_support_bind_iff] at member
        obtain ⟨resolved, resolvedMember, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        obtain ⟨cache, native, effects⟩ := resolve_quiet .beacon ref w resolved resolvedMember
        cases ref <;> exact ⟨cache, native, effects⟩
      · simp only [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨rfl, rfl, rfl⟩
  | hash bytes => exact absurd rfl (notHash bytes)


/-- A Server record step does not raise the stopped birthday potential in expectation. -/
theorem serverStep_coll (H : ℕ) (query : RawCtxServerMixed.SourceSpec.Domain) (w : PqxdhRecordLiftWorld.State 2) :
    expectedValue ((PqxdhRecordLiftWorld.serverStep setup codec route query).run w) (fun r => collPotential H r.2) ≤
      collPotential H w := by
  change expectedValue (PqxdhRecordLiftWorld.serverStep setup codec route query w) _ ≤ _
  unfold PqxdhRecordLiftWorld.serverStep
  split
  · split <;> simp only [OracleComp.EvalDist.expectedValue_pure, le_refl]
  · rw [OracleComp.EvalDist.expectedValue_bind]
    simp only [OracleComp.EvalDist.expectedValue_pure]
    exact primitiveRun_step setup codec H _ w.primitive

/-- A Beacon record step does not raise the stopped birthday potential in expectation. -/
theorem beaconStep_coll (H : ℕ) (owner : ℕ) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (w : PqxdhRecordLiftWorld.State 2) :
    expectedValue ((PqxdhRecordLiftWorld.beaconStep setup codec owner query).run w) (fun r => collPotential H r.2) ≤
      collPotential H w := by
  change expectedValue (PqxdhRecordLiftWorld.beaconStep setup codec owner query w) _ ≤ _
  unfold PqxdhRecordLiftWorld.beaconStep
  split
  · simp only [OracleComp.EvalDist.expectedValue_pure, le_refl]
  · rw [OracleComp.EvalDist.expectedValue_bind]
    simp only [OracleComp.EvalDist.expectedValue_pure]
    exact primitiveRun_step setup codec H _ w.primitive

/-- `world_step_coll`: one World handler query never raises the stopped birthday potential in expectation. -/
theorem world_step_coll (H : ℕ) (query : (PqxdhRecordLiftInterface.WorldSpec 2).Domain)
    (w : PqxdhRecordLiftWorld.State 2) :
    expectedValue ((PqxdhRecordLiftWorld.handler setup codec route query).run w) (fun r => collPotential H r.2) ≤
      collPotential H w := by
  rcases query with created | (effect | ((send | raw) | ⟨owner, plaintext | raw⟩))
  · refine quiet_step H _ w fun r member => ?_
    change r ∈ support (PqxdhRecordLiftWorld.initializeServer created w) at member
    unfold PqxdhRecordLiftWorld.initializeServer at member
    split at member <;>
    · simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl⟩
  · rcases effect with coin | request
    · refine quiet_step H _ w fun r member => ?_
      simp only [PqxdhRecordLiftWorld.handler, PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.sampled, StateT.run,
        bind_pure_comp, support_map] at member
      obtain ⟨_, _, rfl⟩ := member
      refine ⟨rfl, ?_⟩
      simp only [hashCount, primCount, PqxdhRecordLiftWorld.chargeEffect, PqxdhRecordLiftInterface.effectKind]
      rw [Function.update_of_ne (by decide)]
    · by_cases hashing : ∃ bytes, request = .hash bytes
      · obtain ⟨bytes, rfl⟩ := hashing
        simp only [PqxdhRecordLiftWorld.handler, PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability,
          PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map, OracleComp.EvalDist.expectedValue_map]
        simp only [collPotential, primPotential, primCount, PqxdhRecordLiftWorld.chargeEffect,
          PqxdhRecordLiftInterface.effectKind, Function.update_self]
        have count : w.primitive.1.effects .hash + 1 + w.primitive.1.native .hash =
            (w.primitive.1.effects .hash + w.primitive.1.native .hash) + 1 := by omega
        rw [count]
        have same := expected_countCoin ((CtxRomAuth.ctxRandomOracle ((), bytes)).run w.primitive.2)
          w.primitive.1.uniform
          (fun r => drawPotential H (w.primitive.1.effects .hash + w.primitive.1.native .hash + 1) r.2)
        exact (le_of_eq same).trans (draw_step H _ w.primitive.2 ((), bytes))
      · simp only [not_exists] at hashing
        refine quiet_step H _ w fun r member => ?_
        obtain ⟨cache, native, effects⟩ := capability_quiet request hashing _ r member
        refine ⟨cache, ?_⟩
        simp only [hashCount, primCount, native, effects, PqxdhRecordLiftWorld.chargeEffect]
        cases request with
        | hash bytes => exact absurd rfl (hashing bytes)
        | _ =>
            simp only [PqxdhRecordLiftInterface.effectKind]
            rw [Function.update_of_ne (by decide)]
  · exact serverStep_coll setup codec route H (.inl send) w
  · exact serverStep_coll setup codec route H (.inr raw) w
  · exact beaconStep_coll setup codec H owner (.inl plaintext) w
  · exact beaconStep_coll setup codec H owner (.inr raw) w

end World

/-! ### The bound on the World -/

section Bound
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
  (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)

/-- `world_hash_count` (design c's lemma H): every outcome of the record world with the ideal environment of a target makes at most `ctxCap` counted BLAKE2b calls (`PqxdhDeploymentEnvironment.c4_closed` with the frame `frame_idealD`). -/
theorem world_hash_count (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (PqxdhDeploymentIdealParams.Target.ofCE budget g) ensureInit 0
          runtime) setup.serverKeyId bounds mode adversary),
      hashCount result.2 ≤ PqxdhDeploymentHeadlineDctEvent.ctxCap budget := by
  intro result supported
  have hashes : ∀ kind : Fin 14, PqxdhDeploymentEnvironment.baseAllowance caps kind .hash =
      if kind = 4 ∨ kind = 5 then 1 else 0 := fun _ => rfl
  exact (PqxdhDeploymentEnvironment.c4_closed setup codec route _ _ _
    (PqxdhDeploymentIdealFrame.frame_idealD setup codec checks caps bounded
      (PqxdhDeploymentIdealParams.Target.ofCE budget g) ensureInit qInit initBound 0 runtime)
    (fun kind => PqxdhDeploymentEnvironment.allowanceG_hash _ _ hashes kind) setup.serverKeyId
    bounds mode budget adversary respects result supported).1

/-- The empty cache has no entry. -/
theorem size_empty : size (∅ : CtxRomAuth.CtxRO.QueryCache) = 0 := by
  unfold size
  simp

open Classical in
/-- `coll_world`: on the record world with the ideal environment of a target, the BLAKE2b cache ends with two distinct inputs of one digest with probability at most `C(ctxCap, 2)/2^512` (the stopped birthday potential does not increase, `world_step_coll`, starts at `C(ctxCap, 2)/2^512`, and is at least one on a collision, since every outcome makes at most `ctxCap` counted calls, `world_hash_count`). -/
theorem coll_world (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (respects : budget.Respects adversary) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun result => result.1.isSome && decide (CtxColl result.2.primitive.2)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (PqxdhDeploymentIdealParams.Target.ofCE budget g) ensureInit 0
          runtime) setup.serverKeyId bounds mode adversary] {true} ≤
      ((PqxdhDeploymentHeadlineDctEvent.ctxCap budget).choose 2 : ℝ≥0∞) / 2 ^ 512 := by
  classical
  refine (PqxdhDeploymentHeadlineDctTools.chance_le_expected _ _
    (fun result => collPotential (PqxdhDeploymentHeadlineDctEvent.ctxCap budget) result.2)
    (fun result supported held => ?_)).trans ?_
  · have counted := world_hash_count setup codec checks route ensureInit bounds mode adversary budget caps bounded qInit
      initBound respects g runtime result supported
    simp only [Bool.and_eq_true, decide_eq_true_eq] at held
    change 1 ≤ drawPotential _ (hashCount result.2) result.2.primitive.2
    unfold drawPotential
    simp only [counted, held.2, ↓reduceIte]
    exact le_self_add
  · refine (PqxdhDeploymentHeadlineDctTools.expected_run_bounded (PqxdhRecordLiftWorld.handler setup codec route)
      (fun _ => False) (fun _ state => collPotential (PqxdhDeploymentHeadlineDctEvent.ctxCap budget) state)
      (fun _ _ => le_rfl) (fun _ _ _ wrong => absurd wrong id)
      (fun query state _ _ => world_step_coll setup codec route _ query state) _ 0 (isQueryBoundP_false _ 0)
      PqxdhRecordLiftWorld.initial).trans (le_of_eq ?_)
    have notColl : ¬ CtxColl (∅ : CtxRomAuth.CtxRO.QueryCache) := by
      rintro ⟨y, z, d, -, found, -⟩
      cases found
    change drawPotential _ 0 ∅ = _
    simp only [drawPotential, Nat.zero_le, ↓reduceIte, notColl, Nat.sub_zero, size_empty, zero_mul, zero_add,
      ENNReal.div_eq_inv_mul, mul_comm]

end Bound

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.ctxColl_collIn' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.ctxColl_collIn

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.draw_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.draw_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.expected_countCoin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.expected_countCoin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.primitive_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.primitive_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.primitiveRun_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.primitiveRun_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.quiet_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.quiet_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.resolve_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.resolve_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.capability_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.capability_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.serverStep_coll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.serverStep_coll

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.beaconStep_coll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.beaconStep_coll

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.world_step_coll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.world_step_coll

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.world_hash_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.world_hash_count

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.size_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.size_empty

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.coll_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.coll_world
