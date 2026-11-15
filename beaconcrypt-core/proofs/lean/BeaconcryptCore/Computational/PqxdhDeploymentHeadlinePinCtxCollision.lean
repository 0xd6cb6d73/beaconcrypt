-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills
import BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame
import BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential

/-! The actual CTX world's shared BLAKE2b cache obeys the birthday bound for its ordinary source hash bill. Private coordinate/suffix hash queries are separate addresses and preserve this shared projection. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision
open CtxRomAuth
open PqxdhRecordFactsDigestCache (Cache cacheOf)
open PqxdhRecordFactsPrivateCacheSourceDraw (Spec HashInput)
open PqxdhRecordFactsPrivateCacheSourceDrawMemo (plain packed)
open PqxdhRecordFactsHashOrdinaryBills (ordinaryQuery)
open PqxdhDeploymentHeadlineDctHash (CtxColl drawPotential draw_step size_empty)
open OracleComp.ProgramLogic (wp)
variable {n : Nat}

/-- The public-byte half of the combined lazy cache is the original shared CTX cache. -/
def ordinaryCache (cache : Cache n) : CtxRO.QueryCache :=
  QueryCache.ofFn fun input => cache (.inr input.2)

/-- A private-coordinate update leaves every ordinary-byte entry unchanged. -/
theorem ordinaryCache_private (cache : Cache n) (input : PqxdhRecordLiftWorldCompiler.Label n × Pqxdh.Bytes)
    (digest : CtxDigest) : ordinaryCache (cache.cacheQuery (.inl input) digest) = ordinaryCache cache := by
  apply QueryCache.ext
  rintro ⟨⟨⟩, bytes⟩
  simp [ordinaryCache, QueryCache.cacheQuery]

/-- An ordinary-byte update is exactly the corresponding shared-cache update. -/
theorem ordinaryCache_shared (cache : Cache n) (bytes : Pqxdh.Bytes) (digest : CtxDigest) :
    ordinaryCache (cache.cacheQuery (.inr bytes) digest) = (ordinaryCache cache).cacheQuery ((), bytes) digest := by
  apply QueryCache.ext
  rintro ⟨⟨⟩, other⟩
  by_cases same : other = bytes
  · subst other
    simp [ordinaryCache, QueryCache.cacheQuery]
  · simp [ordinaryCache, QueryCache.cacheQuery, same]

/-- Both empty interfaces start with the same shared cache. -/
theorem ordinaryCache_empty : ordinaryCache (∅ : Cache n) = ∅ := by
  apply QueryCache.ext
  rintro ⟨⟨⟩, bytes⟩
  rfl

/-- Canonical source packing retains the full shared-cache projection. -/
theorem ordinaryCache_cacheOf (state : PqxdhRecordLiftIdeal.CtxPrivate n) :
    ordinaryCache (cacheOf state) = state.base.primitive.2 := by
  apply QueryCache.ext
  rintro ⟨⟨⟩, bytes⟩
  rfl

/-- An ordinary query of the combined lazy oracle is the same shared-cache query. -/
theorem ordinary_step (cache : Cache n) (bytes : Pqxdh.Bytes) :
    Prod.map id ordinaryCache <$> (plain (.inl (.inr bytes))).run cache =
      (ctxRandomOracle ((), bytes)).run (ordinaryCache cache) := by
  change Prod.map id ordinaryCache <$> ((HashInput n →ₒ CtxDigest).randomOracle (.inr bytes)).run cache =
    (CtxRO.randomOracle ((), bytes)).run (ordinaryCache cache)
  rw [randomOracle.run_eq, randomOracle.run_eq]
  have lookup : ordinaryCache cache ((), bytes) = cache (.inr bytes) := rfl
  cases hit : cache (.inr bytes) <;>
    simp [lookup, hit, Functor.map_map, ordinaryCache_shared]

/-- One ordinary digest read spends one reserved birthday read on the shared projection. -/
theorem ordinary_read (cap : ℕ) (cache : Cache n) (bytes : Pqxdh.Bytes) :
    wp ((plain (.inl (.inr bytes))).run cache) (fun result => drawPotential cap 0 (ordinaryCache result.2)) ≤
      drawPotential (cap + 1) 0 (ordinaryCache cache) := by
  have projected := congrArg (fun run => wp run (fun result => drawPotential cap 0 result.2))
    (ordinary_step cache bytes)
  rw [OracleComp.ProgramLogic.wp_map] at projected
  change (wp ((plain (.inl (.inr bytes))).run cache)
    (fun result => drawPotential cap 0 (ordinaryCache result.2))) = _ at projected
  rw [projected]
  have step := draw_step (cap + 1) 0 (ordinaryCache cache) ((), bytes)
  simp only [PqxdhCtxBirthdayPotential.drawPotential_shift] at step
  convert step using 1
  rfl

/-- Private digest reads and finite coins preserve the shared projection's birthday potential. -/
theorem ordinary_free (query : (Spec n).Domain) (cache : Cache n) (cap : ℕ)
    (free : ordinaryQuery query ≠ true) :
    wp ((plain query).run cache) (fun result => drawPotential cap 0 (ordinaryCache result.2)) ≤
      drawPotential cap 0 (ordinaryCache cache) := by
  rcases query with (input | bytes) | coin
  · change wp (((HashInput n →ₒ CtxDigest).randomOracle (.inl input)).run cache) _ ≤ _
    rw [randomOracle.run_eq]
    cases hit : cache (.inl input)
    · simp only [bind_pure_comp, OracleComp.ProgramLogic.wp_map]
      exact OracleComp.ProgramLogic.wp_le_const_of_support _ fun _ _ => le_rfl
    · simp only [OracleComp.ProgramLogic.wp_pure]
      exact le_rfl
  · exact (free rfl).elim
  · change wp ((fun reply => (reply, cache)) <$> (unifSpec.query coin : ProbComp _)) _ ≤ _
    rw [OracleComp.ProgramLogic.wp_map]
    exact OracleComp.ProgramLogic.wp_le_const_of_support _ fun _ _ => le_rfl

/-- The combined memo oracle spends only ordinary-byte hash reads in the shared-cache birthday potential. -/
theorem ordinary_program_potential {X : Type} (work : OracleComp (Spec n) X)
    (cap : ℕ) (bounded : work.IsQueryBoundP (fun query => ordinaryQuery query = true) cap) (cache : Cache n) :
    wp ((simulateQ plain work).run cache) (fun result => drawPotential 0 0 (ordinaryCache result.2)) ≤
      drawPotential cap 0 (ordinaryCache cache) := by
  refine PqxdhDeploymentHeadlineDctTools.expected_run_bounded plain (fun query => ordinaryQuery query = true)
    (fun budget state => drawPotential budget 0 (ordinaryCache state))
    (fun budget state => PqxdhCtxBirthdayPotential.drawPotential_mono_cap (Nat.le_succ budget) 0 (ordinaryCache state))
    ?_ ?_ work cap bounded cache
  · rintro ((input | bytes) | coin) state budget hashing
    · simp [ordinaryQuery] at hashing
    · exact ordinary_read budget state bytes
    · simp [ordinaryQuery] at hashing
  · exact fun query state budget free => ordinary_free query state budget free

open Classical in
/-- The shared projection of the complete combined memo experiment has at most the birthday collision probability. -/
theorem ordinary_program_collision {X : Type} (work : OracleComp (Spec n) X)
    (cap : ℕ) (bounded : work.IsQueryBoundP (fun query => ordinaryQuery query = true) cap) :
    𝒟[(fun result => decide (CacheHasCollision (ordinaryCache result.2))) <$>
      (simulateQ plain work).run ∅] {true} ≤ (cap.choose 2 : ℝ≥0∞) / 2 ^ 512 := by
  refine (PqxdhDeploymentHeadlineDctTools.chance_le_expected _ _
    (fun result => drawPotential 0 0 (ordinaryCache result.2)) ?_).trans ?_
  · intro result _ collision
    have collides := (PqxdhCtxBirthdayPotential.cacheHasCollision_iff_ctxColl (ordinaryCache result.2)).1
      (of_decide_eq_true collision)
    simp [drawPotential, collides]
  · refine (ordinary_program_potential work cap bounded ∅).trans (le_of_eq ?_)
    simp [ordinaryCache_empty, drawPotential, CtxColl, size_empty, ENNReal.div_eq_inv_mul, mul_comm]

open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxRun Client)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment Frame EffectKind)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

open Classical in
/-- The exact source compiler and the actual CTX world have the same probability of a shared-cache collision. Only private suffix dictionaries and uniform counters are erased. -/
theorem ctx_collision_probability (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (supported : ∀ label, modes label ≠ .real)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[(fun result => decide (CacheHasCollision result.2.base.primitive.2)) <$>
      ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} =
    𝒟[(fun result => decide (CacheHasCollision (ordinaryCache result.2))) <$>
      (simulateQ plain ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec)
        (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
          (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial))).run ∅] {true} := by
  rw [PqxdhRecordFactsHashSource.source_exact modes replace setup codec supported, Functor.map_map]
  have observed := (PqxdhRecordFactsPrivateCacheWorld.run_observation modes replace setup codec route env
    serverKid bounds mode adversary supported).map
    (fun result : Client n E X × (PqxdhRecordLiftProtocol.Private n ×
        (Label n → PqxdhRecordFactsPrivateCache.Local)) => decide (CacheHasCollision result.2.1.primitive.2))
  simp only [Functor.map_map] at observed
  have equal := congrArg (fun distribution : MeasureTheory.Measure Bool => distribution {true}) observed.evalDist_eq
  simp only [Prod.map, id_eq, PqxdhRecordFactsPrivateCacheWorld.observe,
    PqxdhRecordFactsPrivateCacheFamily.observeFamily, PqxdhRecordFactsCounter.zeroCtx,
    PqxdhRecordFactsCounter.zeroPrivate, PqxdhRecordFactsCounter.zeroPrimitive] at equal
  convert equal using 1 <;> rfl

open Classical in
/-- The actual CTX shared cache obeys the birthday bound under the existing environment frame and adversary budget, for replay and random key modes. -/
theorem ctx_collision (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (supported : ∀ label, modes label ≠ .real)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) (decisionCost : Nat) :
    𝒟[(fun result => decide (CacheHasCollision result.2.base.primitive.2)) <$>
      ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} ≤
      ((PqxdhRecordLiftIdeal.sharedHashTotal ⟨budget, startup, allowance, bounds, n, decisionCost⟩).choose 2 : ℝ≥0∞) /
        2 ^ 512 := by
  rw [ctx_collision_probability modes replace setup codec supported]
  exact ordinary_program_collision _ _
    (PqxdhRecordFactsHashOrdinaryBills.source_ordinary modes replace setup codec route env startup allowance framed
      serverKid bounds mode budget adversary respects decisionCost)

open Classical in
/-- Each ideal environment target's actual shared cache is charged for all public, record, build and finish hash calls. -/
theorem idealAuth_collision {A : Type} {count : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) (t : PqxdhDeploymentIdealParams.Target count)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (identityIndex : Nat) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    𝒟[(fun result => decide (CacheHasCollision result.2.base.primitive.2)) <$>
      PqxdhRecordLiftIdeal.idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime)
        setup.serverKeyId bounds mode adversary] {true} ≤
      ((budget.hash + budget.sends + budget.receives + 2 * budget.build + 2 * budget.finish).choose 2 : ℝ≥0∞) /
        2 ^ 512 := by
  have countHash : PqxdhRecordLiftIdeal.sharedHashTotal
      ⟨budget, qInit + 32 + (count + 1) * caps.keygenCost + caps.encapsCost,
        PqxdhDeploymentEnvironment.allowanceG (PqxdhDeploymentEnvironment.baseAllowance caps)
          PqxdhDeploymentEnvironment.ceFirstTouch, bounds, 2, 0⟩ =
      budget.hash + budget.sends + budget.receives + 2 * budget.build + 2 * budget.finish := by
    dsimp only [PqxdhRecordLiftIdeal.sharedHashTotal]
    rw [PqxdhDeploymentEnvironment.envTotal_hash budget 0 _
      (PqxdhDeploymentEnvironment.allowanceG_hash _ _ (fun _ => rfl))]
    omega
  have bound := ctx_collision (fun _ => .replay) id setup codec (fun _ impossible => by cases impossible) route
    (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime)
    _ _ (PqxdhDeploymentIdealFrame.frame_idealD setup codec checks caps bounded t ensureInit qInit initBound
      identityIndex runtime) setup.serverKeyId bounds mode budget adversary respects 0
  simpa only [PqxdhRecordLiftIdeal.idealAuth, countHash] using bound

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinaryCache_private' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinaryCache_private

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinaryCache_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinaryCache_shared

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinaryCache_empty' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinaryCache_empty

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinaryCache_cacheOf' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinaryCache_cacheOf

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinary_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinary_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinary_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinary_read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinary_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinary_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinary_program_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinary_program_potential

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinary_program_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ordinary_program_collision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ctx_collision_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ctx_collision_probability

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ctx_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.ctx_collision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.idealAuth_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision.idealAuth_collision
