import BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains
import BeaconcryptCore.Computational.VCVioLegacyBridge

/-!
# Key-coordinate collisions in the actual eager material tapes

Both original key/nonce lists remain paired with the complete continued observer.
The unconditioned key-collision event costs choose(L+R,2)/2^256, including positions
across directions. No actual-source collision transfer, external-key exclusion,
nonce-freshness, native consumption or global multi-key conclusion is assumed.
Retained tapes are analysis state, not a new adversary key-reveal interface.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

/-- One key-coordinate event is measured in the unchanged full material sampler. -/
theorem material_key_eq (key : RootOutput) :
    Pr{let material ← $ᵗ Material}[material.1 = key] =
      (Fintype.card RootOutput : ℝ≥0∞)⁻¹ := by
  have marginal : ∀ (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
      [SampleableType (α × β)] (a : α),
      Pr{let pair ← $ᵗ (α × β)}[pair.1 = a] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
    intro α β _ _ _ _ _ a
    rw [SampleableType.prEvent_uniformSample]
    have fiber : (Finset.univ.filter fun pair : α × β => pair.1 = a) =
        ({a} : Finset α) ×ˢ (Finset.univ : Finset β) := by
      ext ⟨first, second⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Finset.mem_singleton, and_true]
    have positive : (Fintype.card β : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have finite : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [fiber, Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ, Fintype.card_prod,
      Nat.cast_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr finite) (Or.inr positive), mul_assoc,
      ENNReal.inv_mul_cancel positive finite, mul_one]
  exact marginal RootOutput NonceOutput key

/-- A prior fixed list may repeat; each entry is still charged in the collision bound. -/
theorem material_key_mem (prior : List RootOutput) :
    Pr{let material ← $ᵗ Material}[material.1 ∈ prior] ≤
      (prior.length : ℝ≥0∞) / (Fintype.card RootOutput : ℝ≥0∞) := by
  induction prior with
  | nil =>
    simp only [List.not_mem_nil, prEvent_false]
    exact zero_le
  | cons head tail ih =>
    have union := (prEvent_or_le ($ᵗ Material)
      (fun material => material.1 = head) (fun material => material.1 ∈ tail)).trans
      (add_le_add (material_key_eq head).le ih)
    simpa only [List.mem_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
      div_eq_mul_inv, add_mul, one_mul, add_comm] using union

/-- Every supported full tape retains exactly its prescribed number of material positions. -/
theorem sampleMaterials_length (count : Nat) (records : List Material)
    (supported : records ∈ support (sampleMaterials count)) : records.length = count := by
  induction count generalizing records with
  | zero =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    rfl
  | succ count ih =>
    simp only [sampleMaterials, mem_support_bind_iff] at supported
    obtain ⟨prior, hprior, last, _, finished⟩ := supported
    obtain rfl := OracleComp.eq_of_mem_support_pure _ finished
    simp only [List.length_append, List.length_singleton, ih prior hprior]

def KeyCollision (records : List Material) : Prop :=
  ¬ (records.map Prod.fst).Nodup

/-- A new position can collide only with an earlier key or inherit an existing collision. -/
theorem keyCollision_append (records : List Material) (last : Material) :
    KeyCollision (records ++ [last]) ↔ KeyCollision records ∨ last.1 ∈ records.map Prod.fst := by
  classical
  simp [KeyCollision, List.nodup_append, imp_iff_not_or]

/-- The exact birthday bound counts unordered distinct material positions, retaining their original paired nonces. -/
theorem sampleMaterials_collision_bound (count : Nat) :
    Pr{let records ← sampleMaterials count}[KeyCollision records] ≤
      (Nat.choose count 2 : ℝ≥0∞) / (Fintype.card RootOutput : ℝ≥0∞) := by
  classical
  induction count with
  | zero =>
    have zero : Pr{let records ← sampleMaterials 0}[KeyCollision records] = 0 := by
      rw [show sampleMaterials 0 = pure [] from rfl, prEvent_pure]
      simp [KeyCollision]
    rw [zero]
    exact zero_le
  | succ count ih =>
    change Pr{let records ← (sampleMaterials count >>= fun prior =>
      ($ᵗ Material) >>= fun last => pure (prior ++ [last]))}[KeyCollision records] ≤ _
    have step := prEvent_bind_le_prEvent_add_of_support (mx := sampleMaterials count)
      (p := KeyCollision) (q := KeyCollision)
      (ε := (count : ℝ≥0∞) / (Fintype.card RootOutput : ℝ≥0∞))
      (f := fun prior => ($ᵗ Material) >>= fun last => pure (prior ++ [last])) (by
        intro prior supported fresh
        have shape : (($ᵗ Material) >>= fun last => pure (prior ++ [last])) =
            (fun last => prior ++ [last]) <$> ($ᵗ Material) := by
          rw [map_eq_bind_pure_comp]
          rfl
        rw [shape, prEvent_map]
        simpa only [Function.comp_def, keyCollision_append, fresh, false_or,
          List.length_map, sampleMaterials_length count prior supported] using
          material_key_mem (prior.map Prod.fst))
    refine step.trans ((add_le_add ih le_rfl).trans_eq ?_)
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, ENNReal.add_div, add_comm]

/-- Joining the two unchanged tapes preserves their exact key/nonce draw order. -/
theorem sampleMaterials_append (left right : Nat) :
    (do let first ← sampleMaterials left
        let second ← sampleMaterials right
        pure (first ++ second)) = sampleMaterials (left + right) := by
  induction right with
  | zero => simp only [sampleMaterials, pure_bind, List.append_nil, bind_pure, Nat.add_zero]
  | succ right ih =>
    calc
      (do let first ← sampleMaterials left
          let second ← sampleMaterials (right + 1)
          pure (first ++ second)) =
        (do let prior ← (do let first ← sampleMaterials left
                            let second ← sampleMaterials right
                            pure (first ++ second))
            let last ← $ᵗ Material
            pure (prior ++ [last])) := by
              simp only [sampleMaterials, bind_assoc, pure_bind, List.append_assoc]
      _ = sampleMaterials (left + (right + 1)) := by rw [ih]; rfl

/-- The original two lists are retained together, with their original paired nonces. -/
noncomputable def sampleTapes (left right : Nat) : ProbComp (List Material × List Material) := do
  let first ← sampleMaterials left
  let second ← sampleMaterials right
  pure (first, second)

/-- The joint two-tape event charges every distinct position across and within both directions. -/
theorem sampleTapes_collision_bound (left right : Nat) :
    Pr{let tapes ← sampleTapes left right}[KeyCollision (tapes.1 ++ tapes.2)] ≤
      (Nat.choose (left + right) 2 : ℝ≥0∞) / (Fintype.card RootOutput : ℝ≥0∞) := by
  have joined : (fun tapes : List Material × List Material => tapes.1 ++ tapes.2) <$>
      sampleTapes left right = sampleMaterials (left + right) := by
    simpa only [sampleTapes, map_bind, map_pure] using sampleMaterials_append left right
  have bound := sampleMaterials_collision_bound (left + right)
  rw [← joined, prEvent_map] at bound
  exact bound

structure Observation (Context Result : Type) where
  context : Context
  tapes : List Material × List Material
  result : Result

/-- Analysis retains the same complete tapes beside an arbitrary continued observation. -/
noncomputable def observedTapes {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → List Material → List Material → ProbComp Result) (left right : Nat) :
    ProbComp (Observation Context Result) := do
  let context ← sample
  let tapes ← sampleTapes left right
  let result ← observe context tapes.1 tapes.2
  pure ⟨context, tapes, result⟩

/-- Arbitrary later observation and stopping cannot amplify this event on the retained original tapes. -/
theorem observedTapes_collision_bound {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → List Material → List Material → ProbComp Result) (left right : Nat) :
    Pr{let output ← observedTapes sample observe left right}[
      KeyCollision (output.tapes.1 ++ output.tapes.2)] ≤
      (Nat.choose (left + right) 2 : ℝ≥0∞) / (Fintype.card RootOutput : ℝ≥0∞) := by
  unfold observedTapes
  apply prEvent_bind_le_of_forall_le
  intro context
  calc
    _ ≤ Pr{let tapes ← sampleTapes left right}[KeyCollision (tapes.1 ++ tapes.2)] := by
      apply prEvent_bind_le_prEvent_of_support
      intro tapes _ fresh
      have shape :
          (do
            let result ← observe context tapes.1 tapes.2
            pure (⟨context, tapes, result⟩ : Observation Context Result)) =
          (fun result => (⟨context, tapes, result⟩ : Observation Context Result)) <$>
            observe context tapes.1 tapes.2 := by
        rw [map_eq_bind_pure_comp]
        rfl
      rw [shape, prEvent_map]
      exact prEvent_eq_zero_of_forall_not _ _ fun _ => fresh
    _ ≤ _ := sampleTapes_collision_bound left right

/-- The key coordinate has exactly the source's 256-bit width. -/
theorem material_key_card : Fintype.card RootOutput = 2 ^ 256 := by
  rw [card_vector]
  have byteCard : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in rfl
  rw [byteCard]
  calc
    256 ^ 32 = (2 ^ 8) ^ 32 := by norm_num
    _ = 2 ^ (8 * 32) := by rw [pow_mul]
    _ = 2 ^ 256 := by norm_num

/-- The concrete retained-tape bound uses key width, independently of nonce equality. -/
theorem observedTapes_collision_bound256 {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → List Material → List Material → ProbComp Result) (left right : Nat) :
    Pr{let output ← observedTapes sample observe left right}[
      KeyCollision (output.tapes.1 ++ output.tapes.2)] ≤
      (Nat.choose (left + right) 2 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  simpa only [material_key_card, Nat.cast_pow, Nat.cast_ofNat] using
    observedTapes_collision_bound sample observe left right

open PqxdhAdaptiveBidirectionalChains

/-- The exact eager client and final observation retain their complete result beside the same two tapes. -/
noncomputable def observedEager {Context Result : Type} (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left right : Nat) :
    ProbComp (Observation Context ((Result × (Nat × Nat)) × Bool)) :=
  observedTapes sample (fun context first second => do
    let original ← tapeView fallback (client context) ⟨(first, second), (0, 0)⟩
    let decision ← finish context original
    pure (original, decision)) left right

/-- Projection is the published eager game exactly, before probabilistic interpretation. -/
theorem observedEager_projection {Context Result : Type} (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left right : Nat) :
    (fun output => output.result.2) <$> observedEager fallback sample client finish left right =
      eagerGame fallback sample client finish left right := by
  simp only [observedEager, observedTapes, sampleTapes, eagerGame, map_bind, map_pure,
    bind_assoc, pure_bind, bind_pure]

/-- The exact published eager observer is paired with its original tapes when charging key aliases. -/
theorem observedEager_collision_bound {Context Result : Type} (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left right : Nat) :
    Pr{let output ← observedEager fallback sample client finish left right}[
      KeyCollision (output.tapes.1 ++ output.tapes.2)] ≤
      (Nat.choose (left + right) 2 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  exact observedTapes_collision_bound256 sample _ left right

/-- Absent the charged event, equal key bytes identify the same original material position. -/
theorem keyPositions_injective (records : List Material) (good : ¬ KeyCollision records)
    (i j : Fin records.length) (same : (records.get i).1 = (records.get j).1) : i = j := by
  have unique : (records.map Prod.fst).Nodup := Classical.not_not.mp good
  have hi : i.val < (records.map Prod.fst).length := by simpa only [List.length_map] using i.isLt
  have hj : j.val < (records.map Prod.fst).length := by simpa only [List.length_map] using j.isLt
  apply Fin.ext
  apply (unique.getElem_inj_iff (hi := hi) (hj := hj)).mp
  simpa only [List.getElem_map, List.get_eq_getElem] using same

/-- Both retained lists have their exact original lengths in every supported joint sample. -/
theorem sampleTapes_lengths (left right : Nat) (tapes : List Material × List Material)
    (supported : tapes ∈ support (sampleTapes left right)) :
    tapes.1.length = left ∧ tapes.2.length = right := by
  simp only [sampleTapes, mem_support_bind_iff] at supported
  obtain ⟨first, hfirst, second, hsecond, finished⟩ := supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ finished
  exact ⟨sampleMaterials_length left first hfirst, sampleMaterials_length right second hsecond⟩

/-- Later computation keeps the exact original position ranges alongside its full result. -/
theorem observedTapes_lengths {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → List Material → List Material → ProbComp Result) (left right : Nat)
    (output : Observation Context Result)
    (supported : output ∈ support (observedTapes sample observe left right)) :
    output.tapes.1.length = left ∧ output.tapes.2.length = right := by
  simp only [observedTapes, mem_support_bind_iff] at supported
  obtain ⟨context, _, tapes, htapes, result, _, finished⟩ := supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ finished
  exact sampleTapes_lengths left right tapes htapes

/-- Retaining the sampled objects adds no oracle call; all tape draws and complete later work remain charged. -/
theorem observedTapes_uniform_bound {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → List Material → List Material → ProbComp Result)
    (left right qSample qObserve : Nat) (sampleBound : IsTotalQueryBound sample qSample)
    (observeBound : ∀ context first second, IsTotalQueryBound (observe context first second) qObserve) :
    IsTotalQueryBound (observedTapes sample observe left right)
      (qSample + (44 * left + (44 * right + qObserve))) := by
  simp only [observedTapes, sampleTapes, bind_assoc, pure_bind]
  apply isTotalQueryBound_bind sampleBound
  intro context
  apply isTotalQueryBound_bind (sampleMaterials_query_bound left)
  intro first
  apply isTotalQueryBound_bind (sampleMaterials_query_bound right)
  intro second
  apply isTotalQueryBound_bind (n₂ := 0) (observeBound context first second)
  intro result
  trivial

/-- The concrete eager game keeps original client/observer costs and every reserved material draw. -/
theorem observedEager_uniform_bound {Context Result : Type} (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool)
    (left right qSample coins after : Nat) (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    IsTotalQueryBound (observedEager fallback sample client finish left right)
      (qSample + (44 * left + (44 * right + (coins + after)))) := by
  apply observedTapes_uniform_bound sample _ left right qSample (coins + after) sampleBound
  intro context first second
  apply isTotalQueryBound_bind
  · rw [tapeView, IsTotalQueryBound, isQueryBound_map_iff]
    exact tapeRun_uniform_bound fallback (client context) _ coins (clientBound context)
  · intro original
    apply isTotalQueryBound_bind (n₂ := 0) (finishBound context original)
    intro decision
    trivial

end BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.material_key_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.material_key_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.material_key_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.material_key_mem

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.sampleMaterials_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.sampleMaterials_length

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.keyCollision_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.keyCollision_append

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.sampleMaterials_collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.sampleMaterials_collision_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.sampleMaterials_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.sampleMaterials_append

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.sampleTapes_collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.sampleTapes_collision_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedTapes_collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedTapes_collision_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.material_key_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.material_key_card

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedTapes_collision_bound256' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedTapes_collision_bound256

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedEager_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedEager_projection

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedEager_collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedEager_collision_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.keyPositions_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.keyPositions_injective

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.sampleTapes_lengths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.sampleTapes_lengths

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedTapes_lengths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedTapes_lengths

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedTapes_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedTapes_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedEager_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions.observedEager_uniform_bound
