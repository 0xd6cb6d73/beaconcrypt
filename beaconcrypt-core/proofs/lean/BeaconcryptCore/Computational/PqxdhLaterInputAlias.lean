import BeaconcryptCore.Computational.PqxdhLaterParentAlias
import BeaconcryptCore.Computational.PqxdhInitialPreparedRisk

/-! The selected next-chain address is compared with the actual earlier private-input log, sampled before the full parent output. These events are distinct from merely comparing with the current parent address. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhLaterInputAlias
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhCorrelatedExpand
open PqxdhErasedParentSample
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (depth qPost : Nat)
local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (A := A) (N := N) (S := S) (B := B)
local notation "Packet" => PqxdhErasedParentSample.Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)

/-- The literal missing-parent source branch retains its complete chronological log, whose length is bounded by the original all-reply source allowance. -/
theorem sample_one_log (start : Start) (pending : Pending)
    (bounded : ∀ reply, (start.1.post reply).IsTotalQueryBound qPost)
    (supported : Sum.inr pending ∈ support (sampleOne source writer sender route read depth start)) :
    pending.2.1.1.2.length ≤ 7 + qPost * 67 := by
  unfold sampleOne at supported
  have carried := (PqxdhInitialPreparedParent.supported_pending source writer _ _ _ _ _ _ sender route read _ _
    depth _ pending.2 pending.1).mp supported
  simpa only [PqxdhInitialSourceExperiment.initialState, List.length_nil, Nat.zero_add] using
    PqxdhInitialPreparedRisk.supported_length source writer _ _ _ _ _ _ sender route read _ depth _
    qPost bounded ⟨pending, carried.1⟩

/-- Every binding in the retained source cache occurs in the same actual earlier-input log. This is proved from the literal empty private source state. -/
theorem sample_one_covered (start : Start) (pending : Pending)
    (supported : Sum.inr pending ∈ support (sampleOne source writer sender route read depth start)) :
    PqxdhInitialNativeLog.Covered pending.2.1 := by
  unfold sampleOne at supported
  have carried := (PqxdhInitialPreparedParent.supported_pending source writer _ _ _ _ _ _ sender route read _ _
    depth _ pending.2 pending.1).mp supported
  apply PqxdhInitialPreparedRisk.supported_covered source writer _ _ _ _ _ _ sender route read _ depth _ _ ⟨pending, carried.1⟩
  exact fun address output found => by cases found

def inputs : Packet → List JointKdfAddress
  | .inl _ => []
  | .inr (_, .inl _) => []
  | .inr (_, .inr pending) => pending.2.1.1.2

def PacketCovered : Packet → Prop
  | .inl _ => True
  | .inr (_, .inl _) => True
  | .inr (_, .inr pending) => PqxdhInitialNativeLog.Covered pending.2.1

/-- The entire original sampler supplies both the actual earlier-log allowance and cache coverage; completed and cached decisions retain their original probability mass. -/
theorem sample_log
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (bounded : ∀ input, Sum.inr input ∈ support prior → ∀ reply, (input.post reply).IsTotalQueryBound qPost)
    (packet : Packet) (supported : packet ∈ support (sample source writer sender route read depth prior)) :
    (inputs packet).length ≤ 7 + qPost * 67 ∧ PacketCovered packet := by
  unfold sample at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨context, reached, output, _, supported⟩ := supported
  cases context with
  | inl decision =>
      simp only [mem_support_pure_iff] at supported
      subst packet
      exact ⟨Nat.zero_le _, trivial⟩
  | inr input =>
      simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨value, sampled, rfl⟩ := supported
      cases value with
      | inl decision => exact ⟨Nat.zero_le _, trivial⟩
      | inr pending =>
          exact ⟨sample_one_log source writer sender route read depth qPost (input, output) pending
            (bounded input reached) sampled,
            sample_one_covered source writer sender route read depth (input, output) pending sampled⟩

/-- Removing the earlier unused shared cache preserves the exact log and all private-cache coverage. -/
theorem normalize_inputs (packet : Packet) :
    inputs (normalize packet) = inputs packet ∧ (PacketCovered (normalize packet) ↔ PacketCovered packet) := by
  rcases packet with common | ⟨start, common | pending⟩ <;> exact ⟨rfl, Iff.rfl⟩

local notation "MaterialContext" => PqxdhErasedParentMaterial.MaterialContext (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)

noncomputable def collision (context : MaterialContext) : Bool := by
  classical
  exact decide (RawCtxSelectedParentPrivatePatch.targetAddress context.1.2 ∈
    inputs context.1.1.1 ++ [context.1.1.2.address])

/-- The full parent sampler charges the joint event of hitting any actual earlier private input or the current parent address, after that entire source prefix has executed. All remaining parent/material coordinates are retained. -/
theorem prepared_collision
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (bounded : ∀ input, Sum.inr input ∈ support prior → ∀ reply, (input.post reply).IsTotalQueryBound qPost) :
    𝒟[collision <$> PqxdhErasedParentMaterial.prepare source writer sender route read depth prior] {true} ≤
      ((8 + qPost * 67 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  simp only [PqxdhErasedParentMaterial.prepare, map_bind, map_pure, evalDist_apply_singleton,
    ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro packet supported
  have length := (sample_log source writer sender route read depth qPost prior bounded packet supported).1
  have bound : 𝒟[(do
      let parent ← $ᵗ FullOutput
      pure (decide (RawCtxFirstParentRisk.inputAddress (PqxdhOrderedChainHybrids.nextChain parent) ∈
        inputs packet ++ [address packet])) : ProbComp Bool)] {true} ≤
      ((inputs packet ++ [address packet]).length : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    simpa only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput,
      bind_pure_comp, probEvent_map, Function.comp_def, decide_eq_true_eq] using
      RawCtxFirstParentRisk.full_inputs (inputs packet ++ [address packet])
  simp only [collision, RawCtxSelectedParentEntry.fromOutput, (normalize_inputs packet).1,
    PqxdhLaterParentAlias.target_address]
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput] at bound
  rw [probEvent_bind_eq_tsum] at bound ⊢
  simp only [probEvent_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  apply bound.trans
  apply mul_le_mul_left
  apply Nat.cast_le.mpr
  simp only [List.length_append, List.length_singleton]
  omega

/-- Every retained pending cache in the full material sampler is covered by its literal earlier-input log; the unused start-cache normalization changes neither. -/
theorem material_covered
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (bounded : ∀ input, Sum.inr input ∈ support prior → ∀ reply, (input.post reply).IsTotalQueryBound qPost)
    (context : MaterialContext)
    (supported : context ∈ support (PqxdhErasedParentMaterial.prepare source writer sender route read depth prior)) :
    PacketCovered context.1.1.1 := by
  unfold PqxdhErasedParentMaterial.prepare at supported
  simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨packet, sampled, parent, _, nonce, _, chain, _, rfl⟩ := supported
  exact (normalize_inputs packet).2.mpr
    (sample_log source writer sender route read depth qPost prior bounded packet sampled).2

/-- Outside the explicitly charged joint input-collision event, the sampled child patch changes no earlier source-cache binding and cannot replace the current parent response. -/
theorem material_safe
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (bounded : ∀ input, Sum.inr input ∈ support prior → ∀ reply, (input.post reply).IsTotalQueryBound qPost)
    (context : MaterialContext)
    (supported : context ∈ support (PqxdhErasedParentMaterial.prepare source writer sender route read depth prior))
    (start : Start) (pending : Pending) (shape : context.1.1.1 = .inr (start, .inr pending))
    (safe : collision context = false) :
    pending.2.1.1.1.2.1 (RawCtxSelectedParentPrivatePatch.targetAddress context.1.2) = none ∧
      RawCtxSelectedParentPrivatePatch.targetAddress context.1.2 ≠ context.1.1.2.address ∧
      RawCtxSelectedParentPrivatePatch.targetAddress context.1.2 ∉ pending.2.1.1.2 := by
  have covered := material_covered source writer sender route read depth qPost prior bounded context supported
  simp only [PacketCovered, shape] at covered
  have absent : RawCtxSelectedParentPrivatePatch.targetAddress context.1.2 ∉ pending.2.1.1.2 ∧
      RawCtxSelectedParentPrivatePatch.targetAddress context.1.2 ≠ context.1.1.2.address := by
    simpa only [collision, shape, inputs, decide_eq_false_iff_not, List.mem_append, List.mem_singleton, not_or] using safe
  refine ⟨?_, absent.2, absent.1⟩
  cases found : pending.2.1.1.1.2.1 (RawCtxSelectedParentPrivatePatch.targetAddress context.1.2) with
  | none => rfl
  | some output => exact False.elim (absent.1 (covered _ output found))

end BeaconcryptCore.Computational.PqxdhLaterInputAlias

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterInputAlias.sample_one_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterInputAlias.sample_one_log
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterInputAlias.sample_one_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterInputAlias.sample_one_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterInputAlias.sample_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterInputAlias.sample_log
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterInputAlias.normalize_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterInputAlias.normalize_inputs
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterInputAlias.prepared_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterInputAlias.prepared_collision
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterInputAlias.material_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterInputAlias.material_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterInputAlias.material_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterInputAlias.material_safe
