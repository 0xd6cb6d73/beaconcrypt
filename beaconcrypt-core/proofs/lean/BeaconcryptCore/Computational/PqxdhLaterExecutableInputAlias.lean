import BeaconcryptCore.Computational.PqxdhLaterInputAlias

/-! The actual certified and ordinary-component clients retain the same explicitly charged earlier-input/parent collision event. The source certificate discharges the complete prefix length; no path-safety assumption is added. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias
open PqxdhLaterInputAlias
section Actual
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
open PqxdhNativeSharedPrefix PqxdhSelectedFirstRecord RawCtxSelectedParentTable PqxdhJointKdfGame RawCtxSelectedMessageDriver PqxdhJointKdf
local notation "Front" => PqxdhInitialPostContext.NativeFront M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1)
local notation "Trace" => PqxdhInitialOriginPost.Trace Bool S (B + 1)
local notation "Carrier" => PqxdhLaterSavedSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)



noncomputable def carrierCollision (result : Carrier) : Bool :=
  collision (PqxdhLaterSharedMessagePrefix.restore setup result.2 ∅)

/-- The earlier-input collision event reads the complete private input log and sampled parent, never the separately owned shared commitment cache. -/
theorem collision_cache (result : Carrier) (cache : CtxRO.QueryCache) :
    collision (PqxdhLaterSharedMessagePrefix.restore setup result.2 cache) = carrierCollision setup result := by
  rcases result with ⟨parameters, ⟨⟨⟨packet, parent⟩, target⟩, nonce, chain⟩⟩
  rcases packet with common | ⟨start, common | pending⟩ <;> rfl

/-- The original source certificate, not an extra log-length premise, gives the full same-sampler input-collision charge for the certified executable prefix. -/
theorem certified_collision (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) :
    𝒟[(fun result => carrierCollision setup result.1.val) <$>
      ((simulateQ AdaptiveCtxSharedHash.hashImpl
        (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
          selected number ancestors disclosed c depth)).run ∅)] {true} ≤
      ((8 + PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c * 67 : Nat) : ℝ≥0∞) *
        (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have bound := prepared_collision env.source env.recordWriter env.senderId env.route env.decode depth
    (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c)
    (PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)
    (fun input reached => (PqxdhInitialPreparedSourceCaps.supported_caps env0 baseImpl kem attachedVerify primitives program post c
      selected number ancestors disclosed input reached).postBound)
  rw [← PqxdhLaterExecutableCertificates.certified_source env callbacks baseImpl kem attachedVerify primitives program post
    selected number ancestors disclosed c depth] at bound
  simpa only [Functor.map_map, collision_cache] using bound

/-- The actual ordinary component executes the complete prefix from its empty state; projecting only instrumentation retains exactly the same alias event and bound for every selected key. -/
theorem component_prefix_collision (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (depth : Nat) (key : RootOutput) :
    𝒟[(fun result => carrierCollision setup result.1.val) <$>
      ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto key)
        (simulateQ RawCtxSourceSharedRom.forward
          (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
            selected number ancestors disclosed c depth))).run AdaptiveCtxDynamicKnownKeys.initialSource)] {true} ≤
      ((8 + PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c * 67 : Nat) : ℝ≥0∞) *
        (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have bound := certified_collision setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth
  have source := RawCtxSourceSharedRom.forward_cache true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto key
    (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
      selected number ancestors disclosed c depth) AdaptiveCtxDynamicKnownKeys.initialSource
  simp only [RawCtxPrefixKeyOrder.initial_cache] at source
  rw [← source] at bound
  simpa only [Functor.map_map] using bound


local notation "Output" => PqxdhLaterExecutableCompletion.Output (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)
noncomputable def outputCollision : Output → Bool
  | .inl _ => false
  | .inr (carrier, _) => carrierCollision setup carrier

/-- The executable suffix keeps the exact sampled carrier; no later callback, optional failure or refusal can create a earlier-input/parent collision event absent from that carrier. -/
theorem suffix_collision (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c))
    (out : Output)
    (supported : out ∈ support (PqxdhLaterExecutableCompletion.suffix setup env callbacks program post attachedVerify primitives baseImpl kem c result))
    (hit : outputCollision setup out = true) : carrierCollision setup result.val = true := by
  unfold PqxdhLaterExecutableCompletion.suffix at supported
  split at supported
  · simp only [mem_support_pure_iff] at supported
    subst out
    cases hit
  · simp only [mem_support_pure_iff] at supported
    subst out
    cases hit
  · simp only [bind_pure_comp, support_map, Set.mem_image] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact hit


/-- The ordinary component's complete actual client retains the same joint earlier-input/parent collision charge, including all suffix work and every failed or stopping branch. This bound is separate from earlier cache-normalization and chronological collision terms. -/
theorem client_collision (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) :
    𝒟[(fun final => outputCollision setup final.1) <$>
      AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
        (PqxdhLaterExecutableCompletion.client setup env callbacks program post attachedVerify primitives baseImpl kem
          selected number ancestors disclosed c depth)] {true} ≤ ((8 + PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c * 67 : Nat) : ℝ≥0∞) *
        (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, PqxdhLaterExecutableCompletion.client,
    simulateQ_bind, StateT.run_bind, map_bind, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro key keySupported
  have prefixBound := component_prefix_collision setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth key
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def] at prefixBound
  apply le_trans ?_ prefixBound
  apply probEvent_bind_le_probEvent
  intro result supported absent
  rw [probEvent_map]
  apply probEvent_eq_zero_iff.mpr
  intro final reached hit
  apply absent
  apply suffix_collision setup env callbacks program post attachedVerify primitives baseImpl kem c result.1 final.1 ?_ hit
  apply support_simulateQ_run'_subset (AdaptiveCtxDynamicKnownKeys.sourceImpl true
    (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto key) _ result.2
  rw [StateT.run'_eq, support_map]
  exact ⟨final, reached, rfl⟩

local notation "Input" => PqxdhInitialPreparedSourceInput.Input (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (S := S) (B := B)
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
  (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)

/-- The earlier standalone parent self-alias is literally contained in the joint event. A consumer charging this joint event does not add that self-alias a second time at this same hop. -/
theorem parent_included (result : Carrier) (hit : PqxdhLaterParentAlias.carrierAlias setup result = true) :
    carrierCollision setup result = true := by
  simp only [PqxdhLaterParentAlias.carrierAlias, decide_eq_true_eq] at hit
  simp only [carrierCollision, collision, PqxdhLaterSharedMessagePrefix.restore, decide_eq_true_eq,
    List.mem_append, List.mem_singleton]
  exact Or.inr hit

/-- The same evaluated certified prefix supplies concrete private-cache absence and earlier-input separation on every noncolliding pending outcome. The shared cache remains exactly the one reached by this prefix. -/
theorem certified_safe (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c))
    (cache : CtxRO.QueryCache)
    (supported : (result, cache) ∈ support ((simulateQ hashImpl
      (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
        selected number ancestors disclosed c depth)).run ∅))
    (start : Input × HmacBlock) (pending : Pending)
    (shape : result.val.2.1.1.1 = .inr (start, .inr pending))
    (safe : carrierCollision setup result.val = false) :
    pending.2.store.1 (RawCtxSelectedParentPrivatePatch.targetAddress result.val.2.1.2) = none ∧
      RawCtxSelectedParentPrivatePatch.targetAddress result.val.2.1.2 ≠ result.val.2.1.1.2.address ∧
      RawCtxSelectedParentPrivatePatch.targetAddress result.val.2.1.2 ∉ pending.2.inputs := by
  have sampled : PqxdhLaterSharedMessagePrefix.restore setup result.val.2 cache ∈ support
      (PqxdhErasedParentMaterial.prepare env.source env.recordWriter env.senderId env.route env.decode depth
        (PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)) := by
    rw [← PqxdhLaterExecutableCertificates.certified_source env callbacks baseImpl kem attachedVerify primitives program post
      selected number ancestors disclosed c depth, support_map]
    exact ⟨(result, cache), supported, rfl⟩
  apply material_safe env.source env.recordWriter env.senderId env.route env.decode depth
    (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) _
    (fun input reached => (PqxdhInitialPreparedSourceCaps.supported_caps env0 baseImpl kem attachedVerify primitives program post c
      selected number ancestors disclosed input reached).postBound)
    (PqxdhLaterSharedMessagePrefix.restore setup result.val.2 cache) sampled start
    (pending.1, attach pending.2 cache)
  · simp only [PqxdhLaterSharedMessagePrefix.restore, PqxdhSharedParentInput.restore, shape,
      PqxdhSharedParentCollect.restore]
  · rwa [collision_cache setup result.val cache]


end Actual
end BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.collision_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.collision_cache
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.certified_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.certified_collision
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.component_prefix_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.component_prefix_collision
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.suffix_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.suffix_collision
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.client_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.client_collision
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.parent_included' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.parent_included
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.certified_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableInputAlias.certified_safe
