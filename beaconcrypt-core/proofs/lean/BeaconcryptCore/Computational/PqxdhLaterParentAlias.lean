import BeaconcryptCore.Computational.PqxdhLaterExecutableSource
import BeaconcryptCore.Computational.RawCtxFirstParentRisk

/-! The actual full parent output retains its selected next-chain coordinate and parent material. The parent self-address collision is an explicit event; this module charges it without replacing the source branch or assuming separation. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhLaterParentAlias
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdf PqxdhJointKdfGame
open PqxdhOrderedChainHybrids RawCtxSelectedParentEntry

/-- The actual native selected-input address uses the source ratchet domain and the complete sampled next-chain bytes. -/
theorem target_address (target : RootOutput) :
    RawCtxSelectedParentPrivatePatch.targetAddress target = RawCtxFirstParentRisk.inputAddress target := by
  change (⟨_, (RawCtxSelectedQueryTrace.rootVector (RawCtxFreshChainCut.concreteChain target)).toList⟩ : JointKdfAddress) = _
  rw [RawCtxSelectedQueryTrace.rootVector_concrete]
  exact congrArg (fun info => (⟨info, target.toList⟩ : JointKdfAddress))
    (by simpa only [RawCtxChainSend.nativeRequest, FixedHkdfDomain.info, pqxdh.SYM_RATCHET_INFO] using PqxdhRefinement.absBytes_SYM_RATCHET_INFO)

noncomputable def fullAlias (address : JointKdfAddress) (parent : FullOutput) : Bool :=
  by classical exact decide (RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) = address)

/-- A fixed pre-draw parent address meets the actual full76 next-chain coordinate with probability at most one over the full 256-bit space. The other parent coordinates remain in the draw. -/
theorem full_alias (address : JointKdfAddress) :
    𝒟[fullAlias address <$> ($ᵗ FullOutput)] {true} ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  simp only [fullAlias, decide_eq_true_eq, target_address]
  simpa only [List.mem_singleton, List.length_singleton, Nat.cast_one, one_mul] using
    RawCtxFirstParentRisk.full_inputs [address]


section General
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
local notation "MaterialContext" => PqxdhErasedParentMaterial.MaterialContext (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)

noncomputable def collision (context : MaterialContext) : Bool :=
  by classical exact decide (RawCtxSelectedParentPrivatePatch.targetAddress context.1.2 = context.1.1.2.address)

/-- The complete original erased sampler keeps all preparation, full parent output, nonce and next-chain draws. Its parent self-address event has an explicit separate one-coordinate charge. -/
theorem prepared_alias (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (depth : Nat)
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B)) :
    𝒟[collision <$> PqxdhErasedParentMaterial.prepare source writer sender route decode depth prior] {true} ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  simp only [PqxdhErasedParentMaterial.prepare, map_bind, map_pure]
  rw [← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_le_of_forall_le_of_support
  intro packet supported
  have bound := full_alias (PqxdhErasedParentSample.address packet)
  rw [← prEvent_eq_evalDist_singleton _ true, map_eq_bind_pure_comp] at bound
  rw [prEvent_eq_evalDist_singleton]
  change 𝒟[(do
    let parent ← $ᵗ FullOutput
    let _ ← $ᵗ NonceOutput
    let _ ← $ᵗ RootOutput
    pure (fullAlias (PqxdhErasedParentSample.address packet) parent))] {true} ≤ _
  rw [← prEvent_eq_evalDist_singleton _ true]
  have drop := EvalDistEq.bind_right ($ᵗ FullOutput) fun parent =>
    (OracleComp.EvalDistEq.bind_const ($ᵗ NonceOutput) _).trans
      (OracleComp.EvalDistEq.bind_const ($ᵗ RootOutput)
        (pure (fullAlias (PqxdhErasedParentSample.address packet) parent) : ProbComp Bool))
  rw [drop.prEvent_eq (fun value => value = true)]
  simpa only [Function.comp_def] using bound

end General

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


noncomputable def carrierAlias (result : Carrier) : Bool :=
  by classical exact decide (RawCtxSelectedParentPrivatePatch.targetAddress result.2.1.2 = result.2.1.1.2.address)

/-- Exact source erasure transports the one-coordinate collision charge to the actual certified shared-ROM sampler, with its generated callback parameters and full reached cache retained. -/
theorem certified_alias (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) :
    𝒟[(fun result => carrierAlias setup result.1.val) <$>
      ((simulateQ AdaptiveCtxSharedHash.hashImpl
        (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
          selected number ancestors disclosed c depth)).run ∅)] {true} ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have bound := prepared_alias env.source env.recordWriter env.senderId env.route env.decode depth
    (PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)
  rw [← PqxdhLaterExecutableCertificates.certified_source env callbacks baseImpl kem attachedVerify primitives program post
    selected number ancestors disclosed c depth] at bound
  simpa only [Functor.map_map, collision, carrierAlias, PqxdhLaterSharedMessagePrefix.restore] using bound


/-- The actual ordinary component executes the complete prefix from its empty state; projecting only instrumentation retains exactly the same alias event and bound for every selected key. -/
theorem component_prefix_alias (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (depth : Nat) (key : RootOutput) :
    𝒟[(fun result => carrierAlias setup result.1.val) <$>
      ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto key)
        (simulateQ RawCtxSourceSharedRom.forward
          (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
            selected number ancestors disclosed c depth))).run AdaptiveCtxDynamicKnownKeys.initialSource)] {true} ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have bound := certified_alias setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth
  have source := RawCtxSourceSharedRom.forward_cache true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto key
    (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
      selected number ancestors disclosed c depth) AdaptiveCtxDynamicKnownKeys.initialSource
  simp only [RawCtxPrefixKeyOrder.initial_cache] at source
  rw [← source] at bound
  simpa only [Functor.map_map] using bound


local notation "Output" => PqxdhLaterExecutableCompletion.Output (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)
noncomputable def outputAlias : Output → Bool
  | .inl _ => false
  | .inr (carrier, _) => carrierAlias setup carrier

/-- The executable suffix keeps the exact sampled carrier; no later callback, optional failure or refusal can create a parent-alias event absent from that carrier. -/
theorem suffix_alias (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c))
    (out : Output)
    (supported : out ∈ support (PqxdhLaterExecutableCompletion.suffix setup env callbacks program post attachedVerify primitives baseImpl kem c result))
    (hit : outputAlias setup out = true) : carrierAlias setup result.val = true := by
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


/-- The ordinary component's complete actual client retains the same parent self-address charge, including all suffix work and every failed or stopping branch. This bound is separate from earlier cache-normalization and chronological collision terms. -/
theorem client_alias (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) :
    𝒟[(fun final => outputAlias setup final.1) <$>
      AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
        (PqxdhLaterExecutableCompletion.client setup env callbacks program post attachedVerify primitives baseImpl kem
          selected number ancestors disclosed c depth)] {true} ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, PqxdhLaterExecutableCompletion.client,
    simulateQ_bind, StateT.run_bind, map_bind]
  rw [← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_le_of_forall_le_of_support
  intro key keySupported
  have prefixBound := component_prefix_alias setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth key
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map] at prefixBound
  apply le_trans ?_ prefixBound
  apply prEvent_bind_le_prEvent_of_support
  intro result supported absent
  rw [prEvent_map]
  apply (OracleComp.prEvent_eq_zero_iff _ _).mpr
  intro final reached hit
  apply absent
  apply suffix_alias setup env callbacks program post attachedVerify primitives baseImpl kem c result.1 final.1 ?_ hit
  apply support_simulateQ_run'_subset (AdaptiveCtxDynamicKnownKeys.sourceImpl true
    (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto key) _ result.2
  rw [StateT.run'_eq, support_map]
  exact ⟨final, reached, rfl⟩

end Actual
end BeaconcryptCore.Computational.PqxdhLaterParentAlias

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterParentAlias.target_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterParentAlias.target_address
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterParentAlias.full_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterParentAlias.full_alias
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterParentAlias.prepared_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterParentAlias.prepared_alias
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterParentAlias.certified_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterParentAlias.certified_alias
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterParentAlias.component_prefix_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterParentAlias.component_prefix_alias
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterParentAlias.suffix_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterParentAlias.suffix_alias
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterParentAlias.client_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterParentAlias.client_alias
