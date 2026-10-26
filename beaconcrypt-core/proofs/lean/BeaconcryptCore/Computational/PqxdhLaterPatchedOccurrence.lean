import BeaconcryptCore.Computational.PqxdhLaterRetainedPatch

/-! The actual retained parent/child continuation inherits installation paths from the original sampled prefix. Cache extension is discharged by the same actual input-alias event; every source callback and optional result is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhLaterPatchedOccurrence
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand
open PqxdhInitialBeaconAmbient PqxdhInitialNativeRetained RawCtxSelectedParentTable RawCtxCursorLineage
open RawCtxSelectedParentPrivatePatch PqxdhOrderedChainHybrids PqxdhPreparedPendingReplay
variable {ι M P I D K X Response A N AD PT CT : Type} {extra : OracleSpec ι} {S B : Nat}
local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (A := A) (N := N) (S := S) (B := B)
local notation "Evidence" => PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B

noncomputable def patchedPrior (source : FixedHkdfSha512NoSaltSource) (pending : Pending)
    (parent output : FullOutput) : Prior :=
  lookup (privatePatch (view (productionStream source.crypto) pending.2.1.1.1.2.1) (nextChain parent) output)
    (RawCtxSelectedParentEntry.fromOutput (PqxdhInitialBuilderContext.address pending.1.original) parent)
    (nextChain parent)

/-- The literal sampled pending continuation under the retained parent/child lookup has an actual source installation annotation with the identical result and complete operational state. The only branch condition is the previously bounded same-sampler input-alias event. -/
theorem sample_one_paths (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (depth : Nat) (start : Start) (pending : Pending)
    (supported : Sum.inr pending ∈ support
      (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original])
    (result : PqxdhInitialNativeCarried.Final M P I D K Bool Bool S B × RetainedState A N RootOracle.QueryCache)
    (completed : result ∈ support ((simulateQ
      (retained source writer (patchedPrior source pending parent output) (sampleExternal source start))
      (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker source start) sender route decode pending.1
        (PqxdhInitialParentBuilderContext.reply sender route decode pending.1.original parent))).run
          (project pending.2.1))) :
    ∃ evidence : Evidence,
      ((result.1.1, (result.1.2, evidence)), result.2) ∈ support
        ((simulateQ (retained source writer (patchedPrior source pending parent output) (sampleExternal source start))
          (PqxdhPreparedOccurrencePaths.sampleAnnotated source sender route decode start)).run
            (start.1.shared, (start.1.privateState, start.1.cache))) ∧
      PqxdhInitialOccurrencePaths.Holds cr (patchedPrior source pending parent output) result.1.2.1 evidence := by
  have separate : targetAddress (nextChain parent) ≠ PqxdhInitialBuilderContext.address pending.1.original :=
    fun same => safe (List.mem_append_right _ (List.mem_singleton.mpr same))
  simp only [patchedPrior, ← PqxdhInitialNativeParentChild.child_view source pending.2.1
    (PqxdhInitialBuilderContext.address pending.1.original) parent output separate] at completed ⊢
  apply PqxdhPreparedOccurrencePaths.sample_one_paths source writer sender route decode cr depth start pending
    supported _ (PqxdhLaterRetainedPatch.sample_one_extends source writer sender route decode depth start pending
      supported parent output safe) result
  rw [PqxdhLaterRetainedPatch.frame_completion source writer (sampleExternal source start)
    (PqxdhInitialSampledParent.marker source start) sender route decode pending.1 _ (project pending.2.1) parent]
  · exact completed
  · simp only [PqxdhInitialNativeResponse.updated,
      QueryCache.cacheQuery_of_ne (spec := JointKdfRO) _ output separate.symm,
      QueryCache.cacheQuery_self]

local notation "MaterialContext" => PqxdhErasedParentMaterial.MaterialContext (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)

/-- The complete material sampler supplies the actual pre-normalization start for retained replay. The old starting shared cache is witnessed by its reached source draw, while the suffix keeps its actual reached cache; it is not reconstructed from the normalized carrier. -/
theorem material_paths (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (depth : Nat)
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (context : MaterialContext)
    (sampled : context ∈ support (PqxdhErasedParentMaterial.prepare source writer sender route decode depth prior))
    (start : Start) (pending : Pending) (shape : context.1.1.1 = .inr (start, .inr pending))
    (safe : PqxdhLaterInputAlias.collision context = false) (output : FullOutput)
    (result : PqxdhInitialNativeCarried.Final M P I D K Bool Bool S B × RetainedState A N RootOracle.QueryCache)
    (completed : result ∈ support ((simulateQ
      (retained source writer
        (patchedPrior source pending (RawCtxSelectedParentEntry.realize context.1.1.2 context.1.2) output)
        (sampleExternal source start))
      (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker source start) sender route decode pending.1
        (PqxdhInitialParentBuilderContext.reply sender route decode pending.1.original
          (RawCtxSelectedParentEntry.realize context.1.1.2 context.1.2)))).run (project pending.2.1))) :
    ∃ actualStart : Start,
      PqxdhErasedParentSample.forgetStart actualStart = start ∧
      Sum.inr actualStart.1 ∈ support prior ∧
      Sum.inr pending ∈ support (PqxdhErasedParentSample.sampleOne source writer sender route decode depth actualStart) ∧
      ∃ evidence : Evidence,
        ((result.1.1, (result.1.2, evidence)), result.2) ∈ support
          ((simulateQ (retained source writer
            (patchedPrior source pending (RawCtxSelectedParentEntry.realize context.1.1.2 context.1.2) output)
            (sampleExternal source actualStart))
            (PqxdhPreparedOccurrencePaths.sampleAnnotated source sender route decode actualStart)).run
              (actualStart.1.shared, (actualStart.1.privateState, actualStart.1.cache))) ∧
        PqxdhInitialOccurrencePaths.Holds cr
          (patchedPrior source pending (RawCtxSelectedParentEntry.realize context.1.1.2 context.1.2) output)
          result.1.2.1 evidence := by
  simp only [PqxdhErasedParentMaterial.prepare, mem_support_bind_iff, mem_support_pure_iff] at sampled
  obtain ⟨packet, sampled, parent, _, nonce, _, chain, _, rfl⟩ := sampled
  simp only [RawCtxSelectedParentEntry.realize_fromOutput] at completed ⊢
  simp only [PqxdhErasedParentSample.sample, mem_support_bind_iff] at sampled
  obtain ⟨common | input, priorReached, block, _, sampled⟩ := sampled
  · simp only [mem_support_pure_iff] at sampled
    rw [sampled] at shape
    cases shape
  simp only [mem_support_bind_iff, mem_support_pure_iff] at sampled
  obtain ⟨common | reachedPending, reached, rfl⟩ := sampled
  · cases shape
  simp only [PqxdhErasedParentSample.normalize, Sum.inr.injEq, Prod.mk.injEq] at shape
  rcases shape with ⟨rfl, rfl⟩
  refine ⟨(input, block), rfl, priorReached, reached,
    sample_one_paths source writer sender route decode cr depth (input, block) reachedPending reached
      parent output ?_ result completed⟩
  exact of_decide_eq_false safe

end BeaconcryptCore.Computational.PqxdhLaterPatchedOccurrence

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterPatchedOccurrence.sample_one_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterPatchedOccurrence.sample_one_paths
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterPatchedOccurrence.material_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterPatchedOccurrence.material_paths
