import BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins
import BeaconcryptCore.Computational.PqxdhLaterPatchedOccurrence

/-! The literal later sampler and retained completion connect the original selected-coordinate marker to source-generated directional initializer paths. The same input-alias event and pre-normalization source state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhLaterSelectedPaths
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhCorrelatedExpand
open PqxdhInitialBeaconAmbient PqxdhInitialNativeRetained RawCtxSelectedParentTable RawCtxCursorLineage
open PqxdhLaterPatchedOccurrence PqxdhOrderedChainHybrids RawCtxSelectedParentPrivatePatch
open PqxdhPreparedPendingReplay PqxdhRetainedOccurrenceInterpreter PqxdhRetainedSelectedOrigins
variable {ι M P I D K X Response A N AD PT CT : Type} {extra : OracleSpec ι} {S B : Nat}
local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (A := A) (N := N) (S := S) (B := B)
local notation "MaterialContext" => PqxdhErasedParentMaterial.MaterialContext (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)

local notation "Evidence" => PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The actual sampled source initializer and empty original label map discharge selected installation provenance under the complete retained interpreter, including every original outside Post operation. -/
theorem sample_annotated_selected (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (start : Start) (prior : Prior)
    (result : (Bool × ((PqxdhInitialPendingPost.Front RatchetChain M P I D K S B ×
      PqxdhInitialOriginPost.Trace Bool S B) × Evidence)) × RetainedState A N RootOracle.QueryCache)
    (supported : result ∈ support ((simulateQ
      (retained source writer prior (sampleExternal source start))
      (PqxdhPreparedOccurrencePaths.sampleAnnotated source sender route decode start)).run
        (start.1.shared, (start.1.privateState, start.1.cache)))) :
    Selected (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false (PqxdhInitialSampledParent.response start))
      (PqxdhInitialRootAudit.kernel (zeroRoot, PqxdhInitialSampledParent.response start)).refined result.1.2.1.2 result.1.2.2 := by
  apply sequence_selected source writer prior start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start)
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.pre start.1.other query))
    (fun reply => ambient (PqxdhInitialSourcePreparedSecrecy.application start.1.other reply))
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.selector start.1.other query))
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.aux start.1.other query))
    _ true sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot }
    start.1.post start.1.before (reassociate (start.1.shared, (start.1.privateState, start.1.cache)))
    (Prod.map id reassociate result)
  rw [← source_program source writer prior start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start)
    (PqxdhInitialSourcePreparedSecrecy.pre start.1.other) (PqxdhInitialSourcePreparedSecrecy.application start.1.other)
    (PqxdhInitialSourcePreparedSecrecy.selector start.1.other) (PqxdhInitialSourcePreparedSecrecy.aux start.1.other)]
  simp only [support_map, Set.mem_image]
  exact ⟨result, supported, rfl⟩

/-- The same actual sampled pending completion carries selected directional origins and retained paths together, preserving its complete result and operational state. -/
theorem sample_one_selected (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
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
      PqxdhInitialOccurrencePaths.Holds cr (patchedPrior source pending parent output) result.1.2.1 evidence ∧
      Selected (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false (PqxdhInitialSampledParent.response start))
        (PqxdhInitialRootAudit.kernel (zeroRoot, PqxdhInitialSampledParent.response start)).refined result.1.2.2 evidence := by
  obtain ⟨evidence, annotated, paths⟩ := PqxdhLaterPatchedOccurrence.sample_one_paths source writer sender route decode
    cr depth start pending supported parent output safe result completed
  exact ⟨evidence, annotated, paths,
    sample_annotated_selected source writer sender route decode start (patchedPrior source pending parent output)
      ((result.1.1, (result.1.2, evidence)), result.2) annotated⟩

/-- Full material sampling supplies the actual pre-normalization origin and selected initializer together with the existing path certificates. All source callbacks, complete shared cache and original Boolean decisions remain on the same supported run. -/
theorem material_selected (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
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
          result.1.2.1 evidence ∧
        Selected (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false (PqxdhInitialSampledParent.response actualStart))
          (PqxdhInitialRootAudit.kernel (zeroRoot, PqxdhInitialSampledParent.response actualStart)).refined result.1.2.2 evidence := by
  obtain ⟨actualStart, normalized, priorReached, sampledPending, evidence, annotated, paths⟩ :=
    PqxdhLaterPatchedOccurrence.material_paths source writer sender route decode cr depth prior context sampled
      start pending shape safe output result completed
  exact ⟨actualStart, normalized, priorReached, sampledPending, evidence, annotated, paths,
    sample_annotated_selected source writer sender route decode actualStart
      (patchedPrior source pending (RawCtxSelectedParentEntry.realize context.1.1.2 context.1.2) output)
      ((result.1.1, (result.1.2, evidence)), result.2) annotated⟩

end BeaconcryptCore.Computational.PqxdhLaterSelectedPaths

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSelectedPaths.sample_annotated_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSelectedPaths.sample_annotated_selected
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSelectedPaths.sample_one_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSelectedPaths.sample_one_selected
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSelectedPaths.material_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSelectedPaths.material_selected
