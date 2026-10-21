import BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler
import BeaconcryptCore.Computational.PqxdhHiddenRoot

/-!
The explicit full76 cut and the selected response draw feed the same compiled actual source/public continuation. The analysis retains the target, whole selected response, complete client result, owner, common primitive cache and chronological candidate list. Averaging the fixed-target full-state coupling uses the existing checked PqxdhHiddenRoot averaging theorem and charges the original actual candidate event.

Original all-continuation send/raw/public-KDF caps then bound alias routing by (S+51R+K)/2^256. Duplicate inputs, equal-value handles, both directions and all public projections at the same source address remain consistent. This proves neither that the actual native prefix reaches this target-free cut nor that a permitted live reveal preserves freshness. It does not hide the first32 initialization coordinate using the second32 factorization, assert independent owners, or replace the complete public HKDF function. Live exposure, initial-family/reached-prefix and global cryptographic/resource composition remain explicit. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedAliasCut
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open ENNReal

abbrev Cut (Metadata Auxiliary : Type) :=
  (RawCtxSelectedChainGame.Context Metadata Auxiliary × RootOutput) × FullOutput

noncomputable def sampleCut {Prior Metadata Auxiliary : Type} (sample : ProbComp Prior)
    (stop : Prior → RatchetMaterial → RawCtxSelectedChainGame.Context Metadata Auxiliary) :
    ProbComp (Cut Metadata Auxiliary) := do
  let context ← RawCtxFreshChainCut.typedCut sample stop
  let output ← $ᵗ FullOutput
  pure (context, output)

noncomputable def left {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result) (cut : Cut Metadata Auxiliary) :
    ProbComp (RootOutput × RawCtxSelectedTraceOwner.TraceResult Result Metadata Auxiliary) := do
  let result ← (simulateQ (RawCtxSelectedPublicTrace.sourceImpl source writer
    (RawCtxKdfRequestTable.fullResponse cut.2) sender decode) client).run (cut.1.1.1, (cut.1.1.2, []))
  pure (cut.1.2, (cut.2, result))

noncomputable def right {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result) (cut : Cut Metadata Auxiliary) :
    ProbComp (RootOutput × RawCtxSelectedTraceOwner.TraceResult Result Metadata Auxiliary) := do
  let result ← RawCtxSelectedAliasCompiler.consistentGame source writer cut.2 cut.1.2 sender decode client cut.1.1
  pure (cut.1.2, (cut.2, result))

/-- The complete sampled cut and source continuation are exactly the original concrete public/source observation. -/
theorem left_source {Prior Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (sample : ProbComp Prior)
    (stop : Prior → RatchetMaterial → RawCtxSelectedChainGame.Context Metadata Auxiliary) :
    sampleCut sample stop >>= left source writer sender decode client =
      RawCtxFreshChainCut.observedCut sample stop
        (RawCtxSelectedPublicTrace.randomObserver source writer sender decode client) := by
  simp only [sampleCut, left, RawCtxFreshChainCut.observedCut, RawCtxSelectedPublicTrace.randomObserver,
    bind_assoc, pure_bind]

/-- Even the complete tagged analysis result differs only at an input found in the actual source trace. -/
theorem pointwise {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result) (cut : Cut Metadata Auxiliary) :
    tvDist (left source writer sender decode client cut) (right source writer sender decode client cut) ≤
      Pr{let result ← left source writer sender decode client cut}[result.1 ∈ RawCtxSelectedTraceOwner.candidates result.2].toReal := by
  have distance := (tvDist_map_le (fun result => (cut.1.2, (cut.2, result)))
    ((simulateQ (RawCtxSelectedPublicTrace.sourceImpl source writer
      (RawCtxKdfRequestTable.fullResponse cut.2) sender decode) client).run (cut.1.1.1, (cut.1.1.2, [])))
    (RawCtxSelectedAliasCompiler.consistentGame source writer cut.2 cut.1.2 sender decode client cut.1.1)).trans
      (RawCtxSelectedAliasCompiler.source_distance source writer cut.2 cut.1.2 sender decode client cut.1.1)
  have leftShape : left source writer sender decode client cut = (fun result => (cut.1.2, (cut.2, result))) <$>
      (simulateQ (RawCtxSelectedPublicTrace.sourceImpl source writer
        (RawCtxKdfRequestTable.fullResponse cut.2) sender decode) client).run (cut.1.1.1, (cut.1.1.2, [])) := by
    simp only [left, bind_pure_comp]
  have rightShape : right source writer sender decode client cut = (fun result => (cut.1.2, (cut.2, result))) <$>
      RawCtxSelectedAliasCompiler.consistentGame source writer cut.2 cut.1.2 sender decode client cut.1.1 := by
    simp only [right, bind_pure_comp]
  rw [leftShape, rightShape, prEvent_map]
  simpa only [RawCtxSelectedTraceOwner.candidates] using distance

/-- Average the fixed-input alias coupling over exactly the original full76 cut and continued challenge draw. -/
theorem cut_distance {Prior Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (sample : ProbComp Prior)
    (stop : Prior → RatchetMaterial → RawCtxSelectedChainGame.Context Metadata Auxiliary) :
    tvDist (RawCtxFreshChainCut.observedCut sample stop
        (RawCtxSelectedPublicTrace.randomObserver source writer sender decode client))
      (sampleCut sample stop >>= right source writer sender decode client) ≤
    Pr{let result ← (RawCtxFreshChainCut.observedCut sample stop
        (RawCtxSelectedPublicTrace.randomObserver source writer sender decode client))}[result.1 ∈ RawCtxSelectedTraceOwner.candidates result.2].toReal := by
  have averaged := PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind (sampleCut sample stop)
    (left source writer sender decode client) (right source writer sender decode client)
    (left source writer sender decode client)
    (fun result => result.1 ∈ RawCtxSelectedTraceOwner.candidates result.2)
    (pointwise source writer sender decode client)
  simpa only [left_source] using averaged

/-- Actual repeated source and public inputs can be routed consistently at this explicit cut for the unconditioned S+51R+K finite-byte cost. -/
theorem cut_bound {Prior Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result) (qSend qRaw qKdf : Nat)
    (sendBound : client.IsQueryBoundP RawCtxSelectedPublicTrace.IsSend qSend)
    (rawBound : client.IsQueryBoundP RawCtxSelectedPublicTrace.IsRaw qRaw)
    (kdfBound : client.IsQueryBoundP RawCtxSelectedPublicTrace.IsPublicKdf qKdf)
    (sample : ProbComp Prior)
    (stop : Prior → RatchetMaterial → RawCtxSelectedChainGame.Context Metadata Auxiliary) :
    tvDist (RawCtxFreshChainCut.observedCut sample stop
        (RawCtxSelectedPublicTrace.randomObserver source writer sender decode client))
      (sampleCut sample stop >>= right source writer sender decode client) ≤
      (((qSend + 51*qRaw + qKdf : Nat) : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal := by
  refine (cut_distance source writer sender decode client sample stop).trans ?_
  apply ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (pow_ne_zero _ (by norm_num)))
  exact RawCtxSelectedPublicTrace.stopped_candidates_bound source writer sender decode client
    qSend qRaw qKdf sendBound rawBound kdfBound sample stop

end BeaconcryptCore.Computational.RawCtxSelectedAliasCut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCut.left_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCut.left_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCut.pointwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCut.pointwise

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCut.cut_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCut.cut_distance

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCut.cut_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCut.cut_bound
