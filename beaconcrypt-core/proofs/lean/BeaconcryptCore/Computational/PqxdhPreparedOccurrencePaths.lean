import BeaconcryptCore.Computational.PqxdhRetainedOccurrencePaths

/-! The actual later sampler and complete retained saved-frame continuation supply source-generated installation paths. The same initial64 response, original Boolean trace, external callbacks and private state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPreparedOccurrencePaths
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhSecretInputKdf PqxdhCorrelatedExpand
open PqxdhInitialBeaconAmbient PqxdhInitialNativeRetained RawCtxCursorLineage RawCtxSelectedParentTable
open PqxdhPreparedPendingReplay
variable {ι M P I D K X Response A N AD PT CT : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (A := A) (N := N) (S := S) (B := B)
local notation "Evidence" => PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B
local notation "sampleMark" start => PqxdhInitialSampledParent.marker source start
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

noncomputable def sampleAnnotated (start : Start) :=
  let execution := sampleExecution start
  (PqxdhInitialInstallOccurrence.sequence (X := X) (Response := Response) source execution.initial
    (sampleMark start) execution.origin sender route decode execution.index execution.metadata execution.ready
      execution.outside).run ((execution.before, execution.trace), PqxdhInitialInstallOccurrence.empty)

/-- Completing an actually sampled pending frame under an extending retained table produces the same whole source run with its actual installation evidence and directional path certificates. No arbitrary prior owner's path or selected-address premise is supplied. -/
theorem sample_one_paths (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (depth : Nat) (start : Start) (pending : Pending)
    (supported : Sum.inr pending ∈ support
      (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (table : RawCtxKdfRequestTable.Table) (larger : Extends pending.2.1.1.1.2.1 table)
    (result : PqxdhInitialNativeCarried.Final M P I D K Bool Bool S B × RetainedState A N RootOracle.QueryCache)
    (completed : result ∈ support (RawCtxPendingMixedPrefix.finish
      (retained source writer (view (productionStream source.crypto) table) (sampleExternal source start))
      (.pending (PqxdhInitialOriginContext.frame (X := X) (Response := Response) (sampleMark start) sender route decode pending.1).1
        (PqxdhInitialOriginContext.frame (sampleMark start) sender route decode pending.1).2, project pending.2.1))) :
    ∃ evidence : Evidence,
      ((result.1.1, (result.1.2, evidence)), result.2) ∈ support
        ((simulateQ (retained source writer (view (productionStream source.crypto) table) (sampleExternal source start))
          (sampleAnnotated source sender route decode start)).run
            (start.1.shared, (start.1.privateState, start.1.cache))) ∧
      PqxdhInitialOccurrencePaths.Holds cr (view (productionStream source.crypto) table) result.1.2.1 evidence := by
  have replay := sample_one_replay source writer sender route decode depth start pending supported
    table larger result completed
  exact PqxdhRetainedOccurrencePaths.sequence_supported source writer
    (view (productionStream source.crypto) table) start.1.selectedMessage zeroRoot
    (PqxdhInitialSampledParent.response start)
    (PqxdhInitialSourcePreparedSecrecy.pre start.1.other)
    (PqxdhInitialSourcePreparedSecrecy.application start.1.other)
    (PqxdhInitialSourcePreparedSecrecy.selector start.1.other)
    (PqxdhInitialSourcePreparedSecrecy.aux start.1.other)
    (sampleMark start) true sender route decode start.1.index start.1.metadata
    { start.1.ready with root := zeroRoot } start.1.post cr (PqxdhInitialSampledParent.response start)
    (start.1.before, PqxdhInitialSourcePublication.empty) (start.1.shared, (start.1.privateState, start.1.cache))
    result replay

end BeaconcryptCore.Computational.PqxdhPreparedOccurrencePaths

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedOccurrencePaths.sample_one_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedOccurrencePaths.sample_one_paths
