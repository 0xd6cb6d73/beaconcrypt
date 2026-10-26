import BeaconcryptCore.Computational.PqxdhInitialPendingRetainedReplay
import BeaconcryptCore.Computational.PqxdhErasedParentSample

/-! The actual prepared sampler supplies retained-prefix support. Only the analysis audit is erased; the native shared state, identity/private state and initializer cache stay in the replay. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPreparedPendingReplay
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhSecretInputKdf PqxdhCorrelatedExpand
open PqxdhInitialBeaconAmbient PqxdhInitialNativeRetained RawCtxCursorLineage RawCtxSelectedParentTable
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (observe : PqxdhInitialPreparedParent.Output M P I D K Result Origin A N C S B → ProbComp Bool)
  (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
local notation "external" => PqxdhInitialNativeAudit.external pre application initial selector aux

/-- Every actual prepared pending packet reconstructs the original complete retained execution when its exact saved frame completes. The audit is projected using the checked source equality, not recovered from a chosen descriptor. -/
theorem prepared_replay (depth : Nat) (state reached : PqxdhInitialNativeAudit.State A N C)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (supported : Sum.inr (context, reached) ∈ support
      (PqxdhInitialPreparedParent.prepare source writer pre application initial selector aux mark sender route decode
        observe execution depth state))
    (table : RawCtxKdfRequestTable.Table) (larger : Extends reached.1.1.1.2.1 table)
    (result : PqxdhInitialNativeCarried.Final M P I D K Result Origin S B × RetainedState A N C)
    (completed : result ∈ support (RawCtxPendingMixedPrefix.finish
      (retained source writer (view (productionStream source.crypto) table) external)
      (.pending (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode context).1
        (PqxdhInitialOriginContext.frame mark sender route decode context).2, project reached.1))) :
    result ∈ support ((simulateQ (retained source writer (view (productionStream source.crypto) table) external)
      (PqxdhInitialNativeCarried.original (X := X) (Response := Response) source mark sender route decode execution)).run
      (project state.1)) := by
  apply PqxdhInitialPendingRetainedReplay.carried_replay source writer mark sender route decode execution
    depth (depth + 1) external state.1 reached.1 context ?_ table larger result completed
  rw [← PqxdhInitialNativeAuditCarried.carried_projection source writer pre application initial selector aux
    mark sender route decode execution depth (depth + 1) state]
  simp only [support_map, Set.mem_image]
  exact ⟨RawCtxForwardScan.Cut.pending context reached,
    ((PqxdhInitialPreparedParent.supported_pending source writer pre application initial selector aux
      mark sender route decode observe execution depth state reached context).1 supported).1, rfl⟩

local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (A := A) (N := N) (S := S) (B := B)
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
noncomputable abbrev sampleExternal (start : Start) := PqxdhInitialNativeAudit.external
  (PqxdhInitialSourcePreparedSecrecy.pre start.1.other) (PqxdhInitialSourcePreparedSecrecy.application start.1.other)
  (PqxdhInitialNativeInitializer.initial source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
  (PqxdhInitialSourcePreparedSecrecy.selector start.1.other) (PqxdhInitialSourcePreparedSecrecy.aux start.1.other)
noncomputable abbrev sampleExecution (start : Start) := PqxdhInitialSourceExperiment.execution
  (PqxdhInitialSampledParent.response start) start.1.index start.1.metadata
  { start.1.ready with root := zeroRoot } start.1.post start.1.before
local notation "sampleMark" start => PqxdhInitialSampledParent.marker source start

/-- The exact proof-erased later sampler supplies the source support needed for retained completion, with its literal initializer, original outside Post and original ambient/cache initialization. No whole-prefix provenance premise is added. -/
theorem sample_one_replay (depth : Nat) (start : Start) (pending : Pending)
    (supported : Sum.inr pending ∈ support
      (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (table : RawCtxKdfRequestTable.Table) (larger : Extends pending.2.1.1.1.2.1 table)
    (result : PqxdhInitialNativeCarried.Final M P I D K Bool Bool S B × RetainedState A N RootOracle.QueryCache)
    (completed : result ∈ support (RawCtxPendingMixedPrefix.finish
      (retained source writer (view (productionStream source.crypto) table) (sampleExternal source start))
      (.pending (PqxdhInitialOriginContext.frame (X := X) (Response := Response) (sampleMark start) sender route decode pending.1).1
        (PqxdhInitialOriginContext.frame (sampleMark start) sender route decode pending.1).2, project pending.2.1))) :
    result ∈ support ((simulateQ (retained source writer (view (productionStream source.crypto) table) (sampleExternal source start))
      (PqxdhInitialNativeCarried.original (X := X) (Response := Response) source (sampleMark start) sender route decode
        (sampleExecution start))).run (start.1.shared, (start.1.privateState, start.1.cache))) := by
  exact prepared_replay source writer _ _ _ _ _ _ sender route decode _ _ depth _ pending.2 pending.1
    supported table larger result completed

end BeaconcryptCore.Computational.PqxdhPreparedPendingReplay

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedPendingReplay.prepared_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedPendingReplay.prepared_replay
/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedPendingReplay.sample_one_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedPendingReplay.sample_one_replay
