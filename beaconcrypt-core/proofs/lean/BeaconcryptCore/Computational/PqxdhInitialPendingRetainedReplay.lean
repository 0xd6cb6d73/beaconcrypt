import BeaconcryptCore.Computational.RawCtxPendingSupportReplay
import BeaconcryptCore.Computational.PqxdhInitialNativeCarried

/-! Actual saved source prefixes replay under the same retained table as their complete continuations. Original dependent frames, common completions and every ambient state field are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPendingRetainedReplay
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhInitialNativeLog
open PqxdhInitialBeaconAmbient PqxdhInitialNativeRetained RawCtxCursorLineage RawCtxSelectedParentTable
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The actual native callback extension and replay theorems discharge every operational premise of saved-prefix replay. The retained completion may return any supported result, with full shared, private and root-cache state. -/
theorem source_scan (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (selected : (Spec extra RatchetChain I D K X Response Shared S B).Domain → State A N C → Bool)
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : State A N C) (cut : RawCtxPendingMixedPrefix.Prefix
      (Spec extra RatchetChain I D K X Response Shared S B) Result (State A N C))
    (supported : cut ∈ support (RawCtxStatefulPendingPrefix.scan selected
      (handler source writer stage external) client state))
    (table : RawCtxKdfRequestTable.Table) (larger : Extends cut.2.1.1.2.1 table) :
    Extends state.1.1.2.1 cut.2.1.1.2.1 ∧
      ∀ result, result ∈ support (RawCtxPendingMixedPrefix.finish
        (retained source writer (view (productionStream source.crypto) table) external) (cut.1, project cut.2)) →
        result ∈ support ((simulateQ (retained source writer (view (productionStream source.crypto) table) external)
          client).run (project state)) := by
  exact RawCtxPendingSupportReplay.scan_replay selected _
    (fun table => retained (S := S) (B := B) source writer (view (productionStream source.crypto) table) external)
    (fun state : State A N C => state.1.1.2.1) project
    (PqxdhInitialNativePath.step_extends source writer stage external)
    (PqxdhInitialNativeRetained.step_replay source writer stage external)
    client state cut supported table larger

/-- A literal descriptor returned by the full original Builder/Post sampler supplies the exact source prefix for every retained completion of its own dependent frame. No descriptor reconstruction or initial role-path premise is assumed. -/
theorem carried_replay (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
    (depth stage : Nat) (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state reached : State A N C)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth stage external state))
    (table : RawCtxKdfRequestTable.Table) (larger : Extends reached.1.1.2.1 table)
    (result : PqxdhInitialNativeCarried.Final M P I D K Result Origin S B × RetainedState A N C)
    (completed : result ∈ support (RawCtxPendingMixedPrefix.finish
      (retained source writer (view (productionStream source.crypto) table) external)
      (.pending (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode context).1
        (PqxdhInitialOriginContext.frame mark sender route decode context).2, project reached))) :
    result ∈ support ((simulateQ (retained source writer (view (productionStream source.crypto) table) external)
      (PqxdhInitialNativeCarried.original (X := X) (Response := Response) source mark sender route decode execution)).run
      (project state)) := by
  apply (source_scan source writer stage external (PqxdhInitialNativePrefix.selected (extra := extra) depth)
    (PqxdhInitialNativeCarried.original source mark sender route decode execution) state
    (.pending (PqxdhInitialOriginContext.frame mark sender route decode context).1
      (PqxdhInitialOriginContext.frame mark sender route decode context).2, reached) ?_ table larger).2 result completed
  rw [← PqxdhInitialNativeCarried.carried_pack source writer mark sender route decode execution depth stage external state]
  simp only [support_map, Set.mem_image]
  exact ⟨RawCtxForwardScan.Cut.pending context reached, supported, rfl⟩

end BeaconcryptCore.Computational.PqxdhInitialPendingRetainedReplay

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingRetainedReplay.source_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingRetainedReplay.source_scan
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingRetainedReplay.carried_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingRetainedReplay.carried_replay
