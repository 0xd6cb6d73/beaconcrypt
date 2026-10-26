import BeaconcryptCore.Computational.RawCtxSourceFamilyPath
import BeaconcryptCore.Computational.RawCtxPublishedKernel

/-!
Original successful publication replies have an already executed path in the actual private cache. The full adaptive source transcript preserves each such path under later cache extension, including failed operations, unrelated owners and all live reads. An initial publication prefix needs its own actual cached path; the first builder supplies that obligation in the complete source composition. No final checker is used to manufacture a target record or its derivation.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourcePublishedPath
open PqxdhJointKdfGame PqxdhSecretInputKdf RawCtxCursorLineage RawCtxSourceFamilyPath
open RawCtxProtocolReveals RawCtxKdfRequestTable
variable {A M P I D K Result : Type} {S B : Nat}

def Cached (root : RootOutput) (sequence : Std.U64) (table : Table) : Prop :=
  ∃ earlier next, walk table sequence.val root = some (earlier, next)

/-- A concrete cached publication path survives every later extension of the same private cache. -/
theorem cached_extends (root : RootOutput) (sequence : Std.U64) (before after : Table)
    (cached : Cached root sequence before) (extension : Extends before after) : Cached root sequence after := by
  obtain ⟨earlier, next, path⟩ := cached
  exact ⟨earlier, next, walk_extends before after extension _ _ _ path⟩

/-- Actual successful publication is linked to the installed sender and its already executed cache path at that exact step. -/
theorem step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (selected : Owner S B) (number : Std.U64)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec S B).Domain) (entry : LiveState M P I D K S B)
    (state : RawCtxSourceFamilyPath.State A) (valid : Good root selected entry.1 state)
    (result : ((SourceSpec S B).Range query × LiveState M P I D K S B) × RawCtxSourceFamilyPath.State A)
    (supported : result ∈ support (((impl source writer stage sender route decode query).run entry).run state))
    (recorded : (selected, number) ∈ RawCtxPublishedRecords.record query result.1.1) :
    Cached root number result.2.2.1 := by
  have preserved := RawCtxSourceFamilyPath.step source writer stage root selected sender route decode query entry state valid result supported
  have kernel := RawCtxPublishedKernel.live
    (RawCtxGenericNativeCalls.calls (RawCtxSourceSendPath.native source writer stage))
    (fun kernel => kernel.control.send_sequence)
    (RawCtxSourcePathCalls.published_call source writer stage)
    (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift)
    (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)
    sender route decode query entry state result supported selected number recorded
  obtain ⟨kernel, present, sequenceEq⟩ := kernel
  obtain ⟨earlier, path⟩ := preserved.2 kernel present
  exact ⟨earlier, RawCtxSelectedQueryTrace.rootVector kernel.send_chain, by simpa only [sequenceEq] using path⟩

abbrev CompleteState (A M P I D K : Type) (S B : Nat) := LiveState M P I D K S B × RawCtxSourceFamilyPath.State A

noncomputable def flatImpl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (SourceSpec S B) (StateT (CompleteState A M P I D K S B) ProbComp) :=
  (impl source writer stage sender route decode).flattenStateT

private theorem flat_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (selected : Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec S B).Domain) (entry : CompleteState A M P I D K S B)
    (valid : Good root selected entry.1.1 entry.2)
    (result : (SourceSpec S B).Range query × CompleteState A M P I D K S B)
    (supported : result ∈ support ((flatImpl source writer stage sender route decode query).run entry)) :
    Extends entry.2.2.1 result.2.2.2.1 ∧ Good root selected result.2.1.1 result.2.2 ∧
      ∀ number, (selected, number) ∈ RawCtxPublishedRecords.record query result.1 → Cached root number result.2.2.2.1 := by
  change result ∈ support ((fun reply => (reply.1.1, (reply.1.2, reply.2))) <$>
    ((impl source writer stage sender route decode query).run entry.1).run entry.2) at supported
  rw [support_map] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  have kept := RawCtxSourceFamilyPath.step source writer stage root selected sender route decode query entry.1 entry.2 valid reply reached
  exact ⟨kept.1, kept.2, fun number recorded =>
    step source writer stage root selected number sender route decode query entry.1 entry.2 valid reply reached recorded⟩

/-- Every publication in an actual source transcript retains its executed path in the final private cache. -/
theorem trace (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (selected : Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Result) (entry : CompleteState A M P I D K S B)
    (result : Result × CompleteState A M P I D K S B) (publications : List (RawCtxPublishedRecords.Publication S B))
    (traced : RawCtxPublishedRecords.Trace (flatImpl source writer stage sender route decode) client entry result publications)
    (valid : Good root selected entry.1.1 entry.2) :
    Extends entry.2.2.1 result.2.2.2.1 ∧ Good root selected result.2.1.1 result.2.2 ∧
      ∀ number, (selected, number) ∈ publications → Cached root number result.2.2.2.1 := by
  induction traced with
  | pure value state =>
      exact ⟨fun _ _ known => known, valid, by simp⟩
  | query query next state reply result later actual tail ih =>
      have current := flat_step source writer stage root selected sender route decode query state valid reply actual
      have laterPath := ih current.2.1
      refine ⟨fun address output known => laterPath.1 address output (current.1 address output known), laterPath.2.1, ?_⟩
      intro number recorded
      rcases List.mem_append.mp recorded with before | after
      · exact cached_extends root number _ _ (current.2.2 number before) laterPath.1
      · exact laterPath.2.2 number after

/-- A true original publication gate has an already cached target path, retaining any source-proven initial publication prefix. -/
theorem target (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (selected : Owner S B) (number : Std.U64)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Bool) (initial : List (RawCtxPublishedRecords.Publication S B))
    (entry : CompleteState A M P I D K S B) (valid : Good root selected entry.1.1 entry.2)
    (initialPaths : ∀ n, (selected, n) ∈ initial → Cached root n entry.2.2.1)
    (result : Bool × CompleteState A M P I D K S B)
    (supported : result ∈ support ((simulateQ (flatImpl source writer stage sender route decode)
      (RawCtxPublishedRecords.target client initial selected number)).run entry))
    (accepted : result.1 = true) : Cached root number result.2.2.2.1 := by
  obtain ⟨later, traced, recorded⟩ := RawCtxPublishedRecords.target_source _ client initial selected number entry result supported accepted
  have preserved := trace source writer stage root selected sender route decode client entry (true, result.2) later traced valid
  rcases List.mem_append.mp recorded with before | after
  · exact cached_extends root number _ _ (initialPaths number before) preserved.1
  · exact preserved.2.2 number after

/-- The original native selective-table source gate derives the target's retained cache path from the actual successful-publication transcript. -/
theorem source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (selected : Owner S B) (number : Std.U64)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Bool) (initial : List (RawCtxPublishedRecords.Publication S B))
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : RawCtxSourceFamilyPath.State A)
    (valid : NativeGood root selected entry.1 state)
    (initialPaths : ∀ n, (selected, n) ∈ initial → Cached root n state.2.1)
    (result : (Bool × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSourceFamilyPath.State A)
    (supported : result ∈ support (RawCtxSelectiveChainGame.family source writer stage S B sender route decode
      (RawCtxPublishedRecords.target client initial selected number) entry state.1 state.2))
    (accepted : result.1.1 = true) : Cached root number result.2.2.1 := by
  rw [RawCtxPendingSelectiveFamily.source_program, support_map] at supported
  obtain ⟨original, reached, rfl⟩ := supported
  have initialGood : Good root selected (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1) state := by
    intro kernel present
    apply valid ⟨kernel⟩
    rw [← RawCtxGenericRoleFamily.roundtrip ConcreteRatchetKernel.refined ConcreteRatchetKernel.mk (fun _ => rfl) entry.1,
      RawCtxGenericRoleFamily.native_selected, present]
    rfl
  have reached' : original ∈ support (((simulateQ (impl source writer stage sender route decode)
      (RawCtxPublishedRecords.target client initial selected number)).run
        (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1, entry.2)).run state) := by
    simpa only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingSelectiveFamily.program,
      RawCtxPendingFamilyNative.program_interpretation, impl, RawCtxSourceSendPath.native] using reached
  apply target source writer stage root selected number sender route decode client initial
    ((RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1, entry.2), state)
    initialGood initialPaths (original.1.1, (original.1.2, original.2)) _ accepted
  rw [flatImpl, simulateQ_flattenStateT_run, bind_pure_comp, support_map]
  exact ⟨original, reached', rfl⟩

/-- A cached positive-sequence publication has the actual full response at its final derivation input, before any later checker runs. -/
theorem cached_successor (root : RootOutput) (number : Std.U64) (index : Nat) (table : Table)
    (sequence : number.val = index + 1) (cached : Cached root number table) :
    ∃ earlier input output, walk table index root = some (earlier, input) ∧ table (RawCtxFirstParentRisk.inputAddress input) = some output := by
  obtain ⟨earlier, next, path⟩ := cached
  rw [sequence, walk] at path
  cases previous : walk table index root with
  | none => simp [previous] at path
  | some reached =>
      cases present : table (RawCtxFirstParentRisk.inputAddress reached.2) with
      | none => simp [previous, present] at path
      | some output => exact ⟨reached.1, reached.2, output, rfl, present⟩

end BeaconcryptCore.Computational.RawCtxSourcePublishedPath

/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePublishedPath.cached_extends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublishedPath.cached_extends


/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePublishedPath.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublishedPath.step


/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePublishedPath.trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublishedPath.trace


/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePublishedPath.target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublishedPath.target


/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePublishedPath.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublishedPath.source


/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePublishedPath.cached_successor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublishedPath.cached_successor
