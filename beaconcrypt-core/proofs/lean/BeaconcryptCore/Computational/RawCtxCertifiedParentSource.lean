import BeaconcryptCore.Computational.RawCtxSupportedSample
import BeaconcryptCore.Computational.RawCtxCursorLineage

/-!
Every pending context in the reduction carries a proof that this exact context and complete logged state came from the original source sampler. The certificate changes no runtime data, and all bounds can be proved for every inhabitant by using its actual source support. Earlier chain inputs are recovered by the finite retained-cache walk, not by an inverse of a saved continuation.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxCertifiedParentSource
open PqxdhJointKdfGame PqxdhSecretInputKdf RawCtxSelectiveFamilyLog RawCtxStoppedParentSource
variable {M P I D K A Result : Type} {S B : Nat}

/-- A certificate of the original common/pending sum is precisely a certificate of the same source pending mode. -/
theorem pending_mode (sample : ProbComp (Mode M P I D K A Result S B))
    (saved : RawCtxSupportedSample.Pending (toSum <$> sample)) :
    Mode.pending saved.val.1 saved.val.2 ∈ support sample := by
  have supported := saved.property
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨mode, actual, same⟩ := supported
  cases mode with
  | common decision => cases same
  | pending context state =>
    have equal : (context, state) = saved.val := Sum.inr.inj same
    simpa only [← equal] using actual

/-- Every certified prepared context has the exact original forward-source support and its selected cache miss. -/
theorem source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (observe : RawCtxAdjacentCacheNormalization.Output M P I D K A Result S B → ProbComp Bool)
    (saved : RawCtxSupportedSample.Pending
      (toSum <$> prepare source writer depth sender route decode client state initial observe)) :
    RawCtxLoggedParentSampler.Cut.pending saved.val.1 saved.val.2 ∈ support
      (RawCtxForwardParentSampler.first source writer depth (depth + 1) sender route decode client state initial) ∧
      saved.val.2.1.2.1 (RawCtxSelectedFamilyContext.address saved.val.1) = none :=
  pending_source source writer depth sender route decode client state initial saved.val.2 observe saved.val.1
    (pending_mode _ saved)

/-- The certified source prefix has the original initial-coordinate cache path and retains every initial full response. -/
theorem lineage (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (root : RootOutput) (initialPath : RawCtxCursorLineage.Lineage root initial.1.2)
    (observe : RawCtxAdjacentCacheNormalization.Output M P I D K A Result S B → ProbComp Bool)
    (saved : RawCtxSupportedSample.Pending
      (toSum <$> prepare source writer depth sender route decode client state initial observe)) :
    RawCtxCursorLineage.Extends initial.1.2.1 saved.val.2.1.2.1 ∧
      RawCtxCursorLineage.Lineage root saved.val.2.1.2 := by
  have actual := (RawCtxCertifiedParentSource.source source writer depth sender route decode client state initial observe saved).1
  have mapped : RawCtxLoggedParentSampler.pack sender route decode (.pending saved.val.1 saved.val.2) ∈ support
      (RawCtxLoggedParentSampler.pack sender route decode <$>
        RawCtxForwardParentSampler.first source writer depth (depth + 1) sender route decode client state initial) :=
    by rw [support_map]; exact ⟨_, actual, rfl⟩
  rw [RawCtxForwardParentSampler.first_pack] at mapped
  exact RawCtxCursorLineage.scan_state source writer (depth + 1) (RawCtxFirstParentPrefix.selected depth)
    (RawCtxPendingSelectiveFamily.program sender route decode client state) initial root initialPath _ mapped

def earlier (root : RootOutput) (depth : Nat) (state : LoggedState A) : List RootOutput :=
  ((RawCtxCursorLineage.walk state.1.2.1 depth root).map Prod.fst).getD []

/-- The finite executable prefix list contains exactly the original requested-depth ancestors and ends at the actual selected request input. -/
theorem earlier_actual (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (covered : Covered initial) (root : RootOutput) (initialPath : RawCtxCursorLineage.Lineage root initial.1.2)
    (observe : RawCtxAdjacentCacheNormalization.Output M P I D K A Result S B → ProbComp Bool)
    (saved : RawCtxSupportedSample.Pending
      (toSum <$> prepare source writer depth sender route decode client state initial observe)) :
    RawCtxCursorLineage.walk saved.val.2.1.2.1 depth root =
      some (earlier root depth saved.val.2, saved.val.2.1.2.2.input) ∧
      (earlier root depth saved.val.2).length = depth ∧
      RawCtxSelectedFamilyContext.address saved.val.1 = RawCtxFirstParentRisk.inputAddress saved.val.2.1.2.2.input ∧
      ∀ input ∈ earlier root depth saved.val.2, ∃ output, saved.val.2.1.2.1 (RawCtxFirstParentRisk.inputAddress input) = some output := by
  have facts := pending_origin source writer depth sender route decode client state initial saved.val.2 covered observe saved.val.1
    (pending_mode _ saved)
  obtain ⟨past, path⟩ := (lineage source writer depth sender route decode client state initial root initialPath observe saved).2
  rw [facts.2.2.2] at path
  have stored : earlier root depth saved.val.2 = past := by simp [earlier, path]
  rw [stored]
  have shape := RawCtxCursorLineage.walk_shape _ depth root _ path
  refine ⟨path, shape.1, ?_, shape.2⟩
  simpa only [RawCtxSelectiveChainGame.matched, RawCtxSelectiveChainGame.cursorAddress,
    RawCtxFirstParentRisk.inputAddress, decide_eq_true_eq] using facts.2.1

end BeaconcryptCore.Computational.RawCtxCertifiedParentSource

/-- info: 'BeaconcryptCore.Computational.RawCtxCertifiedParentSource.pending_mode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCertifiedParentSource.pending_mode

/-- info: 'BeaconcryptCore.Computational.RawCtxCertifiedParentSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCertifiedParentSource.source

/-- info: 'BeaconcryptCore.Computational.RawCtxCertifiedParentSource.lineage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCertifiedParentSource.lineage

/-- info: 'BeaconcryptCore.Computational.RawCtxCertifiedParentSource.earlier_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCertifiedParentSource.earlier_actual
