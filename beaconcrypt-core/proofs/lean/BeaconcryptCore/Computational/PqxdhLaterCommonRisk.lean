import BeaconcryptCore.Computational.PqxdhErasedParentSample
import BeaconcryptCore.Computational.RawCtxSendLineageCollision
import BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy

/-! The later sampler's completed publication and cached pending branches share one actual chronological cache-collision event. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterCommonRisk
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxCursorLineage RawCtxSelectiveChainGame

/-- A cached publication strictly beyond the actual retained cursor forces that cursor's input to be present in the same table. No injectivity or collision-freedom hypothesis is used. -/
theorem cached_beyond_cursor (root : RootOutput) (number : Std.U64) (store : Store)
    (lineage : Lineage root store) (cached : RawCtxSourcePublishedPath.Cached root number store.1)
    (ordered : store.2.depth < number.val) : store.1 (cursorAddress store.2) ≠ none := by
  obtain ⟨earlier, left⟩ := lineage
  obtain ⟨past, next, right⟩ := cached
  have member := RawCtxSendLineageCollision.walk_earlier store.1 store.2.depth number.val ordered root
    (earlier, store.2.input) (past, next) left right
  obtain ⟨output, present⟩ := (walk_shape store.1 number.val root (past, next) right).2 store.2.input member
  exact fun absent => (Option.some_ne_none output) (present.symm.trans absent)

open PqxdhInitialNativeCarried PqxdhInitialNativeLog PqxdhInitialNativePrefix PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : Execution extra M P I D K Result Origin S B)

local notation "packed" cut => RawCtxForwardScan.pack
  (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) cut

/-- Every actual complete or pending cut retains the initial directional lineage and the scan's depth bound. All unselected source callbacks, including failed and external callbacks, are included. -/
theorem carried_invariants (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (root : RootOutput) (state : State A N C)
    (initialDepth : Depth depth state) (initialLineage : Lineage root state.1.1.2)
    (cut : Carried extra M P I D K Result Origin A N C S B)
    (supported : cut ∈ support (carried source writer mark sender route decode execution depth stage external state)) :
    Depth depth (packed cut).2 ∧ Lineage root (packed cut).2.1.1.2 := by
  have mapped : (packed cut) ∈ support
      ((fun result => packed result) <$> carried source writer mark sender route decode execution depth stage external state) := by
    rw [support_map]
    exact ⟨cut, supported, rfl⟩
  rw [carried_pack] at mapped
  exact RawCtxStatefulPrefixInvariant.scan_valid (PqxdhInitialNativePrefix.selected (extra := extra) depth)
    (PqxdhInitialNativeLog.handler source writer stage external)
    (fun current => Depth depth current ∧ Lineage root current.1.1.2)
    (fun query before valid unchosen reply actual =>
      ⟨step_preserve source writer stage depth external query before valid.1 unchosen reply actual,
       PqxdhInitialPublishedEvent.callback_lineage source writer stage external query before root valid.2 reply actual⟩)
    _ state ⟨initialDepth, initialLineage⟩ _ mapped

/-- A supported complete cut is a supported execution of the identical full source, with the same actual result and entire reached state. No suffix is invented. -/
theorem complete_supported (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state reached : State A N C) (result : Final M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.complete result reached ∈ support
      (carried source writer mark sender route decode execution depth stage external state)) :
    (result, reached) ∈ support
      (PqxdhInitialNativeAdjacent.run source writer mark sender route decode execution external stage state) := by
  rw [PqxdhInitialNativeAdjacent.run, ← carried_finish source writer mark sender route decode execution depth stage external state]
  rw [mem_support_bind_iff]
  refine ⟨.complete result reached, supported, ?_⟩
  simp [RawCtxForwardScan.pack, RawCtxPendingMixedPrefix.finish]

section Source
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
variable (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
  (other : QueryImpl (External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache))
  (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
  (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
  (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
  (selectedOwner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
  (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)

local notation "sourceMark" => PqxdhInitialSelectedOrigin.mark source selectedMessage
local notation "sourceExecution" => PqxdhInitialSourceExperiment.execution response64 index metadata ready post before
local notation "sourceExternal" => PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other
local notation "sourceRoot" => PqxdhInitialSourceExperiment.root source previousRoot response64 selectedOwner
local notation "sourceInitial" => PqxdhInitialSourceExperiment.initialState sourceRoot shared privateState cache
local notation "sourceCarried" depth => carried source writer sourceMark sender route decode sourceExecution depth (depth + 1) sourceExternal sourceInitial

/-- A completed actual later-target publication before the selected cut forces the same chronological cache-collision event. The concrete source supplies its empty initial trace, cursor and directional root. -/
theorem source_complete_risk (depth : Nat) (position : number.val = depth + 2)
    (result : Final M P I D K Bool Bool S B) (reached : PqxdhInitialOriginPostPath.State A N)
    (supported : RawCtxForwardScan.Cut.complete result reached ∈ support (sourceCarried depth))
    (published : PqxdhInitialPublishedEvent.Gate selectedOwner number result) :
    ¬ PqxdhInitialNativeRisk.Clean reached := by
  have actual := complete_supported source writer sourceMark sender route decode sourceExecution depth (depth + 1)
    sourceExternal sourceInitial reached result supported
  rw [← PqxdhInitialSourceExperiment.run_source] at actual
  have cached := PqxdhInitialSourceExperiment.published_cached source writer selectedMessage previousRoot response64
    other sender route decode index metadata ready post before selectedOwner number shared privateState cache
    (depth + 1) (result, reached) actual published.2
  have invariant := carried_invariants source writer sourceMark sender route decode sourceExecution depth (depth + 1)
    sourceExternal sourceRoot sourceInitial (Nat.zero_le depth) (RawCtxCursorLineage.initial _ sourceRoot)
    (.complete result reached) supported
  refine cached_beyond_cursor sourceRoot number reached.1.1.2 invariant.2 cached ?_
  exact Nat.lt_of_le_of_lt invariant.1 (by omega)

/-- The actual inner common branches: a completed target publication or a pending cached predecessor. This does not include the outer preparation's common Boolean. -/
def Common : Carried extra M P I D K Bool Bool A N RootOracle.QueryCache S B → Prop
  | .complete result _ => PqxdhInitialPublishedEvent.Gate selectedOwner number result
  | .pending context state => state.1.1.2.1 (PqxdhInitialBuilderContext.address context.original) ≠ none

open Classical in
/-- Completed target publication and cached pending branches share one chronological collision bound from the actual empty source state; they are not charged by two independent union bounds. -/
theorem source_common_risk (depth : Nat) (position : number.val = depth + 2)
    (qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost) :
    𝒟[(fun cut => decide (Common selectedOwner number cut)) <$> sourceCarried depth] {true} ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  simp only [decide_eq_true_eq]
  have risk := PqxdhInitialNativeRisk.carried_risk source writer sourceMark sender route decode sourceExecution
    depth 0 qPost sourceExternal bounded sourceInitial
    (PqxdhInitialSourceExperiment.initial_valid sourceRoot shared privateState cache depth).1
    (PqxdhInitialSourceExperiment.initial_valid sourceRoot shared privateState cache depth).2
  simp only [Nat.zero_add] at risk
  refine (prEvent_mono_of_support _ _ (fun result => ¬PqxdhInitialNativeRisk.Clean
    (RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame (X := X) (Response := Response) sourceMark sender route decode) result).2) ?_).trans risk
  intro cut supported common
  cases cut with
  | complete result reached =>
      exact source_complete_risk source writer sender route decode selectedMessage previousRoot response64
        other index metadata ready post before selectedOwner number shared privateState cache
        depth position result reached supported common
  | pending context reached =>
      have selected := carried_cases source writer sourceMark sender route decode sourceExecution depth (depth + 1)
        sourceExternal sourceInitial reached
        (PqxdhInitialSourceExperiment.initial_valid sourceRoot shared privateState cache depth).1.1 context supported
      have same : PqxdhInitialBuilderContext.address context.original = cursorAddress reached.1.1.2.2 := by
        simpa only [RawCtxSelectiveChainGame.matched, decide_eq_true_eq] using selected.1
      change reached.1.1.2.1 (cursorAddress reached.1.1.2.2) ≠ none
      rw [← same]
      exact common

variable (ancestors disclosed : List RatchetChain)
local notation "sourcePre" => PqxdhInitialSourcePreparedSecrecy.pre other
local notation "sourceApplication" => PqxdhInitialSourcePreparedSecrecy.application other
local notation "sourceInitializer" => PqxdhInitialNativeInitializer.initial source selectedMessage previousRoot response64
local notation "sourceSelector" => PqxdhInitialSourcePreparedSecrecy.selector other
local notation "sourceAux" => PqxdhInitialSourcePreparedSecrecy.aux other
local notation "sourceObserve" => PqxdhInitialSourcePreparedSecrecy.observe source previousRoot response64 selectedOwner number ancestors disclosed
local notation "sourcePrepared" depth => PqxdhInitialPreparedParent.prepare source writer sourcePre sourceApplication
  sourceInitializer sourceSelector sourceAux sourceMark sender route decode sourceObserve sourceExecution depth (sourceInitial, [])

open Classical in
/-- The concrete prepared sampler's common true mass obeys the same single bound. Its cached continuation and original freshness decision remain evaluated in full. -/
theorem prepared_common_risk (depth : Nat) (position : number.val = depth + 2)
    (qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost) :
    𝒟[(fun value => @decide (value = Sum.inl true) (Classical.propDecidable _)) <$> sourcePrepared depth] {true} ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  classical
  have bound := source_common_risk source writer sender route decode selectedMessage previousRoot response64
    other index metadata ready post before selectedOwner number shared privateState cache depth position qPost bounded
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map] at bound ⊢
  simp only [decide_eq_true_eq] at bound ⊢
  rw [← PqxdhInitialSourcePreparedSecrecy.external_source source selectedMessage previousRoot response64 other,
    ← PqxdhInitialNativeAuditCarried.carried_projection source writer sourcePre sourceApplication sourceInitializer
      sourceSelector sourceAux sourceMark sender route decode sourceExecution depth (depth + 1) (sourceInitial, []),
    prEvent_map] at bound
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun cut => Common selectedOwner number
    (PqxdhInitialNativeAuditCarried.eraseCut cut)) _ ?_).trans bound
  intro cut _ absent
  let : DecidablePred (fun value : Bool ⊕ PqxdhInitialPreparedParent.Pending extra M P I D K Bool Bool A N RootOracle.QueryCache S B =>
    value = Sum.inl true) := fun _ => Classical.propDecidable _
  cases cut with
  | complete result reached =>
      have denied : ¬ PqxdhInitialPublishedEvent.Gate selectedOwner number result := absent
      simp only [PqxdhInitialPreparedParent.collect, PqxdhInitialSourcePreparedSecrecy.observe,
        PqxdhInitialPublishedEvent.sourceDecision, PqxdhInitialPublishedEvent.sourceEvent, denied,
        false_and, decide_false, map_pure, prEvent_pure, Sum.inl.injEq, Bool.false_eq_true, ite_false]
  | pending context reached =>
      have missing : reached.1.1.1.2.1 (PqxdhInitialBuilderContext.address context.original) = none :=
        Classical.not_not.mp absent
      simp only [PqxdhInitialPreparedParent.collect, missing, ite_true, prEvent_pure,
        Sum.inr_ne_inl, ite_false]

end Source

/-- The complete actual one-start later sampler inherits the single common-event charge, at either selected role and every position beyond one. -/
theorem sample_one_common (depth qPost : Nat)
    (start : PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B))
    (position : start.1.number.val = depth + 2)
    (bounded : ∀ reply, (start.1.post reply).IsTotalQueryBound qPost) :
    𝒟[(fun value => @decide (value = Sum.inl true) (Classical.propDecidable _)) <$>
      PqxdhErasedParentSample.sampleOne source writer sender route decode depth start] {true} ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  exact prepared_common_risk source writer sender route decode start.1.selectedMessage (List.Vector.replicate 32 0)
    (PqxdhInitialSampledParent.response start) start.1.other start.1.index start.1.metadata
    { start.1.ready with root := List.Vector.replicate 32 0 } start.1.post start.1.before start.1.selected start.1.number
    start.1.shared start.1.privateState start.1.cache start.1.ancestors start.1.disclosed depth position qPost bounded

/-- Only inner completed/cached decisions are selected; the earlier root-preparation result is a separate mass term. -/
def innerCommon (packet : PqxdhErasedParentSample.Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
    (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) : Bool :=
  match packet with
  | .inr (_, .inl result) => result
  | _ => false

/-- Averaging over the original preparation and full initial64 draw retains every source branch and charges its inner common true mass once. -/
theorem sample_inner_common (depth qPost : Nat)
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (positions : ∀ input, Sum.inr input ∈ support prior → input.number.val = depth + 2)
    (bounded : ∀ input, Sum.inr input ∈ support prior → ∀ reply, (input.post reply).IsTotalQueryBound qPost) :
    𝒟[innerCommon <$> PqxdhErasedParentSample.sample source writer sender route decode depth prior] {true} ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  simp only [PqxdhErasedParentSample.sample]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun context reached => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun output _ => ?_
  cases context with
  | inl decision => simp only [prEvent_pure, innerCommon, Bool.false_eq_true, ite_false, zero_le]
  | inr input =>
      have bound := sample_one_common source writer sender route decode depth qPost (input, output)
        (positions input reached) (bounded input reached)
      rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map] at bound
      simp only [decide_eq_true_eq] at bound
      dsimp only
      rw [bind_pure_comp _ (PqxdhErasedParentSample.sampleOne source writer sender route decode depth (input, output)),
        prEvent_map]
      refine (prEvent_mono_of_support _ _ _ ?_).trans bound
      intro value _ winning
      cases value with
      | inl decision => exact congrArg Sum.inl winning
      | inr pending => cases winning

section Prepared
open PqxdhStatefulPhase1EufCma PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity
variable {baseSpec : OracleSpec ι} {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selectedOwner : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
local notation "actualPrior" => PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program post
  selectedOwner number ancestors disclosed
local notation "actualPostCap" certificate => PqxdhInitialPreparedSourceCaps.postCap env baseImpl kem program post certificate

/-- The authenticated source preparation supplies the selected position and original Post allowance. The resulting concrete common-mass bound adds no whole-observer or honest-target premise. -/
theorem authenticated_common (depth : Nat) (position : number.val = depth + 2)
    (certificate : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post) :
    𝒟[innerCommon <$> PqxdhErasedParentSample.sample env.source env.recordWriter env.senderId env.route env.decode depth actualPrior] {true} ≤
      ∑ j ∈ Finset.range (7 + (actualPostCap certificate) * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  apply sample_inner_common env.source env.recordWriter env.senderId env.route env.decode depth (actualPostCap certificate) actualPrior
  · exact fun input reached => (congrArg (fun value : Std.U64 => value.val)
      (PqxdhAuthenticatedEvolvingSecrecy.prior_position env baseImpl kem attachedVerify primitives program post
        selectedOwner number ancestors disclosed input reached)).trans position
  · exact fun input reached => (PqxdhInitialPreparedSourceCaps.supported_caps env baseImpl kem attachedVerify primitives
      program post certificate selectedOwner number ancestors disclosed input reached).postBound

end Prepared
end BeaconcryptCore.Computational.PqxdhLaterCommonRisk

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterCommonRisk.cached_beyond_cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterCommonRisk.cached_beyond_cursor

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterCommonRisk.carried_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterCommonRisk.carried_invariants

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterCommonRisk.complete_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterCommonRisk.complete_supported

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterCommonRisk.source_complete_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterCommonRisk.source_complete_risk

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterCommonRisk.source_common_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterCommonRisk.source_common_risk

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterCommonRisk.prepared_common_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterCommonRisk.prepared_common_risk

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterCommonRisk.sample_one_common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterCommonRisk.sample_one_common

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterCommonRisk.sample_inner_common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterCommonRisk.sample_inner_common

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterCommonRisk.authenticated_common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterCommonRisk.authenticated_common
