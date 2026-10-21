import BeaconcryptCore.Computational.PqxdhInitialPreparedResources
import BeaconcryptCore.Computational.PqxdhInitialCounterBudget

/-!
The full original prefix bounds its actual chronological private-input list before the parent draw. That list and the current parent address give an explicit input-collision charge for the prepared comparison, including repeated and failed derivations. No child cache-miss assumption is added to the security contract.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPreparedRisk
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialNativeLog
variable {ι M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The actual stopped source prefix cannot append more chronological inputs than its original all-reply callback budget. -/
theorem scan_length (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (selected : (Spec extra RatchetChain I D K X Response Shared S B).Domain → State A N C → Bool)
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (budget : Nat) (bounded : client.IsTotalQueryBound budget) (state : State A N C)
    (result : RawCtxPendingMixedPrefix.Prefix (Spec extra RatchetChain I D K X Response Shared S B) Result (State A N C))
    (supported : result ∈ support (RawCtxStatefulPendingPrefix.scan selected
      (handler source writer stage external) client state)) :
    result.2.1.2.length ≤ state.1.2.length + budget := by
  induction client using OracleComp.inductionOn generalizing budget state with
  | pure value =>
    simp only [RawCtxStatefulPendingPrefix.scan_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    cases chosen : selected query state with
    | true =>
      rw [RawCtxStatefulPendingPrefix.scan_cut selected _ query next state chosen, mem_support_pure_iff] at supported
      subst result
      exact Nat.le_add_right _ _
    | false =>
      rw [RawCtxStatefulPendingPrefix.scan_other selected _ query next state chosen, mem_support_bind_iff] at supported
      obtain ⟨reply, first, rest⟩ := supported
      rw [isTotalQueryBound_query_bind_iff] at bounded
      have step := (PqxdhInitialCounterBudget.step_length source writer stage external query state reply first).2
      have tail := ih reply.1 (budget - 1) (bounded.2 reply.1) reply.2 rest
      omega

/-- The complete actual builder/post descriptor sampler inherits its source callback allowance and retains the same chronological log. -/
theorem carried_length (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
    (depth stage qPost : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state reached : State A N C)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth stage external state)) :
    reached.1.2.length ≤ state.1.2.length + (7 + qPost * 67) := by
  have packed : RawCtxForwardScan.pack
      (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode)
      (.pending context reached) ∈ support
      (RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) <$>
        PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth stage external state) := by
    rw [support_map]
    exact ⟨.pending context reached, supported, rfl⟩
  rw [PqxdhInitialNativeCarried.carried_pack] at packed
  exact scan_length source writer stage external (PqxdhInitialNativePrefix.selected depth)
    (PqxdhInitialNativeCarried.original source mark sender route decode execution) (7 + qPost * 67)
    (PqxdhInitialOriginPost.sequence_total source execution.initial mark execution.origin sender route decode
      execution.index execution.metadata execution.ready execution.outside qPost bounded (execution.before, execution.trace))
    state _ packed

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
  (depth : Nat) (state : PqxdhInitialNativeAudit.State A N C)

local notation "sourceRun" => PqxdhInitialNativeAuditCarried.carried source writer pre application initializer selector aux
  mark sender route decode execution depth (depth + 1) state

/-- The proof-annotated actual pending descriptor carries a chronological log bounded by the same complete source allowance. -/
theorem supported_length (qPost : Nat) (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (input : PqxdhInitialSupportedCertificate.Supported sourceRun) :
    input.val.2.1.1.2.length ≤ state.1.1.2.length + (7 + qPost * 67) := by
  apply carried_length source writer mark sender route decode execution depth (depth + 1) qPost
    (PqxdhInitialNativeAudit.external pre application initializer selector aux) bounded state.1 input.val.2.1 input.val.1
  rw [← PqxdhInitialNativeAuditCarried.carried_projection source writer pre application initializer selector aux
    mark sender route decode execution depth (depth + 1) state, support_map]
  exact ⟨.pending input.val.1 input.val.2, input.property, rfl⟩

def addresses : Bool ⊕ PqxdhInitialSupportedCertificate.Supported sourceRun → List JointKdfAddress
  | .inl _ => []
  | .inr input => input.val.2.1.1.2 ++ [PqxdhInitialBuilderContext.address input.val.1.original]

/-- The candidate addresses contain the entire actual earlier private-input log and the current unexecuted parent input, each explicitly counted. -/
theorem addresses_length (qPost : Nat) (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (input : Bool ⊕ PqxdhInitialSupportedCertificate.Supported sourceRun) :
    (addresses source writer pre application initializer selector aux mark sender route decode execution depth state input).length ≤
      state.1.1.2.length + (7 + qPost * 67) + 1 := by
  cases input with
  | inl result => exact Nat.zero_le _
  | inr input =>
    simpa only [addresses, List.length_append, List.length_singleton] using
      Nat.add_le_add_right
        (supported_length source writer pre application initializer selector aux mark sender route decode execution depth state
          qPost bounded input) 1

private theorem target_address (target : RootOutput) :
    RawCtxSelectedParentPrivatePatch.targetAddress target = RawCtxFirstParentRisk.inputAddress target := by
  change (⟨_, (RawCtxSelectedQueryTrace.rootVector (RawCtxFreshChainCut.concreteChain target)).toList⟩ : JointKdfAddress) = _
  rw [RawCtxSelectedQueryTrace.rootVector_concrete]
  exact congrArg (fun info => (⟨info, target.toList⟩ : JointKdfAddress))
    (by simpa only [RawCtxChainSend.nativeRequest, FixedHkdfDomain.info, pqxdh.SYM_RATCHET_INFO] using PqxdhRefinement.absBytes_SYM_RATCHET_INFO)

/-- The exact prepared prefix and full76 parent draw charge all prior-input collisions plus the parent self-address by their concrete original log allowance. -/
theorem collision_bound
    (observe : PqxdhInitialPreparedParent.Output M P I D K Result Origin A N C S B → ProbComp Bool)
    (qPost : Nat) (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost) :
    Pr[fun pair => RawCtxSelectedParentPrivatePatch.targetAddress pair.2 ∈
      addresses source writer pre application initializer selector aux mark sender route decode execution depth state pair.1.1 |
      RawCtxSelectedParentCandidates.sample
        (PqxdhInitialPreparedResources.sample source writer pre application initializer selector aux mark sender route decode
          observe execution depth state)
        (PqxdhInitialPreparedResources.address source writer pre application initializer selector aux mark sender route decode execution depth state)] ≤
      ((state.1.1.2.length + (7 + qPost * 67) + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  unfold RawCtxSelectedParentCandidates.sample
  apply probEvent_bind_le_of_forall_le
  intro context _
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, target_address]
  exact (RawCtxFirstParentRisk.full_inputs_vcvioLegacy _).trans (mul_le_mul_left
    (Nat.cast_le.mpr (addresses_length source writer pre application initializer selector aux mark sender route decode
      execution depth state qPost bounded context)) _)

/-- Every private-cache binding at the actual supported source cut is represented in its chronological log. -/
theorem supported_covered (covered : PqxdhInitialNativeLog.Covered state.1)
    (input : PqxdhInitialSupportedCertificate.Supported sourceRun) :
    PqxdhInitialNativeLog.Covered input.val.2.1 := by
  apply PqxdhInitialNativeCarried.carried_covered source writer mark sender route decode execution depth (depth + 1)
    (PqxdhInitialNativeAudit.external pre application initializer selector aux) state.1 input.val.2.1 covered input.val.1
  rw [← PqxdhInitialNativeAuditCarried.carried_projection source writer pre application initializer selector aux
    mark sender route decode execution depth (depth + 1) state, support_map]
  exact ⟨.pending input.val.1 input.val.2, input.property, rfl⟩

/-- Outside the charged prior-input event, the actual child address is absent from the retained cache and differs from the current parent address. -/
theorem safe_pending (covered : PqxdhInitialNativeLog.Covered state.1)
    (input : PqxdhInitialSupportedCertificate.Supported sourceRun) (target : RootOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress target ∉
      addresses source writer pre application initializer selector aux mark sender route decode execution depth state (.inr input)) :
    input.val.2.1.1.1.2.1 (RawCtxSelectedParentPrivatePatch.targetAddress target) = none ∧
      RawCtxSelectedParentPrivatePatch.targetAddress target ≠ PqxdhInitialBuilderContext.address input.val.1.original ∧
      RawCtxSelectedParentPrivatePatch.targetAddress target ∉ input.val.2.1.1.2 := by
  have absent : RawCtxSelectedParentPrivatePatch.targetAddress target ∉ input.val.2.1.1.2 ∧
      RawCtxSelectedParentPrivatePatch.targetAddress target ≠ PqxdhInitialBuilderContext.address input.val.1.original := by
    simpa only [addresses, List.mem_append, List.mem_singleton, not_or] using safe
  refine ⟨?_, absent.2, absent.1⟩
  cases found : input.val.2.1.1.1.2.1 (RawCtxSelectedParentPrivatePatch.targetAddress target) with
  | none => rfl
  | some output =>
    exact False.elim (absent.1 (supported_covered source writer pre application initializer selector aux mark sender route decode
      execution depth state covered input _ output found))

end BeaconcryptCore.Computational.PqxdhInitialPreparedRisk

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.scan_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.scan_length
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.carried_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.carried_length
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.supported_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.supported_length
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.addresses_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.addresses_length
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.collision_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.supported_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.supported_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.safe_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedRisk.safe_pending
