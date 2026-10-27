import BeaconcryptCore.Computational.PqxdhInitialPreparedParent
import BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate
import BeaconcryptCore.Computational.RawCtxFirstParentRisk

/-!
Forward support annotation converts the actual prepared source sampler into the supported ordinary continuation without changing common decisions, saved descriptors, reached state, query syntax or missing-cache selection. The source-derived certificate and original sampler bill are then consumed directly. A separate self-address collision term accounts for the current parent input, which was not an earlier executed query and need not have been disclosed.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialPreparedResources
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialSupportedCertificate
variable {ι M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (observe : PqxdhInitialPreparedParent.Output M P I D K Result Origin A N C S B → ProbComp Bool)
  (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
  (depth : Nat) (state : PqxdhInitialNativeAudit.State A N C)

local notation "prepared" => PqxdhInitialPreparedParent.prepare source writer pre application initializer selector aux
  mark sender route decode observe execution depth state
local notation "sourceRun" => PqxdhInitialNativeAuditCarried.carried source writer pre application initializer selector aux
  mark sender route decode execution depth (depth + 1) state

def pending (input : RawCtxSupportedSample.Pending prepared) : Supported sourceRun :=
  ⟨input.val, ((PqxdhInitialPreparedParent.supported_pending source writer pre application initializer selector aux
    mark sender route decode observe execution depth state input.val.2 input.val.1).mp input.property).1⟩

noncomputable def sample : ProbComp (Bool ⊕ Supported sourceRun) :=
  Sum.map id (pending source writer pre application initializer selector aux mark sender route decode observe execution depth state) <$>
    RawCtxSupportedSample.sum prepared

/-- Forgetting only the proof annotation returns the exact original prepared source sampler, with the same common bits and complete reached states. -/
theorem sample_erase : Sum.map id Subtype.val <$>
    sample source writer pre application initializer selector aux mark sender route decode observe execution depth state = prepared := by
  rw [sample, Functor.map_map]
  convert RawCtxSupportedSample.sum_erase prepared using 1
  congr 1
  funext value
  cases value <;> rfl


/-- Original common and pending source continuations receive exactly the same runtime value after the support annotation. -/
theorem sample_run {Result' : Type}
    (next : Bool ⊕ PqxdhInitialPreparedParent.Pending extra M P I D K Result Origin A N C S B → ProbComp Result') :
    (sample source writer pre application initializer selector aux mark sender route decode observe execution depth state >>=
      fun value => next (Sum.map id Subtype.val value)) = prepared >>= next := by
  rw [← bind_map_left, sample_erase]


/-- Proof annotation retains the original source-derived prepared sampler bill, including common completed continuations and the final source observation. -/
theorem sample_uniform (qPost qObserve : Nat)
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (costs : PqxdhInitialParentObserverBudgets.Costs)
    (callbacks : PqxdhInitialParentObserverBudgets.ExternalUniform costs pre application initializer selector aux)
    (observeBound : ∀ result, (observe result).IsTotalQueryBound qObserve) :
    (sample source writer pre application initializer selector aux mark sender route decode observe execution depth state).IsTotalQueryBound
      (PqxdhInitialAuditedResources.uniformBudget costs qPost + qObserve) := by
  apply (isQueryBound_map_iff _ (Sum.map id Subtype.val) _ _ _).mp
  rw [sample_erase]
  exact PqxdhInitialPreparedParent.prepare_uniform source writer pre application initializer selector aux mark sender route decode observe
    execution depth qPost qObserve bounded costs callbacks observeBound state


/-- Every supported pending result still has the actual missing private entry; proof annotation does not add cached or unreachable branches. -/
theorem sample_missing (input : Supported sourceRun)
    (supported : Sum.inr input ∈ support
      (sample source writer pre application initializer selector aux mark sender route decode observe execution depth state)) :
    input.val.2.1.1.1.2.1 (PqxdhInitialBuilderContext.address input.val.1.original) = none := by
  apply ((PqxdhInitialPreparedParent.supported_pending source writer pre application initializer selector aux
    mark sender route decode observe execution depth state input.val.2 input.val.1).mp ?_).2
  rw [← sample_erase source writer pre application initializer selector aux mark sender route decode observe execution depth state,
    support_map]
  exact ⟨Sum.inr input, supported, rfl⟩



/-- The exact prepared sampler's supported carrier directly instantiates the actual stopped observer certificate and both complete resource bills. -/
theorem pending_resources (qPost : Nat)
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (costs : PqxdhInitialParentObserverBudgets.Costs)
    (callbacks : PqxdhInitialParentObserverBudgets.ExternalUniform costs pre application initializer selector aux)
    (disclosed : List RatchetChain) (remaining : Nat)
    (event : Supported sourceRun × RawCtxSelectedParentEntry.Entry →
      PqxdhInitialParentStoppedHop.Trace M P I D K A N C Result Origin S B → Prop)
    (context : Supported sourceRun × RawCtxSelectedParentEntry.Entry) (output : FullOutput) :
    let next := continuation source pre application initializer selector aux sourceRun disclosed remaining event
    let work := PqxdhInitialParentStoppedHop.observed source writer mark sender route decode next context output
    work.IsTotalQueryBound ((2 * (255 + qPost * 67) + (remaining + 1)) * costs.cap) ∧
      ∀ result, result ∈ support work → (PqxdhInitialParentStoppedHop.candidates result).length ≤
        priorBudget execution qPost state disclosed + 3 * (2 * (255 + qPost * 67) + (remaining + 1)) :=
  observer_resources source writer pre application initializer selector aux mark sender route decode execution depth (depth + 1)
    qPost state bounded disclosed remaining costs callbacks event context output

private theorem target_address (target : RootOutput) :
    RawCtxSelectedParentPrivatePatch.targetAddress target = RawCtxFirstParentRisk.inputAddress target := by
  change (⟨_, (RawCtxSelectedQueryTrace.rootVector (RawCtxFreshChainCut.concreteChain target)).toList⟩ : JointKdfAddress) = _
  rw [RawCtxSelectedQueryTrace.rootVector_concrete]
  exact congrArg (fun info => (⟨info, target.toList⟩ : JointKdfAddress))
    (by simpa only [RawCtxChainSend.nativeRequest, FixedHkdfDomain.info, pqxdh.SYM_RATCHET_INFO] using PqxdhRefinement.absBytes_SYM_RATCHET_INFO)


/-- The pending branch retains its exact source parent address; the common branch has no source parent and uses an unused fixed comparison address. -/
def address : Bool ⊕ Supported sourceRun → JointKdfAddress
  | .inl _ => FixedHkdfDomain.ratchet.address []
  | .inr input => PqxdhInitialBuilderContext.address input.val.1.original

/-- The current parent input receives its own exact full76-draw collision charge. It is not assumed to appear in an earlier query or disclosure list. -/
theorem parent_collision :
    Pr{let pair ← (RawCtxSelectedParentCandidates.sample
        (sample source writer pre application initializer selector aux mark sender route decode observe execution depth state)
        (address source writer pre application initializer selector aux mark sender route decode execution depth state))}[RawCtxSelectedParentPrivatePatch.targetAddress pair.2 = pair.1.2.address] ≤
      (2 ^ 256 : ENNReal)⁻¹ := by
  unfold RawCtxSelectedParentCandidates.sample
  have split : ∀ {Context Value : Type} (prior : ProbComp Context) (draw : Context → ProbComp Value)
      (q : Value → Prop) (ε : ENNReal),
      (∀ context, Pr{let y ← draw context}[q y] ≤ ε) → Pr{let y ← prior >>= draw}[q y] ≤ ε :=
    fun prior draw q ε h => prEvent_bind_le_of_forall_le prior draw q h
  refine split _ _ _ _ fun context => ?_
  have bound := RawCtxFirstParentRisk.full_inputs [address source writer pre application initializer selector aux mark sender route decode execution depth state context]
  simp only [List.length_singleton, Nat.cast_one, one_mul] at bound
  generalize sampled : ($ᵗ FullOutput : ProbComp FullOutput) = block at bound ⊢
  rw [bind_pure_comp _ block, prEvent_map]
  refine (prEvent_congr _ _ _ fun output => ?_).trans_le bound
  simp only [RawCtxSelectedParentEntry.fromOutput, target_address, List.mem_cons, List.not_mem_nil, or_false]

end BeaconcryptCore.Computational.PqxdhInitialPreparedResources


/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedResources.sample_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedResources.sample_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedResources.sample_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedResources.sample_run

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedResources.sample_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedResources.sample_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedResources.sample_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedResources.sample_missing

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedResources.pending_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedResources.pending_resources

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedResources.parent_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedResources.parent_collision
