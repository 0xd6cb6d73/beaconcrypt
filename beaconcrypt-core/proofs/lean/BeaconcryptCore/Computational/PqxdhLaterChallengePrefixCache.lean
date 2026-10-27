import BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication
import BeaconcryptCore.Computational.PqxdhInitialSourcePublication

/-! Preserve the established finite source-cache publication paths along the actual wrapper prefix. The candidate audit is projected only for applying the existing native path theorem; the reached frontend, trace and complete backend remain the original ones. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache
open PqxdhInitialPostContext PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhRecordConfidentialityChallenge PqxdhRecordConfidentialityTrace
open PqxdhFirstRecordConfidentiality (AdvSpec)
variable {ι M P I D K X Response A N Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (Ambient A N RootOracle.QueryCache))
    (application : Response → Ambient A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (Ambient A N RootOracle.QueryCache))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N RootOracle.QueryCache))
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
local notation "initial" => PqxdhInitialNativeInitializer.initial source selectedMessage previousRoot response
local notation "native" => PqxdhInitialNativeAudit.handler (S := S) (B := B) source writer stage pre application initial selector aux
local notation "external" => PqxdhInitialNativeAudit.external pre application initial selector aux
local notation "mark" => PqxdhInitialSelectedOrigin.mark source selectedMessage
local notation "Snapshot" => NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B
local notation "Backend" => PqxdhInitialNativeAudit.State A N RootOracle.QueryCache
local notation "Full" => Snapshot × Backend
local notation "postImpl" => PqxdhLaterChallengeCutChronology.postImpl mark sender route decode native

private theorem external_initial :
    PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response external = external := by
  funext query
  rcases query with query | (reply | (secrets | (query | query))) <;> rfl

/-- The original complete Post under the audited source retains the same finite-cache publication invariant. The actual initializer discharges its source law, while every other callback and state component remains arbitrary. -/
theorem program_invariant (serverRoot : RootOutput) (owner : RawCtxProtocolReveals.Owner S B)
    (client : OracleComp (PostSpec extra S B) Result) (before : Snapshot) (state : Backend)
    (valid : PqxdhInitialOriginPostPath.Invariant
      (PqxdhInitialOriginPostPath.rootFor serverRoot previousRoot response owner) owner before state.1)
    (result : (Result × Snapshot) × Backend)
    (supported : result ∈ support ((simulateQ native
      ((simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) client).run before)).run state)) :
    PqxdhInitialOriginPostPath.Invariant
      (PqxdhInitialOriginPostPath.rootFor serverRoot previousRoot response owner) owner result.1.2 result.2.1 := by
  apply PqxdhInitialOriginPostPath.program_invariant source writer stage selectedMessage previousRoot response
    external serverRoot owner sender route decode client before state.1 valid (result.1, result.2.1)
  simp only [PqxdhInitialOriginPostPath.program, external_initial]
  rw [← PqxdhInitialNativeAudit.program_erase source writer stage pre application initial selector aux, support_map]
  exact ⟨result, supported, rfl⟩

/-- Every actually reached wrapper request retains the finite-cache path invariant from its real initial Builder state. This forward induction includes all complete preceding callbacks and does not infer an earlier marker from a final state. -/
theorem reaches_invariant (serverRoot : RootOutput) (owner : RawCtxProtocolReveals.Owner S B)
    (number : U64) (bit : Bool) (client rest : OracleComp (AdvSpec extra S B) Result)
    (before current : State) (ambient reached : Full)
    (traced : Reaches postImpl owner number bit client before ambient rest current reached)
    (valid : PqxdhInitialOriginPostPath.Invariant
      (PqxdhInitialOriginPostPath.rootFor serverRoot previousRoot response owner) owner ambient.1 ambient.2.1) :
    PqxdhInitialOriginPostPath.Invariant
      (PqxdhInitialOriginPostPath.rootFor serverRoot previousRoot response owner) owner reached.1 reached.2.1 := by
  induction traced with
  | here => exact valid
  | later query next before ambient step rest current reached actual tail ih =>
      apply ih
      rw [PqxdhLaterChallengeCutChronology.post_program, support_map] at actual
      obtain ⟨completed, supported, rfl⟩ := actual
      exact program_invariant source writer stage selectedMessage previousRoot response pre application selector aux
        sender route decode serverRoot owner ((handler owner number bit query).run before)
        ambient.1 ambient.2 valid completed supported

/-- The literal supplied initializer and first Builder establish the finite-cache invariant from their empty origin trace. Initialization is supplied by the existing typed source constructor, including failed Builder outcomes. -/
theorem builder_invariant (owner : RawCtxProtocolReveals.Owner S B)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (before : NativeFront M P I D K S B) (state : Backend)
    (result : (PqxdhInitialBuilderContext.BuildResult × Snapshot) × Backend)
    (supported : result ∈ support ((simulateQ native (simulateQ RawCtxForwardAnnotation.erase
      (PqxdhInitialOriginForwardBuilder.program source mark true sender route decode
        (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response)
        index metadata ready pure before PqxdhInitialSourcePublication.empty))).run state)) :
    PqxdhInitialOriginPostPath.Invariant
      (PqxdhInitialSourceExperiment.root source previousRoot response owner) owner result.1.2 result.2.1 := by
  apply PqxdhInitialSourcePublication.sequence_invariant source writer stage selectedMessage previousRoot response
    external (PqxdhInitialSourceExperiment.server source response)
    (PqxdhInitialSourceExperiment.server_created source response) owner sender route decode index metadata ready
    pure before state.1 (result.1, result.2.1)
  simp only [PqxdhInitialSourcePublication.sequence, external_initial]
  rw [← PqxdhInitialNativeAudit.program_erase source writer stage pre application initial selector aux, support_map]
  refine ⟨result, ?_, rfl⟩
  simpa only [PqxdhInitialOriginForwardBuilder.program_erase] using supported

/-- Every actual audited callback retains the same prior private bindings, including external callbacks and reached initializer work. -/
theorem query_extends (query : (Base extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared S B).Domain)
    (before : Backend)
    (result : (Base extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared S B).Range query × Backend)
    (supported : result ∈ support ((native query).run before)) :
    RawCtxCursorLineage.Extends before.1.1.1.2.1 result.2.1.1.1.2.1 := by
  apply PqxdhInitialNativePath.step_extends source writer stage external query before.1 (result.1, result.2.1)
  rw [← PqxdhInitialNativeAudit.query_erase source writer stage pre application initial selector aux, support_map]
  exact ⟨result, supported, rfl⟩

/-- The actual callback-local scanner retains an already executed publication path through every request before its saved cut. It uses the same finite cache throughout. -/
theorem pending_cached {Tag : Type}
    (privateQuery : (Base extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared S B).Domain → Bool)
    (selected : (Base extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared S B).Domain → Backend → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (frame : Tag → RawCtxForwardAnnotation.Frame
      (Base extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared S B) Result)
    (work : OracleComp (RawCtxForwardAnnotation.Spec Tag
      (Base extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared S B)) Result)
    (covered : RawCtxForwardCoverage.Covered privateQuery work)
    (sound : RawCtxForwardAnnotation.Sound frame work)
    (before after : Backend) (tag : Tag)
    (supported : RawCtxForwardScan.Cut.pending tag after ∈ support
      (RawCtxForwardScan.scan privateQuery selected selection native work covered before))
    (root : RootOutput) (number : U64) (cached : RawCtxSourcePublishedPath.Cached root number before.1.1.1.2.1) :
    RawCtxSourcePublishedPath.Cached root number after.1.1.1.2.1 := by
  apply RawCtxStatefulPrefixInvariant.scan_valid selected native
    (fun state => RawCtxSourcePublishedPath.Cached root number state.1.1.1.2.1)
    (fun query current valid _ reply head => RawCtxSourcePublishedPath.cached_extends root number _ _ valid
      (query_extends source writer stage selectedMessage previousRoot response pre application selector aux query current reply head))
    (simulateQ RawCtxForwardAnnotation.erase work) before cached
    (RawCtxForwardScan.pack frame (.pending tag after))
  rw [← RawCtxForwardScan.scan_pack privateQuery selected selection native frame work covered sound before, support_map]
  exact ⟨.pending tag after, supported, rfl⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache.program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache.program_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache.reaches_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache.reaches_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache.builder_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache.builder_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache.query_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache.query_extends
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache.pending_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache.pending_cached
