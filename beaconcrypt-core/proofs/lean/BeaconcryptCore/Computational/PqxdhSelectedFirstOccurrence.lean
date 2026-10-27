import BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence
import BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy

/-!
The actual initial builder and complete post-registration continuation preserve reverse private-cache provenance through every retained source callback. Consequently the prepared parent sampler's already-derived missing branch is the first global request for that address. This includes both paired roles and arbitrary interleaving; it does not assume that the chosen callback is a receive or exclude byte aliases with unrelated known keys.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSelectedFirstOccurrence
open PqxdhJointKdf PqxdhJointKdfGame PqxdhInitialBeaconAmbient PqxdhInitialNativeLog
open RawCtxSelectedFirstOccurrence (Recorded)
variable {ι M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

set_option backward.isDefEq.respectTransparency false in
/-- All original external callbacks retain the private cache and log; every live callback records its actual global private address. -/
theorem step_recorded (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (recorded : Recorded state.1)
    (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × State A N C)
    (supported : result ∈ support ((handler source writer stage external query).run state)) : Recorded result.2.1 := by
  cases query with
  | inl query =>
      rw [live_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, actual, rfl⟩ := supported
      exact RawCtxSelectedFirstOccurrence.step_recorded source writer stage query state.1 recorded reply actual
  | inr query =>
      rw [external_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, actual, rfl⟩ := supported
      exact recorded

/-- The complete source prefix retains every earlier private-request binding, including effects before the first builder returns. -/
theorem scan_recorded (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (selected : (Spec extra RatchetChain I D K X Response Shared S B).Domain → State A N C → Bool)
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : State A N C) (recorded : Recorded state.1)
    (result : RawCtxPendingMixedPrefix.Prefix (Spec extra RatchetChain I D K X Response Shared S B) Result (State A N C))
    (supported : result ∈ support (RawCtxStatefulPendingPrefix.scan selected (handler source writer stage external) client state)) :
    Recorded result.2.1 := by
  exact RawCtxStatefulPrefixInvariant.scan_valid selected (handler source writer stage external) (fun state => Recorded state.1)
    (fun query before valid _ reply head => step_recorded source writer stage external query before valid reply head)
    client state recorded result supported

/-- The literal carried source descriptor inherits reverse provenance without changing any saved continuation or state field. -/
theorem carried_recorded (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B) (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state reached : State A N C) (recorded : Recorded state.1)
    (context : PqxdhInitialNativeCarried.Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth stage external state)) :
    Recorded reached.1 := by
  have mapped : RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode)
      (RawCtxForwardScan.Cut.pending context reached) ∈ support
      (RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) <$>
        PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth stage external state) := by
    rw [support_map]
    exact ⟨RawCtxForwardScan.Cut.pending context reached, supported, rfl⟩
  rw [PqxdhInitialNativeCarried.carried_pack] at mapped
  exact scan_recorded source writer stage external (PqxdhInitialNativePrefix.selected (extra := extra) depth)
    (PqxdhInitialNativeCarried.original source mark sender route decode execution) state recorded _ mapped

section Actual
open PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
  (other : QueryImpl (External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache))
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
  (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
  (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
  (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
  (ancestors disclosed : List RatchetChain)
  (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache) (depth : Nat)

local notation "initial" => PqxdhInitialNativeInitializer.initial source selectedMessage previousRoot response64
local notation "mark" => PqxdhInitialSelectedOrigin.mark source selectedMessage
local notation "execution" => PqxdhInitialSourceExperiment.execution response64 index metadata ready post before
local notation "root" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected
local notation "state" => (PqxdhInitialSourceExperiment.initialState root shared privateState cache, ([] : List RootOutput))
local notation "sourceRun" => PqxdhInitialNativeAuditCarried.carried source writer
  (PqxdhInitialSourcePreparedSecrecy.pre other) (PqxdhInitialSourcePreparedSecrecy.application other) initial
  (PqxdhInitialSourcePreparedSecrecy.selector other) (PqxdhInitialSourcePreparedSecrecy.aux other)
  mark sender route decode execution depth (depth + 1) state
local notation "sourceSample" => PqxdhInitialSourcePreparedSecrecy.sample source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth

/-- The exact prepared source sampler stops before the first global occurrence of its selected predecessor address. Both paired roles remain in the saved continuation; known-key byte aliases are not excluded. -/
theorem actual_first (input : PqxdhInitialSupportedCertificate.Supported sourceRun)
    (supported : Sum.inr input ∈ support sourceSample) :
    PqxdhInitialBuilderContext.address input.val.1.original ∉ input.val.2.1.1.2 ∧
      input.val.2.1.1.1.2.1 (PqxdhInitialBuilderContext.address input.val.1.original) = none ∧
      RawCtxSelectiveChainGame.matched input.val.2.1.1.1.2.2 (PqxdhInitialBuilderContext.address input.val.1.original) = true ∧
      input.val.2.1.1.1.2.2.depth = depth := by
  have selectedFacts := PqxdhInitialSourcePreparedSecrecy.pending_selected source writer selectedMessage previousRoot response64 other
    sender route decode index metadata ready post before selected number ancestors disclosed shared privateState cache depth input supported
  have recorded := carried_recorded source writer mark sender route decode execution depth (depth + 1)
    (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other)
    (PqxdhInitialSourceExperiment.initialState root shared privateState cache) input.val.2.1
    (RawCtxSelectedFirstOccurrence.empty_recorded _) input.val.1
    (PqxdhInitialSourcePreparedSecrecy.supported_source source writer selectedMessage previousRoot response64 other sender route decode
      index metadata ready post before selected shared privateState cache depth input)
  exact ⟨RawCtxSelectedFirstOccurrence.missing_first input.val.2.1.1 recorded _ selectedFacts.1, selectedFacts⟩

end Actual

end BeaconcryptCore.Computational.PqxdhSelectedFirstOccurrence

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstOccurrence.step_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstOccurrence.step_recorded

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstOccurrence.scan_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstOccurrence.scan_recorded

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstOccurrence.carried_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstOccurrence.carried_recorded

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstOccurrence.actual_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstOccurrence.actual_first
