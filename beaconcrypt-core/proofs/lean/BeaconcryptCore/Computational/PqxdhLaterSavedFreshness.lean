import BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison
import BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked

/-! The original finite checker includes the selected record material key even when no further chain step remains. Its exact value and interpreted reveal history supply the saved continuation's hidden-disclosure condition; no stronger freshness premise is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedFreshness
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open PqxdhSelectedFirstRecord PqxdhFirstRecordConfidentiality
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The final actual checker contains both the selected input and its exact record key, with the same full-response nonce/next-chain coordinates retained. -/
theorem checker_material (prior : Prior) (parent : Entry) (target key : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) :
    (PqxdhInitialParentStoppedHop.checkerTrace prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next) (some 0)).map
        (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain target)) =
      [RawCtxFreshChainCut.concreteChain target, RawCtxFreshChainCut.concreteChain key] := by
  simp only [PqxdhInitialParentStoppedHop.checkerTrace, RawCtxFiniteLineageCheck.trace,
    RawCtxFiniteLineageCheck.routedStep, RawCtxSelectedParentTable.step,
    RawCtxSelectedMessageKdf.decoded_response, List.map_cons, List.map_nil]
  rfl

/-- The original zero-remaining native decision already forbids a returned selected skipped key. This implication uses its actual checker key and interpreted source history, not chain-only freshness. -/
theorem native_good (prior : Prior) (parent : Entry) (target key : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (earlier ancestors disclosed : List RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (result : Bool × Traced M P I D K A N C S B)
    (accepted : PqxdhInitialNativeParentEvent.nativeDecision prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next) 0 earlier ancestors disclosed selected number
      (result.1, (tracedProj key result.2).1) = true) :
    PqxdhSelectedPostDisclosure.Good result.2.1 := by
  simp only [PqxdhInitialNativeParentEvent.nativeDecision, decide_eq_true_eq,
    checker_material] at accepted
  have fresh : RawCtxLiveLineage.Fresh [RawCtxFreshChainCut.concreteChain key] disclosed
      (RawCtxSelectedMessageFreshness.interpretHistory key result.2.1.1.roles.2) := by
    intro value member
    obtain rfl := List.mem_singleton.mp member
    exact accepted.2 _ (by simp)

  exact ((RawCtxSelectedMessageFreshness.fresh_factor key [] disclosed result.2.1.1.roles.2).mp fresh).1

/-- The original native publication/freshness decision on the interpreted source result. The outer option continues to distinguish compiler refusal from an ordinary false decision. -/
def Event (prior : Prior) (parent : Entry) (target key : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (earlier ancestors disclosed : List RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (result : Option Bool × Traced M P I D K A N C S B) : Prop :=
  ∃ bit, result.1 = some bit ∧ PqxdhInitialNativeParentEvent.nativeDecision prior parent target
    (RawCtxSelectedMessageKdf.response key nonce next) 0 earlier ancestors disclosed selected number
    (bit, (tracedProj key result.2).1) = true

/-- The literal original event supplies the hidden-disclosure condition on every state, without any reachability or cryptographic assumption. -/
theorem event_good (prior : Prior) (parent : Entry) (target key : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (earlier ancestors disclosed : List RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (result : Option Bool × Traced M P I D K A N C S B)
    (accepted : Event prior parent target key nonce next earlier ancestors disclosed selected number result) :
    PqxdhSelectedPostDisclosure.Good result.2.1 := by
  obtain ⟨bit, _, accepted⟩ := accepted
  exact native_good prior parent target key nonce next earlier ancestors disclosed selected number (bit, result.2) accepted

section Comparison
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (monitor : Fin B) (qPost : Nat)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Bool S B)
    (material : PqxdhOrderedChainHybrids.Material)
    (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C))
local notation "parent" => Entry.mk (PqxdhInitialBuilderContext.address context.original) material

/-- The exact original native event in the complete saved continuation is bounded by its compiled event plus the same-run nonce-refusal term. Original finite key freshness discharges the disclosure condition internally. -/
theorem source_bound (earlier ancestors disclosed : List RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) :
    𝒟[(fun result => (by classical exact decide (Event prior parent target key nonce next earlier ancestors disclosed selected number result))) <$>
      PqxdhLaterSavedPostComparison.original pre application initial selector aux fixed writer prior key target nonce next
        mark sender route read qPost context material fits state] {true} ≤
    𝒟[(fun result => (by classical exact decide (Event prior parent target key nonce next earlier ancestors disclosed selected number (result.1, insProject result.2)))) <$>
      PqxdhLaterSavedPostComparison.compiled pre application initial selector aux fixed writer prior key target nonce next
        mark sender route read monitor qPost context material fits state] {true} +
    𝒟[(fun result => result.2.2 && (by classical exact decide (Event prior parent target key nonce next earlier ancestors disclosed selected number (result.1, insProject result.2.1)))) <$>
      PqxdhLaterSavedPostComparison.flagged pre application initial selector aux fixed writer prior key target nonce next
        mark sender route read monitor qPost context material fits state] {true} := by
  classical
  have factor : ∀ result : Option Bool × Traced M P I D K A N C S B,
      (Event prior parent target key nonce next earlier ancestors disclosed selected number result ∧
        PqxdhSelectedPostDisclosure.Good result.2.1) ↔
      Event prior parent target key nonce next earlier ancestors disclosed selected number result :=
    fun result => ⟨And.left, fun enabled => ⟨enabled,
      event_good prior parent target key nonce next earlier ancestors disclosed selected number result enabled⟩⟩
  simpa only [factor] using PqxdhLaterSavedPostComparison.source_bound pre application initial selector aux fixed writer
    prior key target nonce next mark sender route read monitor qPost context material fits state
      (Event prior parent target key nonce next earlier ancestors disclosed selected number)

end Comparison
end BeaconcryptCore.Computational.PqxdhLaterSavedFreshness

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedFreshness.checker_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedFreshness.checker_material
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedFreshness.native_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedFreshness.native_good
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedFreshness.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedFreshness.event_good
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedFreshness.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedFreshness.source_bound
