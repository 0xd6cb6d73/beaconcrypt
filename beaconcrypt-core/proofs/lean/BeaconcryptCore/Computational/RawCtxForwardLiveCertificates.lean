import BeaconcryptCore.Computational.RawCtxForwardTags
import BeaconcryptCore.Computational.RawCtxForwardRoleCertificates
import BeaconcryptCore.Computational.RawCtxForwardLive
import BeaconcryptCore.Computational.RawCtxFamilyHistoryBudget
import BeaconcryptCore.Computational.RawCtxCheckedBudgets
import BeaconcryptCore.Computational.RawCtxForwardParentSampler

/-!
The actual forward LIVE compiler certifies the exact descriptor it constructs. One residual source budget is shared with the already recorded disclosure history, so each original reveal is charged once. Certificates are proof metadata about carried data; no descriptor is selected by inverting a continuation.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardLiveCertificates
open RawCtxSelectedFamilyContext RawCtxForwardTags RawCtxFamilyResidualBudget
variable {M P I D K Result : Type} {S B : Nat}

abbrev Certificate (budget : Budget) (prior : List RatchetChain) (initialKnown : Nat)
    (context : Context M P I D K Result S B) : Prop :=
  ∃ residual : Budget, Below residual budget ∧ Fits residual context ∧
    (RawCtxFamilyFreshnessProxy.knownInputs prior (RawCtxFamilyStoppedResources.history context)).length + residual.2 ≤
      initialKnown + budget.2

/-- The same carried descriptor certificate transports through an earlier source prefix while preserving the single shared reveal allowance. -/
theorem certificate_mono (small large : Budget) (below : Below small large)
    (prior : List RatchetChain) (before after : Nat) (accounted : before + small.2 ≤ after + large.2)
    (context : Context M P I D K Result S B) (valid : Certificate small prior before context) :
    Certificate large prior after context := by
  obtain ⟨residual, smaller, fits, history⟩ := valid
  exact ⟨residual, ⟨fun kind => le_trans (smaller.1 kind) (below.1 kind), le_trans smaller.2 below.2⟩,
    fits, le_trans history accounted⟩

/-- The actual residual resource certificate also supplies the complete original source budget as a conservative bound for that exact descriptor. -/
theorem certificate_fits (budget : Budget) (prior : List RatchetChain) (initialKnown : Nat)
    (context : Context M P I D K Result S B) (valid : Certificate budget prior initialKnown context) :
    Fits budget context := by
  obtain ⟨residual, below, fits, _⟩ := valid
  exact fits_mono residual budget below context fits

private theorem program_of_family
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (familyQuiet : ∀ (request : (FamilySpec S B).Domain) (before : NativeFamily M P I D K S B),
      All RawCtxQuietFamilyTails.Quiet (RawCtxForwardFamily.program sender route decode
        ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _) before))
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (prior : List RatchetChain) (state : NativeLive M P I D K S B) :
    All (Certificate budget prior (RawCtxFamilyFreshnessProxy.knownInputs prior state.2).length)
      (RawCtxForwardLive.program sender route decode client state) := by
  induction client using OracleComp.inductionOn generalizing budget state with
  | pure value => trivial
  | query_bind request outside ih =>
    have tailBound : ∀ reply, RawCtxRevealBudgets.Bounded (outside reply) (RawCtxRevealBudgets.remaining request budget) := bounded.2
    have below := remaining_below request budget
    rw [RawCtxForwardLive.program_query]
    cases request with
    | inl request =>
      dsimp only
      change All _ (RawCtxForwardAnnotationLift.lift (fun inner => Context.family request state.2 outside inner)
        (RawCtxForwardFamily.program sender route decode ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _) state.1) >>=
          fun result => RawCtxForwardLive.program sender route decode (outside result.1)
            (result.2, RawCtxProtocolReveals.tick state.2))
      apply bind_all
      · apply lift_all RawCtxQuietFamilyTails.Quiet _ _ _ _ (familyQuiet request state.1)
        intro inner quiet
        refine ⟨RawCtxRevealBudgets.remaining (.inl request) budget, below, ?_, le_refl _⟩
        exact ⟨RawCtxRevealBudgets.remaining (.inl request) budget, ⟨fun _ => le_refl _, le_refl _⟩, tailBound, quiet⟩
      · intro result
        apply mono _ _ _ _ (ih result.1 _ (tailBound result.1) (result.2, RawCtxProtocolReveals.tick state.2))
        intro context valid
        exact certificate_mono _ budget below prior _ _ (le_refl _) context valid
    | inr request =>
      dsimp only
      rw [query_all]
      refine ⟨(fun _ impossible => by cases impossible), fun reply => ?_⟩
      apply mono _ _ _ _ (ih reply _ (tailBound reply) (state.1, RawCtxProtocolReveals.note ⟨request, reply⟩ state.2))
      intro context valid
      apply certificate_mono _ budget below prior _ _ _ context valid
      have growth := RawCtxFamilyFreshnessProxy.knownInputs_note_length prior state.2 ⟨request, reply⟩
      have positive : 0 < budget.2 := bounded.1
      simp only [RawCtxRevealBudgets.remaining]
      omega

/-- The exact carried certificate pays saved disclosures and later reads from one original allowance, including every finite-checker candidate. -/
theorem checked_candidates {PrimitiveState : Type}
    (handler : QueryImpl RawCtxSelectedLiveCompiler.Spec (StateT PrimitiveState ProbComp))
    (direct : RawCtxSelectedLiveCompiler.Spec.Domain → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (budget : Budget)
    (prior : List RatchetChain) (initialKnown : Nat) (valid : Certificate budget prior initialKnown context)
    (value : PqxdhOrderedChainHybrids.Material) (n : Nat)
    (earlier : List PqxdhSecretInputKdf.RootOutput) (state : PrimitiveState)
    (result : ((Result × RawCtxPendingFamilyLiveQueries.State RawCtxSelectedChain.Slot M P I D K S B) × List RawCtxSelectedChain.Slot) ×
      ((PrimitiveState × List PqxdhSecretInputKdf.RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ
      (RawCtxFlaggedQueryTrace.trace handler RawCtxSelectedLiveCompiler.inputs direct)
      (RawCtxCheckedBudgets.checkedStopped sender route decode context value n)).run
        ((state, RawCtxFamilyFreshnessProxy.knownInputs prior (RawCtxFamilyStoppedResources.history context) ++ earlier), false))) :
    result.2.1.2.length ≤ initialKnown + earlier.length +
      (254 + (budget.1 .send + 51 * budget.1 .raw) + budget.1 .hkdf + budget.2 + (n + 1)) := by
  obtain ⟨residual, below, fits, history⟩ := valid
  have cap := RawCtxCheckedBudgets.history_candidates handler direct sender route decode context residual fits value n
    prior earlier state result supported
  have send := below.1 .send
  have raw := below.1 .raw
  have hkdf := below.1 .hkdf
  omega

private theorem carried_of_all {A : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (RawCtxPendingSelectiveFamily.Spec S B).Domain → RawCtxSelectiveFamilyLog.LoggedState A → Bool)
    (selection : ∀ query reached, selected query reached = true → RawCtxPendingFamilyLiveTails.selected query = true)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B)
    (initial reached : RawCtxSelectiveFamilyLog.LoggedState A) (context : Context M P I D K Result S B)
    (predicate : Context M P I D K Result S B → Prop)
    (valid : All predicate (RawCtxForwardParentSampler.compiled sender route decode client state))
    (supported : RawCtxLoggedParentSampler.Cut.pending context reached ∈ support
      (RawCtxForwardParentSampler.carried source writer stage selected selection sender route decode client state initial)) :
    predicate context := by
  simp only [RawCtxForwardParentSampler.carried, support_map] at supported
  obtain ⟨cut, head, same⟩ := supported
  cases cut with
  | complete result final => cases same
  | pending saved final =>
      cases same
      exact scan_all RawCtxPendingFamilyLiveTails.selected selected selection
        (RawCtxSelectiveFamilyLog.handler source writer stage) predicate
        (RawCtxForwardParentSampler.compiled sender route decode client state)
        (RawCtxForwardLive.program_covered sender route decode client _) valid initial reached context head

/-- Every descriptor constructed by the actual bounded LIVE source carries its exact residual source budget and shares one reveal allowance with its saved original history. -/
theorem program_certificate
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (prior : List RatchetChain) (state : NativeLive M P I D K S B) :
    All (Certificate budget prior (RawCtxFamilyFreshnessProxy.knownInputs prior state.2).length)
      (RawCtxForwardLive.program sender route decode client state) := by
  apply program_of_family sender route decode _ client budget bounded prior state
  intro request before
  exact RawCtxForwardRoleCertificates.family_quiet sender route decode
    ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _)
    ⟨Nat.zero_lt_one, fun _ => True.intro⟩ before

/-- The actual executable carried sampler returns its own resource-certified descriptor, without replacing it by another frame-equivalent context. -/
theorem carried_certificate {A : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (RawCtxPendingSelectiveFamily.Spec S B).Domain → RawCtxSelectiveFamilyLog.LoggedState A → Bool)
    (selection : ∀ query reached, selected query reached = true → RawCtxPendingFamilyLiveTails.selected query = true)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (prior : List RatchetChain) (state : RawCtxProtocolReveals.State M P I D K S B)
    (initial reached : RawCtxSelectiveFamilyLog.LoggedState A) (context : Context M P I D K Result S B)
    (supported : RawCtxLoggedParentSampler.Cut.pending context reached ∈ support
      (RawCtxForwardParentSampler.carried source writer stage selected selection sender route decode client state initial)) :
    Certificate budget prior (RawCtxFamilyFreshnessProxy.knownInputs prior state.2).length context :=
  carried_of_all source writer stage selected selection sender route decode client state initial reached context _
    (program_certificate sender route decode client budget bounded prior _) supported

/-- The original first-hit/predecessor source sampler retains the same exact descriptor certificate on every supported pending result, including cached branches. -/
theorem first_certificate {A : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (prior : List RatchetChain) (state : RawCtxProtocolReveals.State M P I D K S B)
    (initial reached : RawCtxSelectiveFamilyLog.LoggedState A) (context : Context M P I D K Result S B)
    (supported : RawCtxLoggedParentSampler.Cut.pending context reached ∈ support
      (RawCtxForwardParentSampler.first source writer depth stage sender route decode client state initial)) :
    Certificate budget prior (RawCtxFamilyFreshnessProxy.knownInputs prior state.2).length context :=
  carried_certificate source writer stage _ _ sender route decode client budget bounded prior state initial reached context supported

end BeaconcryptCore.Computational.RawCtxForwardLiveCertificates
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.certificate_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.certificate_mono
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.certificate_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.certificate_fits

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.checked_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.checked_candidates

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.program_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.program_certificate
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.carried_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.carried_certificate
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.first_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLiveCertificates.first_certificate
