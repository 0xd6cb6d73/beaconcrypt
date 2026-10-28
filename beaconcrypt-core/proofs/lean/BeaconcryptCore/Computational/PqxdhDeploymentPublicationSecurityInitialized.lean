-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityDomination
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor

/-! Actual constructor initialization, including its failed-runtime branch, preserves the concrete one-sided full-run coupling. The selected event is measured on the unrestricted final real transcript, and the genuine modified program supplies the ordinary fresh-field event. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityInitialized
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentPublicationSecurityCoupling
open PqxdhDeploymentPublicationSecurityDomination (CapturedCandidate)
open PqxdhDeploymentPublicationSecurityFresh (SourceEvent)
open PqxdhDeploymentPublicationSecuritySelection (SelectedEvent)
variable {ι KemSK Reader Response Result A X : Type} {baseSpec : OracleSpec ι}

def CapturedEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (ordinal : Nat)
    (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (outcome : Option (PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK Result) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A) : Prop :=
  ∃ created result state, outcome.1 = some (created, result, state) ∧
    CapturedCandidate setup codec ordinal transcript (result, state)

private theorem captured_some (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (ordinal : Nat)
    (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (result : Result) (state : RealState KemSK)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    CapturedEvent setup codec ordinal transcript (some (created, result, state), after) ↔
      CapturedCandidate setup codec ordinal transcript (result, state) := by
  constructor
  · rintro ⟨created', result', state', present, event⟩
    obtain ⟨sameCreated, sameRest⟩ := Prod.mk.inj (Option.some.inj present)
    obtain ⟨sameResult, sameState⟩ := Prod.mk.inj sameRest
    subst created'
    subst result'
    subst state'
    exact event
  · intro event
    exact ⟨created, result, state, rfl, event⟩

private theorem source_some (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (result : Result) (state : ModifiedState KemSK)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    SourceEvent setup codec transcript (some (created, result, state), after) ↔
      PqxdhDeploymentPublicationSecurityFresh.NativeEvent setup codec transcript (result, state) := by
  constructor
  · rintro ⟨created', result', state', present, event⟩
    obtain ⟨sameCreated, sameRest⟩ := Prod.mk.inj (Option.some.inj present)
    obtain ⟨sameResult, sameState⟩ := Prod.mk.inj sameRest
    subst created'
    subst result'
    subst state'
    exact event
  · intro event
    exact ⟨created, result, state, rfl, event⟩

/-- The same real constructor draw initializes both complete adaptive programs; false initialization retains its actual reached runtime and contributes no fresh-candidate event. -/
theorem initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (client : OracleComp (Spec KemSK) Result) (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    Pr{let observed ← (PqxdhDeploymentPublicationSecurityMonitor.initialized setup codec checks ensureInit supplied ordinal client state)}[
      observed.2 = true ∧ CapturedEvent setup codec ordinal transcript observed.1] ≤
    Pr{let outcome ← ((PqxdhDeploymentPublicationSuppressionInitialized.source setup codec checks ensureInit supplied ordinal client).run state)}[
      SourceEvent setup codec transcript outcome] := by
  unfold PqxdhDeploymentPublicationSecurityMonitor.initialized
    PqxdhDeploymentPublicationSuppressionInitialized.source
  simp only [StateT.run]
  apply prEvent_bind_mono_of_forall_le_of_support
  rintro ⟨(_ | created), born⟩ _
  · simp [CapturedEvent, SourceEvent]
  · have dominated := PqxdhDeploymentPublicationSecurityDomination.program setup codec checks created.seed
      created.server.server.metadata.identityIndex ordinal transcript client
      (PqxdhRegistrationJointSchedule.initial born.1 (PqxdhRegistrationSchedule.initial created).shared,
        PqxdhDeploymentPublicationSuppressionTrace.Audit.empty)
      (PqxdhRegistrationJointSchedule.initial born.1 (PqxdhRegistrationSchedule.initial created).shared,
        PqxdhDeploymentPublicationSuppression.Selection.initial ordinal)
      (initial ordinal _)
    simp only [prEvent_map]
    apply le_trans ?_ (le_trans dominated ?_)
    · apply le_of_eq
      apply prEvent_congr
      rintro ⟨⟨result, state⟩, clean⟩
      simp only [captured_some]
    · apply le_of_eq
      apply prEvent_congr
      rintro ⟨result, state⟩
      exact (source_some setup codec transcript (PqxdhRegistrationJointServerBirth.encode created) result state
        (state.1.pool, born.2)).symm

/-- The actual unrestricted selected event is bounded by the genuine modified initialized execution. There is no cleanliness or first-attempt freshness premise: the same-source monitor derives them. -/
theorem selected (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (ordinal : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary) (runtime : A) :
    Pr{let outcome ← (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode adversary runtime)}[
      SelectedEvent setup codec ordinal outcome] ≤
    Pr{let outcome ← ((PqxdhDeploymentPublicationSuppressionInitialized.source setup codec checks ensureInit none ordinal
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))}[
      SourceEvent setup codec (fun result => result.1.2.transcript) outcome] := by
  have erased := PqxdhDeploymentPublicationSecurityMonitor.initialized_erasure setup codec checks ensureInit none ordinal
    (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  unfold PqxdhDeploymentPublicationSecurityAudit.actual
  rw [← erased, prEvent_map]
  apply le_trans ?_ (initialized setup codec checks ensureInit none ordinal (fun result => result.1.2.transcript)
    (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))
  apply prEvent_mono_of_support
  intro observed supported event
  have clean := PqxdhDeploymentPublicationSecurityMonitor.selected_clean setup codec checks route ensureInit ordinal
    bounds mode adversary runtime observed supported event
  refine ⟨clean, ?_⟩
  obtain ⟨created, result, state, present, target, good, chosen⟩ := event
  have actual : observed.1 ∈ support (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit
      bounds mode adversary runtime) := by
    change observed.1 ∈ support ((PqxdhDeploymentPublicationSecurityAudit.initialized setup codec checks ensureInit none
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))
    rw [← erased, support_map]
    exact ⟨observed, supported, rfl⟩
  have successful : (some (created, result, state), observed.1.2) ∈ support
      (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode adversary runtime) := by
    simpa only [← present, Prod.mk.eta] using actual
  have valid := (PqxdhDeploymentPublicationSecurityAudit.actual_audit setup codec checks route ensureInit bounds mode
    adversary budget respects runtime (created, result, state) observed.1.2 successful).1
  exact ⟨created, result, state, present, target,
    PqxdhDeploymentPublicationSecurityMonitor.goodTarget_captured state.2 valid ordinal target good, chosen⟩

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityInitialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityInitialized.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityInitialized.initialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityInitialized.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityInitialized.selected
