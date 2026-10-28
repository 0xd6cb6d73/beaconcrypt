-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityInitialized
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound

/-! Unrestricted final published-tuple provenance and replay bounds for the actual complete deployment experiment. Failed Fresh bundle writes remain in the real execution and its signing history. An original unissued field uses the existing A2 family; an already-issued unpublished one-time field uses the genuine selected-call suppression family indexed by the original all-attempt bundle cap. No no-failure, honest-partner, failure-independence or event-containment premise is added. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentPublicationSecurityEvents (GameEvent OwnerEvent ReplayEvent)
open PqxdhDeploymentPublicationSecuritySelection (OrdinaryEvent SelectedEvent)
open PqxdhDeploymentPublicationSecurityFresh (SourceEvent)
open PqxdhDeploymentCompileSecrecy (compileFull)
open PqxdhDeploymentCompileCaps (transported compile_full_certified)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- A selected ordinal is a fixed family index, and the only challenger key is the generated identity selected by the existing ordinary joint-use reduction. -/
noncomputable def reduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (count ordinal : Nat) (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : Forgery) (target : Fin (count + 1)) :=
  PqxdhDeploymentPublicationSecurityReduction.reduction setup.joint count
    (PqxdhDeploymentPublicationSecurityBills.client setup codec checks route ensureInit bounds mode adversary count
      ordinal runtime) fallback ordinaryFallback target

/-- The complete finite ordinary joint-use advantage sum: the existing A2 family and one selected-call family per original bundle position. -/
noncomputable def totalAdvantage (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) : ENNReal :=
  (∑ target : Fin (budget.create + 1), advantage setup.joint
    (PqxdhDeploymentProvenance.reduction setup codec checks route ensureInit bounds mode adversary budget.create
      runtime fallback ordinaryFallback target)) +
  ∑ selected : Fin budget.bundle, ∑ target : Fin (budget.create + 1), advantage setup.joint
    (reduction setup codec checks route ensureInit bounds mode adversary budget.create selected.val runtime fallback
      ordinaryFallback target)

/-- The exact original per-reduction bills hold for both finite families, including all reserved identity-seed draws and the challenger's own seed. -/
def FamilyBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) : Prop :=
  (∀ target : Fin (budget.create + 1), PqxdhDeploymentPublicationSecurityReduction.Bills setup.joint budget.create
    (PqxdhDeploymentProvenance.client setup codec checks route ensureInit bounds mode adversary (budget.create + 1)
      runtime) fallback ordinaryFallback (3 * budget.bundle) (budget.finish + budget.accept)
    (PqxdhRegistrationJointIdentityUniform.total caps qInit (transported bounds budget)) target) ∧
  (∀ (selected : Fin budget.bundle) (target : Fin (budget.create + 1)),
    PqxdhDeploymentPublicationSecurityReduction.Bills setup.joint budget.create
      (PqxdhDeploymentPublicationSecurityBills.client setup codec checks route ensureInit bounds mode adversary
        budget.create selected.val runtime) fallback ordinaryFallback (3 * budget.bundle) (budget.finish + budget.accept)
      (PqxdhRegistrationJointIdentityUniform.total caps qInit (transported bounds budget)) target)

/-- Every one selected real final event is bounded by the ordinary generated-identity sum for its concrete modified client. The original all-reply cap discharges every creation and private-read obligation. -/
theorem selected_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (ordinal : Nat) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    Pr{let outcome ← (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode adversary runtime)}[
      SelectedEvent setup codec ordinal outcome] ≤
      ∑ target : Fin (budget.create + 1), advantage setup.joint
        (reduction setup codec checks route ensureInit bounds mode adversary budget.create ordinal runtime fallback
          ordinaryFallback target) := by
  apply (PqxdhDeploymentPublicationSecurityInitialized.selected setup codec checks route ensureInit ordinal bounds mode
    adversary budget respects runtime).trans
  simpa only [reduction, PqxdhDeploymentPublicationSecurityBills.client,
    PqxdhDeploymentPublicationSecurityBills.transcript, PqxdhDeploymentPublicationSecurityBills.source] using
    PqxdhDeploymentPublicationSecuritySource.source_bound setup codec checks ensureInit ordinal budget.create
      (compileFull setup codec route bounds mode adversary) runtime (transported bounds budget)
      (compile_full_certified setup codec route bounds mode adversary budget respects) (by rfl) (by rfl)
      (by simp [transported, Nat.add_comm]) (fun result => result.1.2.transcript) fallback ordinaryFallback

/-- CE-A2pub without a bundle-failure restriction: the actual final published-tuple event is bounded by the original ordinary A2 family plus one ordinary joint-use family for every global bundle-call position. Every failed write and every actual native/private/runtime field remains in the original experiment. -/
theorem published_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    Pr{let outcome ← ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime)}[
      GameEvent setup codec outcome] ≤
      (∑ target : Fin (budget.create + 1), advantage setup.joint
        (PqxdhDeploymentProvenance.reduction setup codec checks route ensureInit bounds mode adversary budget.create
          runtime fallback ordinaryFallback target)) +
      ∑ selected : Fin budget.bundle, ∑ target : Fin (budget.create + 1), advantage setup.joint
        (reduction setup codec checks route ensureInit bounds mode adversary budget.create selected.val runtime fallback
          ordinaryFallback target) := by
  rw [← PqxdhDeploymentPublicationSecurityAudit.actual_deployment setup codec checks route ensureInit phase1 phase2
    bounds mode adversary runtime, prEvent_map]
  have split := PqxdhDeploymentPublicationDomination.finite_or_selection_bound budget.bundle
    (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode adversary runtime)
    (fun outcome => GameEvent setup codec (PqxdhDeploymentPublicationSecurityAudit.deployment outcome))
    (OrdinaryEvent setup codec) (fun selected => SelectedEvent setup codec selected.val)
    (PqxdhDeploymentPublicationWitnessEvents.actual_cover setup codec checks shortRejects phase1 route ensureInit bounds
      mode adversary budget respects runtime)
    (fun selected => (PqxdhDeploymentPublicationSuppressionInitialized.source setup codec checks ensureInit none selected.val
      (compileFull setup codec route bounds mode adversary)).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))
    (fun _ => SourceEvent setup codec (fun result => result.1.2.transcript))
    (fun selected => PqxdhDeploymentPublicationSecurityInitialized.selected setup codec checks route ensureInit selected.val
      bounds mode adversary budget respects runtime)
  apply split.trans
  apply add_le_add
  · exact PqxdhDeploymentPublicationOrdinaryBound.ordinary_bound setup codec checks route ensureInit bounds mode adversary
      budget respects runtime fallback ordinaryFallback
  · apply Finset.sum_le_sum
    intro selected _
    simpa only [reduction, PqxdhDeploymentPublicationSecurityBills.client,
      PqxdhDeploymentPublicationSecurityBills.transcript, PqxdhDeploymentPublicationSecurityBills.source] using
      PqxdhDeploymentPublicationSecuritySource.source_bound setup codec checks ensureInit selected.val budget.create
        (compileFull setup codec route bounds mode adversary) runtime (transported bounds budget)
        (compile_full_certified setup codec route bounds mode adversary budget respects) (by rfl) (by rfl)
        (by simp [transported, Nat.add_comm]) (fun result => result.1.2.transcript) fallback ordinaryFallback

/-- The same unrestricted provenance bound applies to each actual created owner's final published-tuple failure. -/
theorem owner_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A) (owner : Nat)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    Pr{let outcome ← ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime)}[
      OwnerEvent setup codec owner outcome] ≤
      totalAdvantage setup codec checks route ensureInit bounds mode adversary budget runtime fallback ordinaryFallback := by
  apply le_trans (prEvent_mono _ _ _ fun outcome happened =>
    (PqxdhDeploymentPublicationSecurityEvents.game_owner setup codec outcome).mpr ⟨owner, happened⟩)
  exact published_bound setup codec checks shortRejects phase1 phase2 route ensureInit bounds mode adversary budget
    respects runtime fallback ordinaryFallback

/-- CE-R1' without a bundle-failure restriction. Actual registration consumption puts a repeated successful acceptance inside the unrestricted final published-tuple event. -/
theorem replay_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    Pr{let outcome ← ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime)}[
      ReplayEvent setup codec outcome] ≤
      totalAdvantage setup codec checks route ensureInit bounds mode adversary budget runtime fallback ordinaryFallback :=
  (prEvent_mono_of_support _ _ _ fun outcome supported happened =>
    PqxdhDeploymentPublicationSecurityEvents.replay_published setup codec checks route ensureInit 0 bounds mode adversary
      runtime outcome supported happened).trans
    (published_bound setup codec checks shortRejects phase1 phase2 route ensureInit bounds mode adversary
      budget respects runtime fallback ordinaryFallback)

/-- Both ordinary families pay at most three signatures per real bundle call, one converted-DH request per finish/accept, and the complete previous uniform allowance. The number of selected clients is exactly the public bundle cap. -/
theorem family_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (kemBound : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    FamilyBills setup codec checks route ensureInit qInit caps bounds mode adversary budget runtime fallback ordinaryFallback := by
  constructor
  · intro target
    exact PqxdhDeploymentProvenance.a2_bills setup codec checks route ensureInit qInit initBound caps kemBound bounds mode
      adversary budget respects runtime fallback ordinaryFallback target
  · intro selected target
    exact PqxdhDeploymentPublicationSecurityBills.bills setup codec checks route ensureInit qInit initBound caps kemBound
      bounds mode adversary budget respects selected.val runtime fallback ordinaryFallback target

/-- Unrestricted CE-A2pub together with exact bills for every ordinary joint-use reduction of both families. -/
theorem published_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (kemBound : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (Pr{let outcome ← ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime)}[
      GameEvent setup codec outcome] ≤
      totalAdvantage setup codec checks route ensureInit bounds mode adversary budget runtime fallback ordinaryFallback) ∧
    FamilyBills setup codec checks route ensureInit qInit caps bounds mode adversary budget runtime fallback ordinaryFallback :=
  ⟨published_bound setup codec checks shortRejects phase1 phase2 route ensureInit bounds mode adversary budget respects
    runtime fallback ordinaryFallback,
    family_bills setup codec checks route ensureInit qInit initBound caps kemBound bounds mode adversary budget respects
      runtime fallback ordinaryFallback⟩

/-- Unrestricted CE-R1' together with the same exact per-reduction bills; failed Fresh writers are included throughout. -/
theorem replay_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (kemBound : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (Pr{let outcome ← ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime)}[
      ReplayEvent setup codec outcome] ≤
      totalAdvantage setup codec checks route ensureInit bounds mode adversary budget runtime fallback ordinaryFallback) ∧
    FamilyBills setup codec checks route ensureInit qInit caps bounds mode adversary budget runtime fallback ordinaryFallback :=
  ⟨replay_bound setup codec checks shortRejects phase1 phase2 route ensureInit bounds mode adversary budget respects
    runtime fallback ordinaryFallback,
    family_bills setup codec checks route ensureInit qInit initBound caps kemBound bounds mode adversary budget respects
      runtime fallback ordinaryFallback⟩

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.selected_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.selected_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.published_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.published_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.owner_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.replay_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.replay_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.family_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.family_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.published_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.published_billed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.replay_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity.replay_billed
