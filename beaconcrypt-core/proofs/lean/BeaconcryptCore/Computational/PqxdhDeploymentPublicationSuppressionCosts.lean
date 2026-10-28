-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized
import BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts
import BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts
import BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServiceCosts (Kind classify poolClass)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentPublicationSuppression (Selection)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- The selected bundle has precisely the original attempted-generation/signing service budget. -/
theorem bundle_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × Selection) (kind : Kind) :
    ((PqxdhDeploymentPublicationSuppressionSchedule.bundleClient (Response := Response) setup codec address).run state).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (PqxdhRegistrationJointServiceCosts.bundleCap kind) := by
  cases found : state.1[address]? with
  | none => simp only [PqxdhDeploymentPublicationSuppressionSchedule.bundleClient, StateT.run, found, isQueryBoundP_pure]
  | some entry =>
    simpa only [PqxdhDeploymentPublicationSuppressionSchedule.bundleClient, StateT.run, found,
      isQueryBoundP_map_iff, PqxdhRegistrationJointServiceLedger.pool_queries] using
      PqxdhDeploymentPublicationSuppression.client_queries setup codec entry.2.2 state.2 kind

/-- Additional private selection state emits no query while forwarding an unchanged source command. -/
theorem carry_bound (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response Result)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × Selection)
    (kind : Kind) (bound : Nat)
    (bounded : (work.run state.1).IsQueryBoundP (fun query => classify (KemSK := KemSK) query = kind) bound) :
    ((PqxdhDeploymentPublicationSuppressionSchedule.carry work).run state).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) bound := by
  have carried : (PqxdhDeploymentPublicationSuppressionSchedule.carry work).run state =
      (fun result => (result.1, (result.2, state.2))) <$> work.run state.1 := rfl
  simpa only [carried, isQueryBoundP_map_iff] using bounded

/-- Every source class retains the existing complete capability matrix on all typed replies. -/
theorem query_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × Selection) (kind : Kind) :
    ((PqxdhDeploymentPublicationSuppressionSchedule.handler setup codec query).run state).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind)
      (PqxdhRegistrationJointRevealCosts.cost kind (sourceKind (KemSK := KemSK) query)) := by
  rcases query with (coin | command) | read
  · exact carry_bound _ state kind _ (PqxdhRegistrationJointRevealCosts.query_bound setup codec _ state.1 kind)
  · cases command
    case bundle address => exact bundle_bound setup codec address state kind
    all_goals exact carry_bound _ state kind _ (PqxdhRegistrationJointRevealCosts.query_bound setup codec _ state.1 kind)
  · exact carry_bound _ state kind _ (PqxdhRegistrationJointRevealCosts.query_bound setup codec _ state.1 kind)

/-- Suppression preserves the original all-attempt capability ledger for every adaptive source client. -/
theorem program_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × Selection) (kind : Kind) :
    ((simulateQ (PqxdhDeploymentPublicationSuppressionSchedule.handler setup codec) program).run state).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind)
      (PqxdhRegistrationJointOpenCosts.oldBudget budget kind) := by
  rw [PqxdhRegistrationJointOpenCosts.oldBudget, ← PqxdhRegistrationJointRevealCosts.cost_total budget kind]
  exact FinitePartitionQueryBounds.weighted_bound (sourceKind (KemSK := KemSK))
    (PqxdhRegistrationJointRevealCosts.cost kind) budget
    (PqxdhDeploymentPublicationSuppressionSchedule.handler setup codec)
    (fun query => classify (KemSK := KemSK) query = kind) program certified
    (fun query before => query_bound setup codec query before kind) state

/-- Opening the actual native backend preserves all existing private capability caps. -/
theorem command_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (index : Nat) (publicIdentity : PublicIdentity)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × Selection) (native : NativeState KemSK)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((simulateQ (PqxdhRegistrationJointOpenBackend.impl setup codec checks index publicIdentity)
      ((simulateQ (PqxdhDeploymentPublicationSuppressionSchedule.handler setup codec) program).run state)).run native).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind)
      (PqxdhRegistrationJointOpenCosts.privateTotal budget kind) := by
  rw [← PqxdhRegistrationJointOpenCosts.private_total budget kind nonuniform]
  exact PqxdhRegistrationJointOpenCosts.backend_program setup codec checks index publicIdentity _
    (PqxdhRegistrationJointOpenCosts.oldBudget budget)
    (fun source => program_bound setup codec program budget certified state source) native kind nonuniform

/-- The real constructor contributes its single generated identity allowance; every modified command retains its previous private bill. -/
theorem open_initialized_private (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (PqxdhDeploymentPublicationSuppressionInitialized.client setup codec checks supplied ordinal program).IsQueryBoundP
      (fun query => PqxdhRegistrationJointOpenInitializedCosts.classify (KemSK := KemSK) query = some kind)
      ((if kind = .identityCreate ∧ supplied.isNone = true then 1 else 0) +
        PqxdhRegistrationJointOpenCosts.privateTotal budget kind) := by
  unfold PqxdhDeploymentPublicationSuppressionInitialized.client
  apply isQueryBoundP_bind (PqxdhRegistrationJointOpenInitializedCosts.constructor_private setup.serverKeyId supplied kind)
  rintro (_ | created) _
  · trivial
  · simpa only [isQueryBoundP_map_iff, PqxdhRegistrationJointOpenInitializedCosts.lifted_queries] using
      command_program setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
        program budget certified ([], Selection.initial ordinal)
        (PqxdhRegistrationJointInitializedAccept.initial created) kind nonuniform

/-- The ordinary generated-identity client uses the unchanged actual signing, converted-DH, creation and reveal caps. -/
theorem initialized_private (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (PqxdhDeploymentPublicationSuppressionInitialized.initialized setup codec checks ensureInit supplied ordinal program runtime).IsQueryBoundP
      (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = kind)
      ((if kind = .identityCreate ∧ supplied.isNone = true then 1 else 0) +
        PqxdhRegistrationJointOpenCosts.privateTotal budget kind) :=
  PqxdhRegistrationJointIdentityCosts.reduction_private setup ensureInit _ _ _ kind nonuniform _
    (open_initialized_private setup codec checks supplied ordinal program budget certified kind nonuniform)

/-- Suppression creates no runtime-initialization or known-seed-import call; the actual constructor supplies their original caps. -/
theorem initialized_local (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (kind : Bool) :
    (PqxdhDeploymentPublicationSuppressionInitialized.client setup codec checks supplied ordinal program).IsQueryBoundP
      (fun query => PqxdhRegistrationJointOpenInitializedCosts.localClass (KemSK := KemSK) query = some kind)
      (if kind then 1 else if supplied.isSome then 1 else 0) := by
  unfold PqxdhDeploymentPublicationSuppressionInitialized.client
  apply isQueryBoundP_bind (m := 0) (PqxdhRegistrationJointOpenInitializedCosts.constructor_local setup.serverKeyId supplied kind)
  rintro (_ | created) _
  · trivial
  · simpa only [isQueryBoundP_map_iff] using PqxdhRegistrationJointOpenInitializedCosts.lifted_local_free
      ((simulateQ (PqxdhRegistrationJointOpenBackend.impl setup codec checks
          created.server.server.metadata.identityIndex created.publicIdentity)
        ((simulateQ (PqxdhDeploymentPublicationSuppressionSchedule.handler setup codec) program).run
          ([], Selection.initial ordinal))).run (PqxdhRegistrationJointInitializedAccept.initial created)) kind

/-- Opening the modified handle schedule pays the unchanged actual native randomness matrix on every typed service reply. -/
theorem command_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (index : Nat) (publicIdentity : PublicIdentity)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × Selection) (native : NativeState KemSK) :
    ((simulateQ (PqxdhRegistrationJointOpenBackend.impl setup codec checks index publicIdentity)
      ((simulateQ (PqxdhDeploymentPublicationSuppressionSchedule.handler setup codec) program).run state)).run native).IsQueryBoundP
      (PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK)) (PqxdhRegistrationJointOpenUniform.total caps budget) := by
  rw [← PqxdhRegistrationJointOpenUniform.total_eq caps budget]
  exact PqxdhRegistrationJointOpenUniform.backend_program setup codec checks caps bounded index publicIdentity _
    (PqxdhRegistrationJointOpenCosts.oldBudget budget)
    (fun source => program_bound setup codec program budget certified state source) native

/-- The full modified constructor program charges both explicit source coin routes, independently of the identity challenger. -/
theorem initialized_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhDeploymentPublicationSuppressionInitialized.client setup codec checks supplied ordinal program).IsQueryBoundP
      (PqxdhRegistrationJointOpenInitializedUniform.IsCoin (KemSK := KemSK))
      (PqxdhRegistrationJointOpenUniform.total caps budget) := by
  unfold PqxdhDeploymentPublicationSuppressionInitialized.client
  rw [← Nat.zero_add (PqxdhRegistrationJointOpenUniform.total caps budget)]
  apply isQueryBoundP_bind (n := 0) (PqxdhRegistrationJointOpenInitializedUniform.constructor_coins setup.serverKeyId supplied)
  rintro (_ | created) _
  · trivial
  · simpa only [isQueryBoundP_map_iff, PqxdhRegistrationJointOpenInitializedUniform.lifted_coins] using
      command_coins setup codec checks caps bounded created.server.server.metadata.identityIndex created.publicIdentity
        program budget certified ([], Selection.initial ordinal) (PqxdhRegistrationJointInitializedAccept.initial created)

/-- The modified executable constructor satisfies every coordinate of the existing complete compiler partition. -/
theorem initialized_allowances (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source)) (kind : Kind ⊕ Bool) :
    (PqxdhDeploymentPublicationSuppressionInitialized.client setup codec checks supplied ordinal program).IsQueryBoundP
      (fun query => PqxdhRegistrationJointIdentityUniform.classify (KemSK := KemSK) query = kind)
      (PqxdhRegistrationJointIdentityUniform.allowances caps supplied budget kind) := by
  cases kind with
  | inl kind =>
      by_cases uniform : kind = .uniform
      · subst kind
        exact (isQueryBoundP_congr_pred PqxdhRegistrationJointIdentityUniform.classify_coin).mpr
          (initialized_coins setup codec checks caps bounded supplied ordinal program budget certified)
      · have prior := open_initialized_private setup codec checks supplied ordinal program budget certified kind uniform
        have transferred := IsQueryBoundP.of_imp
          (fun query => PqxdhRegistrationJointIdentityUniform.classify_private query kind uniform) prior
        cases kind <;> first | exact (uniform rfl).elim | exact transferred
  | inr kind =>
      have prior := initialized_local setup codec checks supplied ordinal program kind
      have transferred := (isQueryBoundP_congr_pred
        (fun query => PqxdhRegistrationJointIdentityUniform.classify_local query kind)).mpr prior
      cases kind <;> exact transferred

/-- The ordinary client retains the complete all-reply uniform allowance, including local KEM/base work and runtime initialization. -/
theorem initialized_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhDeploymentPublicationSuppressionInitialized.initialized setup codec checks ensureInit supplied ordinal program runtime).IsQueryBoundP
      (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = .uniform)
      (PqxdhRegistrationJointIdentityUniform.total caps qInit budget) := by
  apply PqxdhRegistrationJointIdentityCosts.route_program
  rw [← PqxdhRegistrationJointIdentityUniform.total_eq caps qInit supplied budget]
  exact FinitePartitionQueryBounds.weighted_bound (PqxdhRegistrationJointIdentityUniform.classify (KemSK := KemSK))
    (PqxdhRegistrationJointIdentityUniform.cost caps qInit)
    (PqxdhRegistrationJointIdentityUniform.allowances caps supplied budget)
    (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit)
    (fun query => PqxdhRegistrationJointIdentityCosts.sourceKind query = some .uniform)
    (PqxdhDeploymentPublicationSuppressionInitialized.client setup codec checks supplied ordinal program)
    (initialized_allowances setup codec checks caps bounded supplied ordinal program budget certified)
    (fun query state => PqxdhRegistrationJointIdentityUniform.compiler_step setup ensureInit qInit initBound caps bounded query state)
    (PqxdhLiveKemBirth.empty, runtime)

/-- Every ordinary query predicate is unchanged by the source client's transparent report compiler. -/
theorem sourceClient_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (predicate : PqxdhDynamicIdentityPool.DynamicSpec.Domain → Prop) [DecidablePred predicate] (bound : Nat)
    (bounded : (PqxdhDeploymentPublicationSuppressionInitialized.initialized setup codec checks ensureInit supplied ordinal program runtime).IsQueryBoundP predicate bound) :
    (PqxdhDeploymentPublicationSuppressionInitialized.sourceClient setup codec checks ensureInit supplied ordinal program runtime).IsQueryBoundP
      (PqxdhJointPhase1Reports.SourceClass predicate) bound := by
  rw [← PqxdhDeploymentPublicationSuppressionInitialized.sourceClient_erase setup codec checks ensureInit supplied ordinal program runtime] at bounded
  have lifted := (PqxdhRegistrationJointReportCosts.erase_bound predicate _ bound).mp bounded
  exact (isQueryBoundP_congr_pred (fun query => by cases query <;> rfl)).mp lifted

/-- The public report-game source client has the unchanged all-attempt signing, converted-DH, creation and reveal bills. -/
theorem sourceClient_private (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (PqxdhDeploymentPublicationSuppressionInitialized.sourceClient setup codec checks ensureInit supplied ordinal program runtime).IsQueryBoundP
      (PqxdhJointPhase1Reports.SourceClass (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = kind))
      ((if kind = .identityCreate ∧ supplied.isNone = true then 1 else 0) +
        PqxdhRegistrationJointOpenCosts.privateTotal budget kind) :=
  sourceClient_bound setup codec checks ensureInit supplied ordinal program runtime _ _
    (initialized_private setup codec checks ensureInit supplied ordinal program runtime budget certified kind nonuniform)

/-- The creation count includes the genuine generated Server identity and every generated owner. -/
theorem sourceClient_creates (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhDeploymentPublicationSuppressionInitialized.sourceClient setup codec checks ensureInit supplied ordinal program runtime).IsQueryBoundP
      (PqxdhJointPhase1Reports.SourceClass PqxdhDynamicIdentityPool.IsCreate)
      ((if supplied.isNone then 1 else 0) + budget (.inl 1)) := by
  have bounded := sourceClient_private setup codec checks ensureInit supplied ordinal program runtime budget certified .identityCreate (by decide)
  simp only [PqxdhRegistrationJointOpenCosts.privateTotal, true_and] at bounded
  apply (isQueryBoundP_congr_pred (p := PqxdhJointPhase1Reports.SourceClass
    (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = .identityCreate)) ?_).mp bounded
  rintro (query | report)
  · rcases query with coin | request
    · simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind, PqxdhDynamicIdentityPool.IsCreate]
    · cases request with
      | create => simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind, PqxdhRegistrationJointServiceCosts.poolClass, PqxdhDynamicIdentityPool.IsCreate]
      | reveal index => simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind, PqxdhRegistrationJointServiceCosts.poolClass, PqxdhDynamicIdentityPool.IsCreate]
      | service index request =>
          cases request <;> simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind, PqxdhRegistrationJointServiceCosts.poolClass, PqxdhDynamicIdentityPool.IsCreate]
  · rfl

/-- Suppression and public reporting add no randomness to the complete syntactic ordinary-client uniform allowance. -/
theorem sourceClient_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhDeploymentPublicationSuppressionInitialized.sourceClient setup codec checks ensureInit supplied ordinal program runtime).IsQueryBoundP
      (PqxdhJointPhase1Reports.SourceClass (PqxdhDynamicIdentityRouting.dynamicClass
        (PqxdhJointIdentityFamily.IsClass .uniform)))
      (PqxdhRegistrationJointIdentityUniform.total caps qInit budget) :=
  sourceClient_bound setup codec checks ensureInit supplied ordinal program runtime _ _
    ((isQueryBoundP_congr_pred PqxdhRegistrationJointNativeOriginUniform.uniform_class).mp
      (initialized_uniform setup codec checks ensureInit qInit initBound caps bounded supplied ordinal program runtime budget certified))

/-- A source program with no private reads remains unread after selection, suppression, native compilation and ordinary identity routing. -/
theorem sourceClient_unread (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (identityReads : budget (.inr 0) = 0) (kemReads : budget (.inr 1) = 0) :
    (PqxdhDeploymentPublicationSuppressionInitialized.sourceClient setup codec checks ensureInit supplied ordinal program runtime).IsQueryBoundP
      (PqxdhJointPhase1Reports.SourceClass (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = .other)) 0 := by
  have bounded := sourceClient_private setup codec checks ensureInit supplied ordinal program runtime budget certified .other (by decide)
  simpa only [PqxdhRegistrationJointOpenCosts.privateTotal, identityReads, kemReads,
    reduceCtorEq, false_and, ite_false, Nat.zero_add, Nat.add_zero] using bounded

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.bundle_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.carry_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.carry_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.program_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.command_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.command_program

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.open_initialized_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.open_initialized_private

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.initialized_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.initialized_private

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.initialized_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.initialized_local

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.command_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.command_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.initialized_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.initialized_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.initialized_allowances' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.initialized_allowances

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.initialized_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.initialized_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.sourceClient_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.sourceClient_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.sourceClient_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.sourceClient_private

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.sourceClient_creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.sourceClient_creates

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.sourceClient_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.sourceClient_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.sourceClient_unread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts.sourceClient_unread
