-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler
import BeaconcryptCore.Computational.RegistrationNativeBuildCosts
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendRequestBounds
/-! Shared CTX bills are derived from the actual corrected Server branch. Pure public allocation and signer draws retain their separate coin branches. Only unchanged peer-insertion syntax reuses its existing literal cost proof. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerHashBounds
open RegistrationNativePlatformEffectCompiler (Spec)
open RegistrationNativePlatformEffectHashBounds (IsHash Bounded)
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_run weighted_indicator)
variable {n : Nat} {E Platform A B S : Type}
private def hashCost (query : (Spec n).Domain) := if IsHash query then 1 else 0
private theorem indicator {I : Type} {spec : OracleSpec I} (predicate : I → Prop) [DecidablePred predicate]
    (work : OracleComp spec A) (cap : Nat)
    (bounded : Weighted (fun query => if predicate query then 1 else 0) work cap) : work.IsQueryBoundP predicate cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => trivial
  | query_bind query next ih =>
    rw [Weighted, isQueryBound_query_bind_iff] at bounded
    rw [isQueryBoundP_query_bind_iff]
    constructor
    · by_cases selected : predicate query
      · simp only [selected, ite_true] at bounded
        exact Or.inr (by omega)
      · exact Or.inl selected
    · intro reply
      by_cases selected : predicate query
      · simpa only [selected, ite_true] using ih reply _ (bounded.2 reply)
      · simpa only [selected, ite_false, Nat.sub_zero] using ih reply _ (bounded.2 reply)

private theorem effect (query : (EnvEffects n).Domain) (before : S) :
    ((RegistrationNativePlatformEffectCompiler.effect query).run before).IsQueryBoundP IsHash
      (RegistrationNativeBuildCosts.envCost .hash query) := by
  cases query with
  | inl coin =>
    simp only [RegistrationNativePlatformEffectCompiler.effect, StateT.run_lift, bind_pure_comp,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsHash, RegistrationNativeBuildCosts.envCost, effectKind]
    exact fun impossible => impossible.elim
  | inr query =>
    cases query <;> simp only [RegistrationNativePlatformEffectCompiler.effect, StateT.run_lift, bind_pure_comp,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsHash, RegistrationNativeBuildCosts.envCost, effectKind] <;> first | exact fun impossible => impossible.elim | decide +revert

private theorem env_program (work : OracleComp (EnvEffects n) A)
    (bounded : Weighted (RegistrationNativeBuildCosts.envCost .hash) work 0) :
    Bounded (simulateQ (RegistrationNativePlatformEffectCompiler.effect (Platform := S)) work) 0 := by
  intro before
  apply indicator IsHash _ 0
  exact weighted_run (RegistrationNativeBuildCosts.envCost .hash) hashCost
    RegistrationNativePlatformEffectCompiler.effect work 0 before bounded (fun query previous => by
      have actual := weighted_indicator IsHash 1 _ _ (effect query previous)
      simp only [Nat.one_mul] at actual
      convert actual using 1; rfl)

private theorem bind_bound (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (first later : Nat)
    (bounded : Bounded work first) (rest : ∀ value, Bounded (next value) later) : Bounded (work >>= next) (first + later) := by
  intro before
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (bounded before) (fun result _ => rest result.1 result.2)

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

private theorem continuation (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (work : OracleComp (EnvEffects n) A) :
    simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output)
      (simulateQ RegistrationNativePlatformPairedServerCompiler.forward work) =
        simulateQ RegistrationNativePlatformEffectCompiler.effect work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun implementation => simulateQ implementation work)
  funext query
  simp only [QueryImpl.apply_compose, RegistrationNativePlatformPairedServerCompiler.forward,
    simulateQ_spec_query, RegistrationNativePlatformPairedServerCompiler.target]

/-- The complete actual known or hidden Server service has a finite shared-hash bill, including failed source publication and native installation branches. -/
theorem branch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) :
    Bounded (RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice) 4 := by
  cases choice with
  | known output =>
    unfold RegistrationNativePlatformServerRestrictedService.branch RegistrationNativePlatformPairedServerCompiler.known
    dsimp only
    rw [simulateQ_bind, simulateQ_spec_query]
    apply bind_bound _ _ 4 0
    · exact RegistrationNativePlatformEffectHashBounds.publication_with_record source view failure allocation erased helper sign writer initial output
    · intro published
      rw [continuation]
      exact env_program _ (RegistrationNativeBuildCosts.known_after_bound control published .hash)
  | hidden reference =>
    unfold RegistrationNativePlatformServerRestrictedService.branch RegistrationNativePlatformPairedServerCompiler.hidden
    dsimp only
    rw [simulateQ_bind, simulateQ_spec_query]
    apply bind_bound _ _ 4 0
    · exact RegistrationNativePlatformEffectHashBounds.publication_with_record source view failure allocation erased helper sign writer initial _
    · intro published
      rw [continuation]
      exact env_program _ (RegistrationNativeBuildCosts.hidden_after_bound control reference.slot published .hash)

def IsFrontendHash : (RegistrationNativePlatformServerFrontendCompiler.Spec n).Domain → Prop
  | .inl _ => False
  | .inr query => IsHash query
instance : DecidablePred (IsFrontendHash (n := n)) := fun query => by
  cases query with
  | inl query => simp only [IsFrontendHash]; infer_instance
  | inr query => exact inferInstanceAs (Decidable (IsHash query))
private def frontCost (query : (RegistrationNativePlatformServerFrontendCompiler.Spec n).Domain) :=
  if IsFrontendHash query then 1 else 0
private def FrontBound {X : Type} (work : StateT (RegistrationNativePlatformBoundCompiler.PublicState Platform)
    (OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n)) X) (cap : Nat) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP IsFrontendHash cap
omit primitive in
private theorem embedded (work : OracleComp (Spec n) A) (cap : Nat) (bounded : work.IsQueryBoundP IsHash cap) :
    (simulateQ RegistrationNativePlatformServerFrontendCompiler.embed work).IsQueryBoundP IsFrontendHash cap := by
  apply bounded.simulateQ_of_step
  · intro query _
    simp only [RegistrationNativePlatformServerFrontendCompiler.embed, isQueryBoundP_query_iff]
    exact fun _ => by decide
  · intro query uncounted
    simp only [RegistrationNativePlatformServerFrontendCompiler.embed, isQueryBoundP_query_iff, IsFrontendHash]
    exact fun selected => (uncounted selected).elim
omit primitive in
private theorem lift_bound (work : StateT (RegistrationNativePlatformBoundCompiler.PublicState Platform) (OracleComp (Spec n)) A)
    (cap : Nat) (bounded : Bounded work cap) :
    FrontBound (RegistrationNativePlatformServerFrontendCompiler.liftEffects work) cap :=
  fun before => embedded (work.run before) cap (bounded before)
omit primitive in
private theorem front_bind (work : StateT (RegistrationNativePlatformBoundCompiler.PublicState Platform)
    (OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n)) A)
    (next : A → StateT (RegistrationNativePlatformBoundCompiler.PublicState Platform)
      (OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n)) B)
    (first later : Nat) (bounded : FrontBound work first) (rest : ∀ value, FrontBound (next value) later) :
    FrontBound (work >>= next) (first + later) := by
  intro before
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (bounded before) (fun result _ => rest result.1 result.2)

private theorem service (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) :
    FrontBound (RegistrationNativePlatformServerFrontendCompiler.service (n := n) source view failure allocation erased helper sign writer control initial message) 4 := by
  unfold RegistrationNativePlatformServerFrontendCompiler.service
  apply front_bind _ _ 0 4
  · intro before
    simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsFrontendHash]
    exact fun impossible => impossible.elim
  · intro selected
    cases selected with
    | none => exact fun _ => isQueryBoundP_pure _ _ _
    | some choice => exact lift_bound _ 4 (branch source view failure allocation erased helper sign writer control initial choice)

private theorem target (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (query : RegistrationNativePlatformServerFrontendProgram.Spec.Domain) :
    FrontBound (RegistrationNativePlatformServerFrontendCompiler.target (n := n) source view failure allocation erased helper sign writer reserve query) 4 := by
  cases query with
  | pin current =>
    apply lift_bound
    intro previous
    have bounded : ((RegistrationNativePlatformServerRestrictedService.pin (n := n) current).run previous).IsQueryBoundP IsHash 1 := by
      change (((fun digest => (.ok (.Some ⟨current.binding, current.public_key, RegistrationAuthenticationShared.digestArray digest⟩), previous)) <$>
        ((Spec n).query (.inl (.inr (.hash (PqxdhRefinement.absBytes current.public_key)))))) :
          OracleComp (Spec n) (RustM (core.option.Option session.ServerAuthenticationPin) × RegistrationNativePlatformBoundCompiler.PublicState Platform)).IsQueryBoundP IsHash 1
      simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsHash]
      decide
    exact bounded.mono (by decide)
  | reserve =>
    apply lift_bound
    intro previous
    have bounded : ((RegistrationNativePlatformBoundCompiler.liftPlatform (n := n)
      (RegistrationNativePlatformEffectCompiler.compile reserve)).run previous).IsQueryBoundP IsHash 0 := by
      simp only [RegistrationNativePlatformBoundCompiler.liftPlatform, StateT.run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformEffectHashBounds.platform reserve previous.2
    exact bounded.mono (by decide)
  | present keyId =>
    apply lift_bound
    intro previous
    have bounded := effect (n := n) (.inr (.peerPresent keyId)) previous
    change (_ : OracleComp (Spec n) _).IsQueryBoundP IsHash 0 at bounded
    exact bounded.mono (by decide)
  | service control initial message => exact service source view failure allocation erased helper sign writer control initial message

/-- The literal corrected full Server build has a conservative finite shared-hash allowance derived from four reached source request leaves and their actual stateful implementations. -/
theorem build (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (front : RegistrationServerMaterialFrontend.State) (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) source view failure allocation erased helper sign writer reserve)
      ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run before).IsQueryBoundP IsFrontendHash 16 := by
  apply indicator IsFrontendHash _ 16
  apply weighted_run (fun _ => 4) frontCost _ _ 16 before
  · have actual := weighted_indicator (fun _ => True) 4 _ 4
      ((isQueryBoundP_true_iff _ _).mpr (RegistrationNativePlatformServerFrontendRequestBounds.program handle application front))
    simpa only [ite_true] using actual
  · intro query previous
    have actual := weighted_indicator (IsFrontendHash (n := n)) 1 _ _ (target (n := n) source view failure allocation erased helper sign writer reserve query previous)
    simp only [Nat.one_mul] at actual
    convert actual using 1; rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformServerHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerHashBounds.branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerHashBounds.branch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerHashBounds.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerHashBounds.build
