-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageLog
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation
/-! Source observation preserves the actual request-only signing cut as well as every result. The code uses the same preceding source hash to select its unsigned signing payload; observing it does not replace or reset that cut. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut
open BeaconcryptCore.Refinement
abbrev Spec := RegistrationNativePlatformPublicAdapterBuildStages.Spec
variable {S T A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "Cut" => RegistrationNativePlatformCutJournal.State

noncomputable def lifted (implementation : QueryImpl Spec (StateT S m)) : QueryImpl Spec (StateT (Cut S) m)
  | .inr (.inl query) => RegistrationNativePlatformCutJournal.forward
      (fun request => implementation (.inr (.inl request))) query
  | query => RegistrationNativePlatformCutJournal.liftNative (implementation query)

private theorem lift_source (left : StateT S m A) (right : StateT T m A)
    (projection : S → T) (before : Cut S)
    (law : Prod.map id projection <$>left.run before.1=right.run (projection before.1)) :
    Prod.map id (fun current => projection current.1) <$>
      (RegistrationNativePlatformCutJournal.liftNative left).run before=right.run (projection before.1) := by
  change (fun result : A × S => (result.1,projection result.2)) <$>left.run before.1 = _ at law
  simpa only [RegistrationNativePlatformCutJournal.liftNative,StateT.run,Functor.map_map,Prod.map,id_eq] using law

theorem query_source (left : QueryImpl Spec (StateT S m)) (right : QueryImpl Spec (StateT T m))
    (projection : S → T)
    (law : ∀ query before, Prod.map id projection <$> (left query).run before=(right query).run (projection before))
    (query : Spec.Domain) (before : Cut S) :
    Prod.map id (fun current => projection current.1) <$> (lifted left query).run before =
      (right query).run (projection before.1) := by
  cases query with
  | inl initial => exact lift_source _ _ projection before (law (.inl initial) before.1)
  | inr query => cases query with
    | inl query => cases query with
      | hash request =>
        change Prod.map id (fun current => projection current.1) <$>
          (RegistrationNativePlatformCutJournal.hash (fun request => left (.inr (.inl request))) request).run before = _
        rw [RegistrationNativePlatformCutJournal.hash_run]
        simp only [Functor.map_map,Prod.map,id_eq]
        have same := law (.inr (.inl (.hash request))) before.1
        change (fun result : CtxRomAuth.CtxDigest × S => (result.1,projection result.2)) <$>
          (left (.inr (.inl (.hash request)))).run before.1 = _ at same
        exact same
      | sign request payload digest => exact lift_source _ _ projection before (law (.inr (.inl (.sign request payload digest))) before.1)
    | inr signed => exact lift_source _ _ projection before (law (.inr (.inr signed)) before.1)

/-- The complete source suffix is unchanged, including the final source hash cut. -/
theorem actual (implementation : QueryImpl Spec (StateT S m))
    (fallback : registration.MldsaSigningRequest → StateT S m RegistrationSigningShared.SignReply)
    (initial : registration.ServerInitialKdf) :
    simulateQ (lifted implementation) (RegistrationNativePlatformPublicAdapterBuildStages.code initial) =
      AdapterPublicServerCompletionCut.stage (implementation (.inl initial))
        (fun query => implementation (.inr (.inl query))) fallback
        (fun signed => implementation (.inr (.inr signed))) := by
  rw [RegistrationNativePlatformPublicAdapterBuildStages.interpret]
  apply StateT.ext
  intro before
  unfold AdapterPublicServerCompletionCut.stage
  rw [StateT.run_bind,StateT.run_bind]
  apply bind_congr
  rintro ⟨first,current⟩
  cases first with
  | fail error | div => rfl
  | ok first => cases first with
    | Err rejected => rfl
    | Ok pending =>
      exact (RegistrationNativePlatformCutJournal.server
        (fun query => implementation (.inr (.inl query))) fallback
        (fun signed => RegistrationNativePlatformCutJournal.liftNative (implementation (.inr (.inr signed))))
        pending current).symm


variable {Log : Type}

theorem observed_query (implementation : QueryImpl Spec (StateT S m))
    (observe : (query : Spec.Domain) → Spec.Range query → List Log)
    (query : Spec.Domain) (before : Cut S × List Log) :
    Prod.map id RegistrationNativePlatformPublicAdapterCutLogAssociation.associate <$>
      (RegistrationNativePlatformPublicAdapterSourceTrace.recorded (lifted implementation) observe query).run before =
      (lifted (RegistrationNativePlatformPublicAdapterSourceTrace.recorded implementation observe) query).run
        (RegistrationNativePlatformPublicAdapterCutLogAssociation.associate before) := by
  cases query with
  | inl initial => exact RegistrationNativePlatformPublicAdapterCutLogAssociation.lift_query implementation observe (.inl initial) before
  | inr query => cases query with
    | inl query =>
      exact RegistrationNativePlatformPublicAdapterCutLogAssociation.forward_query
        (fun request => implementation (.inr (.inl request))) (fun request reply => observe (.inr (.inl request)) reply) query before
    | inr signed => exact RegistrationNativePlatformPublicAdapterCutLogAssociation.lift_query implementation observe (.inr (.inr signed)) before

theorem observed_program (implementation : QueryImpl Spec (StateT S m))
    (observe : (query : Spec.Domain) → Spec.Range query → List Log)
    (work : OracleComp Spec A) (before : Cut S × List Log) :
    Prod.map id RegistrationNativePlatformPublicAdapterCutLogAssociation.associate <$>
      (simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded (lifted implementation) observe) work).run before =
      (simulateQ (lifted (RegistrationNativePlatformPublicAdapterSourceTrace.recorded implementation observe)) work).run
        (RegistrationNativePlatformPublicAdapterCutLogAssociation.associate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (observed_query implementation observe) work before

/-- The observed code is the actual request-only source controller with its actual source leaves observed, including the same preceding hash cut. -/
theorem observed_actual (implementation : QueryImpl Spec (StateT S m))
    (observe : (query : Spec.Domain) → Spec.Range query → List Log)
    (fallback : registration.MldsaSigningRequest → StateT (S × List Log) m RegistrationSigningShared.SignReply)
    (initial : registration.ServerInitialKdf) (before : Cut S × List Log) :
    Prod.map id RegistrationNativePlatformPublicAdapterCutLogAssociation.associate <$>
      (simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded (lifted implementation) observe)
        (RegistrationNativePlatformPublicAdapterBuildStages.code initial)).run before =
      (AdapterPublicServerCompletionCut.stage
        (RegistrationNativePlatformPublicAdapterSourceTrace.recorded implementation observe (.inl initial))
        (fun query => RegistrationNativePlatformPublicAdapterSourceTrace.recorded implementation observe (.inr (.inl query))) fallback
        (fun signed => RegistrationNativePlatformPublicAdapterSourceTrace.recorded implementation observe (.inr (.inr signed)))).run
        (RegistrationNativePlatformPublicAdapterCutLogAssociation.associate before) := by
  rw [observed_program,actual]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut.actual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut.observed_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut.observed_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut.observed_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut.observed_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut.observed_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut.observed_actual
