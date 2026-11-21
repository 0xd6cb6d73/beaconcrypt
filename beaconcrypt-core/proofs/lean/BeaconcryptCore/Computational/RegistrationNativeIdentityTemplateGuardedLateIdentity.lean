-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity
/-! The ordinary adversary declines a missed first selector. A positive selector is the public successful-reply policy's own fresh-message choice; no private source predicate enters this executable guard. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity
open PqxdhJointIdentity (Primitives PublicIdentity)
open RegistrationNativeIdentityTemplateLateIdentity (Spec Witness raw note record)
open RegistrationNativeIdentityTemplatePublicRegistry (Registry)
open RegistrationNativeIdentityCensorPacketClient (Found)
abbrev Cut := RegistrationNativeIdentityTemplateSelectionCut.Cut

def resume (joint : Primitives) (selected : Nat) (cut : Cut (Option Found)) (before : Registry) : OracleComp Spec (Option Witness) :=
  match cut with
  | .returned _ => pure none
  | .selected message next => match before selected with
    | none => pure none
    | some identity => do
        let chosen : Bool ← (Spec.query (.inl (.inl (.inr message))) : OracleComp Spec Bool)
        if chosen then
          raw joint identity <$> (RegistrationNativeIdentityRecognitionCapture.capture
            (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity) (next true))
        else pure none

def visit (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found)) :
    Registry → OracleComp Spec (Option Witness) :=
  OracleComp.construct (C := fun _ => Registry → OracleComp Spec (Option Witness))
    (fun _ _before => pure none)
    (fun query next continued before => match query with
      | .inl (.inl (.inr message)) => match before selected with
        | none => pure none
        | some identity => do
            let chosen : Bool ← (Spec.query (.inl (.inl (.inr message))) : OracleComp Spec Bool)
            if chosen then
              raw joint identity <$> (RegistrationNativeIdentityRecognitionCapture.capture
                (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity) (next true))
            else pure none
      | query => do let answer ← Spec.query query; continued answer (note query answer before)) work

private theorem capture_bound {A W : Type} (recognize : Spec.Domain → Option W) (work : OracleComp Spec A)
    (predicate : Spec.Domain → Prop) [DecidablePred predicate] (cap : Nat) (bounded : work.IsQueryBoundP predicate cap) :
    (RegistrationNativeIdentityRecognitionCapture.capture recognize work).IsQueryBoundP predicate cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind query next ih =>
    obtain ⟨first,later⟩ := (isQueryBoundP_query_bind_iff _ _ _ _).mp bounded
    have step : RegistrationNativeIdentityRecognitionCapture.capture recognize (Spec.query query >>= next) =
        (match recognize query with
        | some witness => pure (.inl witness)
        | none => do let answer ← Spec.query query; RegistrationNativeIdentityRecognitionCapture.capture recognize (next answer)) := rfl
    rw [step]
    cases recognize query with
    | some witness => exact isQueryBoundP_pure _ _ _
    | none => exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr ⟨first,fun answer => ih answer _ (later answer)⟩

private theorem visit_query (joint : Primitives) (selected : Nat) (query : Spec.Domain)
    (next : Spec.Range query → OracleComp Spec (Option Found)) (before : Registry) :
    visit joint selected (Spec.query query >>= next) before =
      (match query with
      | .inl (.inl (.inr message)) => match before selected with
        | none => pure none
        | some identity => do
            let chosen : Bool ← (Spec.query (.inl (.inl (.inr message))) : OracleComp Spec Bool)
            if chosen then
              raw joint identity <$> (RegistrationNativeIdentityRecognitionCapture.capture
                (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity) (next true))
            else pure none
      | query => do let answer ← Spec.query query; visit joint selected (next answer) (note query answer before)) := by
  rcases query with ((protocol | message) | scanned) | described <;> rfl

/-- Rejecting a missed public selector adds no request of any class and preserves the original syntactic budget. -/
theorem query_bound (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found))
    (predicate : Spec.Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : work.IsQueryBoundP predicate cap) (before : Registry) :
    (visit joint selected work before).IsQueryBoundP predicate cap := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind query next ih =>
    rw [visit_query]
    obtain ⟨first,later⟩ := (isQueryBoundP_query_bind_iff _ _ _ _).mp bounded
    rcases query with ((protocol | message) | scanned) | described
    · exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr ⟨first,fun answer => ih answer _ (later answer) (note (.inl (.inl (.inl protocol))) answer before)⟩
    · cases before selected with
      | none => exact isQueryBoundP_pure _ _ _
      | some identity =>
        apply (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        refine ⟨first,?_⟩
        intro chosen
        cases chosen with
        | false => exact isQueryBoundP_pure _ _ _
        | true =>
          change (raw joint identity <$> RegistrationNativeIdentityRecognitionCapture.capture
            (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity) (next true)).IsQueryBoundP predicate _
          rw [isQueryBoundP_map_iff]
          exact capture_bound _ _ predicate _ (later true)
    · exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr ⟨first,fun answer => ih answer _ (later answer) (note (.inl (.inr scanned)) answer before)⟩
    · exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr ⟨first,fun answer => ih answer _ (later answer) (note (.inr described) answer before)⟩

private theorem stop_query (query : Spec.Domain)
    (next : Spec.Range query → OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found)) :
    RegistrationNativeIdentityTemplateSelectionCut.stop (Spec.query query >>= next) =
      (match query with
      | .inl (.inl (.inr message)) => pure (.selected message next)
      | query => do let answer ← Spec.query query
                    RegistrationNativeIdentityTemplateSelectionCut.stop (next answer)) := by
  rcases query with ((protocol | selectedMessage) | scanned) | described <;> rfl

/-- The whole late-key client runs the literal identity-free prefix, retaining its original continuation and the public registry at that SAME first selector. -/
theorem factor (joint : Primitives) (selected : Nat)
    (work : OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found)) (before : Registry) :
    visit joint selected work before = (do
      let cut ← (simulateQ record (RegistrationNativeIdentityTemplateSelectionCut.stop work)).run before
      resume joint selected cut.1 cut.2) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    rw [visit_query,stop_query]
    rcases query with ((protocol | selectedMessage) | scanned) | described
    · simp only [simulateQ_bind,simulateQ_spec_query,StateT.run]
      exact bind_congr (fun answer => ih answer (note (.inl (.inl (.inl protocol))) answer before))
    · simp only [simulateQ_pure,StateT.run_pure,pure_bind,resume ]
    · simp only [simulateQ_bind,simulateQ_spec_query,StateT.run]
      exact bind_congr (fun answer => ih answer (note (.inl (.inr scanned)) answer before))
    · simp only [simulateQ_bind,simulateQ_spec_query,StateT.run]
      exact bind_congr (fun answer => ih answer (note (.inr described) answer before))

private theorem capture_scope {A W : Type} (recognize : Spec.Domain → Option W) (work : OracleComp Spec A)
    (predicate : Spec.Domain → Prop) (allowed : work.AllQueriesSatisfy predicate) :
    (RegistrationNativeIdentityRecognitionCapture.capture recognize work).AllQueriesSatisfy predicate := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    have step : RegistrationNativeIdentityRecognitionCapture.capture recognize (Spec.query query >>= next) =
        (match recognize query with
        | some witness => pure (.inl witness)
        | none => do let answer ← Spec.query query; RegistrationNativeIdentityRecognitionCapture.capture recognize (next answer)) := rfl
    rw [step]
    cases recognize query with
    | some witness => exact allQueriesSatisfy_pure _ _
    | none => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨first,fun answer => ih answer (later answer)⟩

/-- The executable fresh-choice guard preserves every original structural query restriction, including no identity reveals. -/
theorem scope (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found))
    (predicate : Spec.Domain → Prop) (allowed : work.AllQueriesSatisfy predicate) (before : Registry) :
    (visit joint selected work before).AllQueriesSatisfy predicate := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    rw [visit_query]
    obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    rcases query with ((protocol | message) | scanned) | described
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨first,fun answer => ih answer (later answer) (note (.inl (.inl (.inl protocol))) answer before)⟩
    · cases before selected with
      | none => exact allQueriesSatisfy_pure _ _
      | some identity =>
        apply (allQueriesSatisfy_query_bind_iff _ _ _).mpr
        refine ⟨first,?_⟩
        intro chosen
        cases chosen with
        | false => exact allQueriesSatisfy_pure _ _
        | true =>
          change (raw joint identity <$> RegistrationNativeIdentityRecognitionCapture.capture
            (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity) (next true)).AllQueriesSatisfy predicate
          exact RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ (capture_scope _ _ predicate (later true))
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨first,fun answer => ih answer (later answer) (note (.inl (.inr scanned)) answer before)⟩
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨first,fun answer => ih answer (later answer) (note (.inr described) answer before)⟩

private theorem bind_apply {State X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT State m X) (next : X → StateT State m Y) (before : State) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem map_apply {State X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT State m X) (before : State) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem capture_selection (joint : Primitives) (identity : PublicIdentity) (message : Pqxdh.Bytes)
    (next : Bool → OracleComp Spec (Option Found)) :
    RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity)
      ((Spec.query (.inl (.inl (.inr message))) : OracleComp Spec Bool) >>= next) = (do
        let chosen ← (Spec.query (.inl (.inl (.inr message))) : OracleComp Spec Bool)
        RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity) (next chosen)) := rfl

/-- The guard changes no correct fresh first-selector path or its literal public poststate. -/
theorem positive (joint : Primitives) (selected : Nat) (message : Pqxdh.Bytes)
    (next : Bool → OracleComp Spec (Option Found)) (registry : Registry) (identity : PublicIdentity)
    (found : registry selected = some identity) (before : RegistrationNativeIdentityTemplatePolicy.Public)
    (picked : RegistrationNativeIdentityAdaptiveCensor.Policy)
    (chosen : RegistrationNativeIdentityCensorPolicySource.choose message before.1 = (true,picked)) :
    (simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
      (resume joint selected (.selected message next) registry)).run before =
    (simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
      (RegistrationNativeIdentityTemplateLateIdentity.resume joint selected (.selected message next) registry)).run before := by
  simp only [resume,RegistrationNativeIdentityTemplateLateIdentity.resume,found,RegistrationNativeIdentityTemplateSelectionCut.resume]
  rw [capture_selection]
  simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_map,StateT.run,bind_apply,map_apply,map_bind]
  simp only [RegistrationNativeIdentityTemplatePolicy.handler,chosen,pure_bind]
  simp only [ite_true,simulateQ_map,map_apply]

/-- Refused public selection returns no candidate while retaining its reached policy/cache poststate. -/
theorem negative (joint : Primitives) (selected : Nat) (message : Pqxdh.Bytes)
    (next : Bool → OracleComp Spec (Option Found)) (registry : Registry) (identity : PublicIdentity)
    (found : registry selected = some identity) (before : RegistrationNativeIdentityTemplatePolicy.Public)
    (picked : RegistrationNativeIdentityAdaptiveCensor.Policy)
    (chosen : RegistrationNativeIdentityCensorPolicySource.choose message before.1 = (false,picked)) :
    (simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
      (resume joint selected (.selected message next) registry)).run before = pure (none,(picked,before.2)) := by
  simp only [resume,found,simulateQ_bind,simulateQ_spec_query,StateT.run,bind_apply]
  simp only [RegistrationNativeIdentityTemplatePolicy.handler,chosen,pure_bind]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity.query_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity.factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity.scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity.scope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity.positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity.positive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity.negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity.negative
