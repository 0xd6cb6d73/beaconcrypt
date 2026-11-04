-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource
/-! Public key discovery and recognition forward only requests already present in the original tree. In particular they preserve the actual source's structural absence of identity reveals. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateScope
open RegistrationNativeIdentityTemplateLateIdentity (Spec)
open RegistrationNativeIdentityTemplatePublicRegistry (Registry)
variable {A : Type}

private theorem capture_safe {W : Type} (recognize : Spec.Domain → Option W) (work : OracleComp Spec A)
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

private theorem visit_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (query : Spec.Domain)
    (next : Spec.Range query → OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found))
    (before : Registry) :
    RegistrationNativeIdentityTemplateLateIdentity.visit joint selected (Spec.query query >>= next) before =
      (match RegistrationNativeIdentityTemplateLateIdentity.selection query with
      | some _ => match before selected with
        | none => pure none
        | some identity => RegistrationNativeIdentityTemplateLateIdentity.raw joint identity <$>
            RegistrationNativeIdentityRecognitionCapture.capture
              (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity) (Spec.query query >>= next)
      | none => do let answer ← Spec.query query
                   RegistrationNativeIdentityTemplateLateIdentity.visit joint selected (next answer)
                     (RegistrationNativeIdentityTemplateLateIdentity.note query answer before)) := rfl

/-- The late public registry and recognizer introduce no request outside the original source tree. -/
theorem visit (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (work : OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found)) (before : Registry)
    (predicate : Spec.Domain → Prop) (allowed : work.AllQueriesSatisfy predicate) :
    (RegistrationNativeIdentityTemplateLateIdentity.visit joint selected work before).AllQueriesSatisfy predicate := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    rw [visit_query]
    cases RegistrationNativeIdentityTemplateLateIdentity.selection query with
    | some message =>
      cases before selected with
      | none => exact allQueriesSatisfy_pure _ _
      | some identity =>
        exact RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ (capture_safe _ _ predicate allowed)
    | none =>
      obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨first,fun answer => ih answer _ (later answer)⟩

/-- Literal public policy and hash compilation preserve the original no-reveal scope. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (work : OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found)) (registry : Registry)
    (allowed : work.AllQueriesSatisfy RegistrationNativeIdentityTemplateChosenSource.TemplateAllowed)
    (before : RegistrationNativeIdentityTemplatePolicy.Public) :
    ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
      (RegistrationNativeIdentityTemplateLateIdentity.visit joint selected work registry)).run before).AllQueriesSatisfy
        RegistrationNativeIdentityTemplateChosenSource.Allowed :=
  RegistrationNativeIdentityTemplateChosenSource.template_program selected _ (visit joint selected work registry _ allowed) before

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateScope
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateScope.visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateScope.visit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateScope.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateScope.program
