-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut
/-! A source-family client discovers its recognition key from earlier public create replies only when it reaches its first selector. The prefix therefore has no dependency on a future sampled identity. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity
open PqxdhJointIdentity (Primitives PublicIdentity Forgery)
open RegistrationNativeIdentityTemplatePublicRegistry (Registry)
abbrev Spec := RegistrationNativeIdentityTemplateCensorRecognition.Spec
abbrev Cut := RegistrationNativeIdentityTemplateSelectionCut.Cut
abbrev Witness := PublicIdentity × Forgery
variable {A : Type}

def selection : Spec.Domain → Option Pqxdh.Bytes
  | .inl (.inl (.inr message)) => some message
  | _ => none

def note : (query : Spec.Domain) → Spec.Range query → Registry → Registry
  | .inl (.inl (.inl protocol)), answer, before => RegistrationNativeIdentityTemplatePublicRegistry.note (.inl protocol) answer before
  | _, _, before => before

def record : QueryImpl Spec (StateT Registry (OracleComp Spec)) := fun query before => do
  let answer ← Spec.query query
  pure (answer,note query answer before)

def raw (joint : Primitives) (identity : PublicIdentity) :
    RegistrationNativeIdentityAdaptiveHashCapture.Candidate joint identity ⊕ Option RegistrationNativeIdentityCensorPacketClient.Found → Option Witness
  | .inl candidate => some (identity,⟨candidate.1,candidate.2.val⟩)
  | .inr found => (RegistrationNativeIdentityCensorPacketClient.candidate joint identity found).map
      (fun candidate => (identity,⟨candidate.1,candidate.2.val⟩))

def resume (joint : Primitives) (selected : Nat) (cut : Cut (Option RegistrationNativeIdentityCensorPacketClient.Found))
    (before : Registry) : OracleComp Spec (Option Witness) :=
  match cut with
  | .returned _ => pure none
  | .selected _ _ => match before selected with
    | none => pure none
    | some identity => raw joint identity <$> RegistrationNativeIdentityRecognitionCapture.capture
        (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity)
        (RegistrationNativeIdentityTemplateSelectionCut.resume cut)

/-- Every oracle request preceding the first selector is forwarded literally. The chosen public key is read only at that selector; no seed table is available to this executable program. -/
def visit (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found)) :
    Registry → OracleComp Spec (Option Witness) :=
  OracleComp.construct (C := fun _ => Registry → OracleComp Spec (Option Witness))
    (fun _ _before => pure none)
    (fun query next continued before => match selection query with
      | some _ => match before selected with
        | none => pure none
        | some identity => raw joint identity <$> RegistrationNativeIdentityRecognitionCapture.capture
            (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity) (Spec.query query >>= next)
      | none => do let answer ← Spec.query query; continued answer (note query answer before)) work

private theorem capture_bound {W X : Type} (recognize : Spec.Domain → Option W)
    (work : OracleComp Spec X) (predicate : Spec.Domain → Prop) [DecidablePred predicate]
    (cap : Nat) (bounded : work.IsQueryBoundP predicate cap) :
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
    (next : Spec.Range query → OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found)) (before : Registry) :
    visit joint selected (Spec.query query >>= next) before =
      (match selection query with
      | some _ => match before selected with
        | none => pure none
        | some identity => raw joint identity <$> RegistrationNativeIdentityRecognitionCapture.capture
            (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity) (Spec.query query >>= next)
      | none => do let answer ← Spec.query query; visit joint selected (next answer) (note query answer before)) := rfl

/-- Deferring key discovery, recording public replies and recognizing a signature add no query of any class. -/
theorem query_bound (joint : Primitives) (selected : Nat)
    (work : OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found))
    (predicate : Spec.Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : work.IsQueryBoundP predicate cap) (before : Registry) :
    (visit joint selected work before).IsQueryBoundP predicate cap := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind query next ih =>
    rw [visit_query]
    cases selection query with
    | some message =>
      cases before selected with
      | none => exact isQueryBoundP_pure _ _ _
      | some identity =>
        rw [isQueryBoundP_map_iff]
        exact capture_bound _ _ predicate cap bounded
    | none =>
      obtain ⟨first,later⟩ := (isQueryBoundP_query_bind_iff _ _ _ _).mp bounded
      exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr ⟨first,fun answer => ih answer _ (later answer) (note query answer before)⟩

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
    · simp only [selection,simulateQ_bind,simulateQ_spec_query,StateT.run]
      exact bind_congr (fun answer => ih answer (note (.inl (.inl (.inl protocol))) answer before))
    · simp only [selection,simulateQ_pure,StateT.run_pure,pure_bind,resume,RegistrationNativeIdentityTemplateSelectionCut.resume]
    · simp only [selection,simulateQ_bind,simulateQ_spec_query,StateT.run]
      exact bind_congr (fun answer => ih answer (note (.inl (.inr scanned)) answer before))
    · simp only [selection,simulateQ_bind,simulateQ_spec_query,StateT.run]
      exact bind_congr (fun answer => ih answer (note (.inr described) answer before))

/-- On the actual selected-row prefix the late-key suffix is the existing fixed-public-identity recognition client exactly. -/
theorem known (joint : Primitives) (selected : Nat) (message : Pqxdh.Bytes)
    (continued : Bool → OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found))
    (before : Registry) (identity : PublicIdentity) (found : before selected = some identity) :
    resume joint selected (.selected message continued) before =
      raw joint identity <$> RegistrationNativeIdentityRecognitionCapture.capture
        (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity)
        (Spec.query (.inl (.inl (.inr message))) >>= continued) := by
  simp only [resume,found]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity.query_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity.factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity.known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity.known
