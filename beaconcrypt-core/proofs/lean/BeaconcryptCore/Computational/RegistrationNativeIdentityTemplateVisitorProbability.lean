-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame
/-! The actual first-selector prefix is shared by the full physical and public packet executions. Integrating the local scan/omission loss over that same prefix keeps recognition and the submitted packet in one event. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPublicClient (ClientState)
open RegistrationNativeIdentityCensorPacketClient (Found)
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
abbrev New := RegistrationNativeIdentityTemplateCensorRecognition.Spec
abbrev OriginalCut := RegistrationNativeIdentityTemplateSelectionCut.Original.Cut
abbrev Cut := RegistrationNativeIdentityTemplateSelectionCut.Cut
abbrev Private := RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State
abbrev Public := RegistrationNativeIdentityTemplatePolicy.Public × PqxdhDynamicIdentityPool.SourceState
variable {A S : Type}

private theorem capture_query {I X W : Type} {spec : OracleSpec I}
    (recognize : spec.Domain → Option W) (query : spec.Domain) (next : spec.Range query → OracleComp spec X) :
    RegistrationNativeIdentityRecognitionCapture.capture recognize (spec.query query >>= next) =
      (match recognize query with
      | some witness => pure (.inl witness)
      | none => do let answer ← (spec.query query : OracleComp spec _)
                   RegistrationNativeIdentityRecognitionCapture.capture recognize (next answer)) := rfl

private theorem capture_bind {I X Y W : Type} {spec : OracleSpec I}
    (recognize : spec.Domain → Option W) (work : OracleComp spec X) (next : X → OracleComp spec Y) :
    RegistrationNativeIdentityRecognitionCapture.capture recognize (work >>= next) = (do
      let result ← RegistrationNativeIdentityRecognitionCapture.capture recognize work
      match result with
      | .inl witness => pure (.inl witness)
      | .inr value => RegistrationNativeIdentityRecognitionCapture.capture recognize (next value)) := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query rest ih =>
    rw [bind_assoc,capture_query,capture_query]
    cases found : recognize query with
    | some witness => simp only [pure_bind]
    | none =>
      rw [bind_assoc]
      exact bind_congr ih

/-- Recognition remains transparent on the complete actual first-selection prefix. The retained continuation is the original whole packet visitor. -/
theorem capture_factor (joint : Primitives) (identity : PqxdhJointIdentity.PublicIdentity)
    (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (missing : before.1.2.target = none) :
    RegistrationNativeIdentityTemplateOmissionPublic.client joint identity placeholder
      (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before) = (do
        let cut ← RegistrationNativeIdentityTemplateSelectionCut.stop
          (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
            (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
        RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity)
          (RegistrationNativeIdentityTemplateSelectionCut.resume cut)) := by
  let code := simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
    (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)
  have factor := congrArg (RegistrationNativeIdentityRecognitionCapture.capture
    (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity))
      (RegistrationNativeIdentityTemplateSelectionCut.factor code)
  rw [capture_bind,RegistrationNativeIdentityTemplateIssuedGame.prefix_capture joint identity selected bundle accept placeholder frontend defaults work before missing,
    bind_map_left] at factor
  exact factor.symm

private theorem public_output (joint : Primitives) (selected : Nat) (identity : PqxdhJointIdentity.PublicIdentity)
    (placeholder : Ed25519Signature) (work : OracleComp Old A) (before : Public) :
    (fun result => result.1.1) <$> RegistrationNativeIdentityTemplateOmissionPublic.execute joint identity selected placeholder work before.1.1 before.1.2 before.2 =
      Prod.fst <$> (simulateQ (RegistrationNativeIdentityTemplatePublicPrefix.publicSource joint selected)
        (RegistrationNativeIdentityTemplateOmissionPublic.client joint identity placeholder work)).run before := by
  rw [RegistrationNativeIdentityTemplatePublicPrefix.publicSource,QueryImpl.Stateful.simulateQ_link_run]
  simp only [RegistrationNativeIdentityTemplateOmissionPublic.execute,Functor.map_map,
    QueryImpl.Stateful.Frame.prod]

private theorem resume_erased (joint : Primitives) (identity : PqxdhJointIdentity.PublicIdentity)
    (placeholder : Ed25519Signature) (cut : OriginalCut A) :
    RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity)
      (RegistrationNativeIdentityTemplateSelectionCut.resume (RegistrationNativeIdentityTemplateSelectionCut.Original.erased placeholder cut)) =
        RegistrationNativeIdentityTemplateOmissionPublic.client joint identity placeholder
          (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut) := by
  cases cut <;> rfl

/-- The public complete recognized-or-packet execution has the SAME reached first-selector prefix as the physical source, including its entire warm table and genuine source audit. -/
theorem public_execution (joint : Primitives) (identity : PqxdhJointIdentity.PublicIdentity)
    (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (missing : before.1.2.target = none) (privateBefore : Private) :
    (fun result => result.1.1) <$> RegistrationNativeIdentityTemplateOmissionPublic.execute joint identity selected placeholder
      (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)
      privateBefore.1 (RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2) privateBefore.2.pool = (do
        let cut ← (simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
          (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
            (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore
        (fun result => result.1.1) <$> RegistrationNativeIdentityTemplateOmissionPublic.execute joint identity selected placeholder
          (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1) cut.2.1
          (RegistrationNativeIdentityTemplateFirstOmitted.install cut.2.2) cut.2.2.pool) := by
  rw [public_output joint selected identity placeholder _ ((privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2),privateBefore.2.pool)]
  change Prod.fst <$> (simulateQ (RegistrationNativeIdentityTemplatePublicPrefix.publicSource joint selected)
    (RegistrationNativeIdentityTemplateOmissionPublic.client joint identity placeholder
      (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run
        (RegistrationNativeIdentityTemplatePublicPrefix.project privateBefore) = _
  rw [capture_factor joint identity selected bundle accept placeholder frontend defaults work before missing,
    simulateQ_bind,StateT.run_bind,map_bind]
  rw [←RegistrationNativeIdentityTemplateIssuedGame.prefix_source joint selected bundle accept placeholder frontend defaults work before missing privateBefore,
    bind_map_left]
  apply bind_congr
  intro cut
  simp only [Prod.map_fst,Prod.map_snd]
  rw [resume_erased]
  exact (public_output joint selected identity placeholder (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)
    ((cut.2.1,RegistrationNativeIdentityTemplateFirstOmitted.install cut.2.2),cut.2.2.pool)).symm

/-- Eligibility is a proof observation of the SAME first-selector cut, never an executable test or a private selector. The original issued branch supplies it from its fresh source receipt. -/
def Eligible (selected : Nat) (seed : IdentitySeed) (cut : OriginalCut (Option Found) × Private) : Prop :=
  match cut.1 with
  | .returned _ => False
  | .selected message _ => cut.2.2.pool.seeds[selected]? = some seed ∧
      message ∉ RegistrationNativeIdentityCensorPolicySource.messages selected cut.2.2.pool

noncomputable def coupled (joint : Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (privateBefore : Private) :
    ProbComp ((OriginalCut (Option Found) × Private) × (Option Found × RegistrationNativeIdentityCensorSource.State)) := do
  let cut ← (simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
    (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
      (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore
  let result ← (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
    (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2.2
  pure (cut,result)

/-- Erasing only the first-selection receipt restores the literal complete censored visitor, with the complete physical cache, source audit and every later callback retained. -/
theorem source_marginal (joint : Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (privateBefore : Private) :
    Prod.snd <$> coupled joint selected bundle accept placeholder frontend defaults work before privateBefore =
      (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
        (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)).run privateBefore.2 := by
  simp only [coupled,map_bind,map_pure,bind_pure]
  symm
  rw [RegistrationNativeIdentityTemplateSelectionCut.Original.execution]
  rw [←RegistrationNativeIdentityCensorPolicySource.program_erasure joint selected placeholder
    (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
      (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)) privateBefore,
    bind_map_left]
  rfl

/-- Integrating the actual local omission loss over its common full prefix charges one public recognized-or-packet event. The original branch is retained only at its actual fresh reached cut; no probability conclusion follows from an existential supported cut. -/
theorem loss {I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (missing : before.1.2.target = none) (privateBefore : Private)
    (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2)
    (seed : IdentitySeed) (event : Option Found → Prop) :
    Pr{let result ← (coupled setup.joint selected bundle accept placeholder frontend defaults work before privateBefore)}[
      Eligible selected seed result.1 ∧ event result.2.1] ≤
    Pr{let result ← (RegistrationNativeIdentityTemplateOmissionPublic.execute setup.joint (setup.joint.publicKeys seed) selected placeholder
      (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)
      privateBefore.1 (RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2) privateBefore.2.pool)}[
        RegistrationNativeIdentityTemplateOmissionPublic.Succeeds event result.1.1] := by
  classical
  have entire := congrArg (fun distribution => Pr{let result ← distribution}[
      RegistrationNativeIdentityTemplateOmissionPublic.Succeeds event result])
    (public_execution setup.joint (setup.joint.publicKeys seed) selected bundle accept placeholder frontend defaults work before missing privateBefore)
  simp only [prEvent_map] at entire
  rw [entire]
  simp only [coupled]
  apply prEvent_bind_mono_of_forall_le_of_support
  intro cut reached
  simp only [bind_pure_comp,prEvent_map]
  by_cases eligible : Eligible selected seed cut
  · simp only [eligible,true_and]
    rcases cut with ⟨cut,after⟩
    cases cut with
    | returned value => exact False.elim eligible
    | selected message continued =>
      obtain ⟨found,fresh⟩ := eligible
      simpa only [RegistrationNativeIdentityTemplateSelectionCut.Original.resume] using
        RegistrationNativeIdentityTemplateIssuedGame.cut_loss setup selected bundle accept placeholder frontend defaults work before missing privateBefore prior journal
          message continued after reached seed found fresh event
  · simp only [eligible,false_and,prEvent_false]
    exact zero_le

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability.capture_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability.capture_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability.public_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability.public_execution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability.loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability.loss

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability.source_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability.source_marginal
