-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistrySource
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLatePhysical
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateFamily
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateIdentity
/-! The identity-free public late-key program has the same physical first-selector prefix and recovers its actual recognition key from the public create-reply registry. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateSource
open PqxdhJointIdentity (Primitives)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec source)
open RegistrationNativeIdentityTemplatePolicy (Public)
open RegistrationNativeIdentityTemplatePublicRegistry (Registry keys)
open RegistrationNativeIdentityCensorPacketClient (Found)
variable {A : Type}

noncomputable def program (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found))
    (registry : Registry) (before : Public) :=
  (simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
    (RegistrationNativeIdentityTemplateGuardedLateIdentity.visit joint selected work registry)).run before

noncomputable def continuation (joint : Primitives) (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (cut : RegistrationNativeIdentityTemplateVisitorProbability.OriginalCut (Option Found) × RegistrationNativeIdentityTemplateVisitorProbability.Private) :
    ProbComp (Option RegistrationNativeIdentityTemplateLateIdentity.Witness) :=
  match cut.1 with
  | .returned _ => pure none
  | .selected message _ => if (RegistrationNativeIdentityCensorPolicySource.choose message cut.2.1).1 then
      RegistrationNativeIdentityTemplateLatePhysical.continuation joint selected placeholder cut else pure none

noncomputable def upper {S V : Type} (joint : Primitives) (selected bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S)
    (privateBefore : RegistrationNativeIdentityTemplateVisitorProbability.Private) :
    ProbComp (Option RegistrationNativeIdentityTemplateLateIdentity.Witness) := do
  let cut ← (simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
    (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
      (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore
  continuation joint selected placeholder cut

/-- The actual public source runs the identity-free prefix and then looks up its same reached public key. Every local policy/cache coordinate and full source pool remains attached. -/
theorem execution (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found))
    (publicBefore : Public) (before : PqxdhDynamicIdentityPool.SourceState) :
    (simulateQ (source joint) (program joint selected work (keys joint before) publicBefore)).run before = (do
      let cut ← (simulateQ (source joint)
        ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
          (RegistrationNativeIdentityTemplateSelectionCut.stop work)).run publicBefore)).run before
      (simulateQ (source joint)
        ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
          (RegistrationNativeIdentityTemplateGuardedLateIdentity.resume joint selected cut.1.1 (keys joint cut.2))).run cut.1.2)).run cut.2) := by
  unfold program
  rw [RegistrationNativeIdentityTemplateGuardedLateIdentity.factor]
  simp only [simulateQ_bind,StateT.run_bind]
  rw [RegistrationNativeIdentityTemplateRegistrySource.policy_complete,bind_map_left]

/-- The public key read by the executable late client is the SAME row used by the physical selector loss. Only public fields enter the client; the complete original source remains in its interpreter. -/
theorem upper_source {S V : Type} (joint : Primitives) (selected bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S) (missing : before.1.2.target = none)
    (privateBefore : RegistrationNativeIdentityTemplateVisitorProbability.Private) :
    (fun result => result.1.1) <$>
      (simulateQ (source joint)
        (program joint selected
          (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
            (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
          (keys joint privateBefore.2.pool)
          (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool =
      upper joint selected bundle accept placeholder frontend defaults work before privateBefore := by
  rw [execution,map_bind]
  have observed := congrArg (Functor.map (fun result :
      RegistrationNativeIdentityTemplateSelectionCut.Cut (Option Found) ×
        (Public × PqxdhDynamicIdentityPool.SourceState) => ((result.1,result.2.1),result.2.2)))
    (RegistrationNativeIdentityTemplateIssuedGame.prefix_source joint selected bundle accept placeholder frontend defaults work before missing privateBefore)
  rw [RegistrationNativeIdentityTemplatePublicPrefix.publicSource,QueryImpl.Stateful.simulateQ_link_run] at observed
  simp only [Functor.map_map,QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst_put,PFunctor.Lens.State.snd_put,Prod.map_def,Prod.eta] at observed
  have shared :
      (fun cut => ((RegistrationNativeIdentityTemplateSelectionCut.Original.erased placeholder cut.1,
        (RegistrationNativeIdentityTemplatePublicPrefix.project cut.2).1),
        (RegistrationNativeIdentityTemplatePublicPrefix.project cut.2).2)) <$>
          (simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
            (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
              (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore =
      (simulateQ (source joint)
        ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
          (RegistrationNativeIdentityTemplateSelectionCut.stop
            (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
              (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)))).run
          (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool := by
    simpa only [RegistrationNativeIdentityTemplatePublicPrefix.project,RegistrationNativeIdentityTemplatePublicCtx.install,RegistrationNativeIdentityTemplateFirstOmitted.install,show (fun value : (RegistrationNativeIdentityTemplateSelectionCut.Cut (Option Found) × Public) × PqxdhDynamicIdentityPool.SourceState => value) = id from rfl,id_map] using observed
  rw [←shared,bind_map_left]
  unfold upper
  apply bind_congr
  intro cut
  rcases cut with ⟨cut,after⟩
  cases cut with
  | returned value =>
    simp only [RegistrationNativeIdentityTemplateSelectionCut.Original.erased,RegistrationNativeIdentityTemplateGuardedLateIdentity.resume,
      simulateQ_pure,StateT.run_pure,map_pure,continuation]
  | selected message continued =>
    simp only [RegistrationNativeIdentityTemplateSelectionCut.Original.erased,
      RegistrationNativeIdentityTemplatePublicPrefix.project,continuation]
    cases row : after.2.pool.seeds[selected]? with
    | none =>
      simp only [RegistrationNativeIdentityTemplateGuardedLateIdentity.resume,keys,row,Option.map_none,
        simulateQ_pure,StateT.run_pure,map_pure,RegistrationNativeIdentityTemplateLatePhysical.continuation]
      split <;> rfl
    | some seed =>
      have known : keys joint after.2.pool selected = some (joint.publicKeys seed) := by simp only [keys,row,Option.map_some]
      cases chosen : RegistrationNativeIdentityCensorPolicySource.choose message after.1 with
      | mk decision picked =>
        cases decision with
        | false =>
          rw [RegistrationNativeIdentityTemplateGuardedLateIdentity.negative joint selected message
            (fun reply => simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) (continued reply))
            (keys joint after.2.pool) (joint.publicKeys seed) known
            (after.1,RegistrationNativeIdentityTemplatePublicCtx.install after.2.hash) picked chosen]
          simp only [simulateQ_pure,StateT.run_pure,map_pure]
          rfl
        | true =>
          rw [RegistrationNativeIdentityTemplateGuardedLateIdentity.positive joint selected message
            (fun reply => simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) (continued reply))
            (keys joint after.2.pool) (joint.publicKeys seed) known
            (after.1,RegistrationNativeIdentityTemplatePublicCtx.install after.2.hash) picked chosen]
          simp only [RegistrationNativeIdentityTemplateLateIdentity.resume,known,RegistrationNativeIdentityTemplateLatePhysical.continuation,
            row,simulateQ_map,StateT.run_map,Functor.map_map,
            RegistrationNativeIdentityTemplateOmissionPublic.execute,RegistrationNativeIdentityTemplateOmissionPublic.client,
            RegistrationNativeIdentityTemplateSelectionCut.Original.resume,simulateQ_bind,simulateQ_spec_query,
            RegistrationNativeIdentityTemplateCensorRecognition.erase,RegistrationNativeIdentityTemplateSelectionCut.resume]
          rfl

private theorem raw_success (joint : Primitives) (identity : PqxdhJointIdentity.PublicIdentity)
    (result : RegistrationNativeIdentityAdaptiveHashCapture.Candidate joint identity ⊕ Option Found) :
    ((RegistrationNativeIdentityTemplateLateIdentity.raw joint identity result).isSome = true) =
      RegistrationNativeIdentityTemplateOmissionPublic.Succeeds
        (fun found => (RegistrationNativeIdentityCensorPacketClient.candidate joint identity found).isSome = true) result := by
  cases result with
  | inl candidate => simp only [RegistrationNativeIdentityTemplateLateIdentity.raw,Option.isSome_some,RegistrationNativeIdentityTemplateOmissionPublic.Succeeds]
  | inr found => simp only [RegistrationNativeIdentityTemplateLateIdentity.raw,Option.isSome_map,RegistrationNativeIdentityTemplateOmissionPublic.Succeeds]

private theorem physical_loss {S V I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S) (missing : before.1.2.target = none)
    (privateBefore : RegistrationNativeIdentityTemplateVisitorProbability.Private)
    (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2) :
    Pr{let result ← (RegistrationNativeIdentityTemplateVisitorProbability.coupled setup.joint selected bundle accept placeholder frontend defaults work before privateBefore)}[
      RegistrationNativeIdentityTemplateLatePhysical.Success setup.joint selected result.1 result.2.1] ≤
    Pr{let result ← (upper setup.joint selected bundle accept placeholder frontend defaults work before privateBefore)}[result.isSome = true] := by
  classical
  simp only [RegistrationNativeIdentityTemplateVisitorProbability.coupled,upper]
  apply prEvent_bind_mono_of_forall_le_of_support
  intro cut reached
  simp only [bind_pure_comp,prEvent_map]
  rcases cut with ⟨cut,after⟩
  cases cut with
  | returned value =>
    simp only [RegistrationNativeIdentityTemplateLatePhysical.Success,prEvent_false]
    exact zero_le
  | selected message continued =>
    cases row : after.2.pool.seeds[selected]? with
    | none =>
      simp only [RegistrationNativeIdentityTemplateLatePhysical.Success,row,prEvent_false]
      exact zero_le
    | some seed =>
      simp only [RegistrationNativeIdentityTemplateLatePhysical.Success,row]
      by_cases fresh : message ∉ RegistrationNativeIdentityCensorPolicySource.messages selected after.2.pool
      · have ready := (RegistrationNativeIdentityTemplateIssuedGame.first_cut setup.joint selected bundle accept placeholder frontend defaults work before missing
          privateBefore prior journal message continued after reached).1
        have publicNone : after.1.target = none := ready.aligned.1.trans ready.missing
        have publicFresh : message ∉ after.1.forwarded := by
          simpa only [ready.aligned.2 publicNone] using fresh
        have chosen : RegistrationNativeIdentityCensorPolicySource.choose message after.1 = (true,{after.1 with target := some message}) := by
          simp [RegistrationNativeIdentityCensorPolicySource.choose,publicNone,publicFresh]
        simp only [fresh,not_false_eq_true,true_and,continuation,chosen,ite_true,
          RegistrationNativeIdentityTemplateLatePhysical.continuation,row,prEvent_map,raw_success]
        simpa only [RegistrationNativeIdentityTemplateSelectionCut.Original.resume] using
          RegistrationNativeIdentityTemplateIssuedGame.cut_loss setup selected bundle accept placeholder frontend defaults work before missing privateBefore prior journal
            message continued after reached seed row fresh
              (fun found => (RegistrationNativeIdentityCensorPacketClient.candidate setup.joint (setup.joint.publicKeys seed) found).isSome = true)
      · simp only [fresh,false_and,prEvent_false]
        exact zero_le

/-- The actual fresh reached source event is bounded by the guarded executable public client. Its accepted first choice is DERIVED from actual source alignment and freshness, rather than required of the real experiment. -/
theorem loss {S V I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S) (missing : before.1.2.target = none)
    (privateBefore : RegistrationNativeIdentityTemplateVisitorProbability.Private)
    (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2) :
    Pr{let result ← (RegistrationNativeIdentityTemplateVisitorProbability.coupled setup.joint selected bundle accept placeholder frontend defaults work before privateBefore)}[
      RegistrationNativeIdentityTemplateLatePhysical.Success setup.joint selected result.1 result.2.1] ≤
    Pr{let result ← ((simulateQ (source setup.joint)
      (program setup.joint selected
        (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
          (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
        (keys setup.joint privateBefore.2.pool)
        (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool)}[
      result.1.1.isSome = true] := by
  have bound := physical_loss setup selected bundle accept placeholder frontend defaults work before missing privateBefore prior journal
  have same := congrArg (fun distribution => Pr{let result ← distribution}[result.isSome = true])
    (upper_source setup.joint selected bundle accept placeholder frontend defaults work before missing privateBefore)
  simp only [prEvent_map] at same
  rw [←same] at bound
  exact bound

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateSource.execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateSource.execution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateSource.upper_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateSource.upper_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateSource.loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateSource.loss
