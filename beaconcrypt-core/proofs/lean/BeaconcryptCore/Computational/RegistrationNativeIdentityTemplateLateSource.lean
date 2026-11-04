-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistrySource
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLatePhysical
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateFamily
/-! The identity-free public late-key program has the same physical first-selector prefix and recovers its actual recognition key from the public create-reply registry. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateSource
open PqxdhJointIdentity (Primitives)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec source)
open RegistrationNativeIdentityTemplatePolicy (Public)
open RegistrationNativeIdentityTemplatePublicRegistry (Registry keys)
open RegistrationNativeIdentityCensorPacketClient (Found)
variable {A : Type}

/-- The actual public source runs the identity-free prefix and then looks up its same reached public key. Every local policy/cache coordinate and full source pool remains attached. -/
theorem execution (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found))
    (publicBefore : Public) (before : PqxdhDynamicIdentityPool.SourceState) :
    (simulateQ (source joint) (RegistrationNativeIdentityTemplateLateFamily.program joint selected work (keys joint before) publicBefore)).run before = (do
      let cut ← (simulateQ (source joint)
        ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
          (RegistrationNativeIdentityTemplateSelectionCut.stop work)).run publicBefore)).run before
      (simulateQ (source joint)
        ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
          (RegistrationNativeIdentityTemplateLateIdentity.resume joint selected cut.1.1 (keys joint cut.2))).run cut.1.2)).run cut.2) := by
  unfold RegistrationNativeIdentityTemplateLateFamily.program
  rw [RegistrationNativeIdentityTemplateLateIdentity.factor]
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
        (RegistrationNativeIdentityTemplateLateFamily.program joint selected
          (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
            (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
          (keys joint privateBefore.2.pool)
          (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool =
      RegistrationNativeIdentityTemplateLatePhysical.upper joint selected bundle accept placeholder frontend defaults work before privateBefore := by
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
  unfold RegistrationNativeIdentityTemplateLatePhysical.upper
  apply bind_congr
  intro cut
  rcases cut with ⟨cut,after⟩
  cases cut with
  | returned value =>
    simp only [RegistrationNativeIdentityTemplateSelectionCut.Original.erased,RegistrationNativeIdentityTemplateLateIdentity.resume,
      simulateQ_pure,StateT.run_pure,map_pure,RegistrationNativeIdentityTemplateLatePhysical.continuation]
  | selected message continued =>
    simp only [RegistrationNativeIdentityTemplateSelectionCut.Original.erased,RegistrationNativeIdentityTemplateLateIdentity.resume,
      RegistrationNativeIdentityTemplatePublicPrefix.project,keys,RegistrationNativeIdentityTemplateLatePhysical.continuation]
    cases row : after.2.pool.seeds[selected]? with
    | none => simp only [Option.map_none,simulateQ_pure,StateT.run_pure,map_pure]
    | some seed =>
      simp only [Option.map_some,simulateQ_map,StateT.run_map,Functor.map_map,
        RegistrationNativeIdentityTemplateOmissionPublic.execute,RegistrationNativeIdentityTemplateOmissionPublic.client,
        RegistrationNativeIdentityTemplateSelectionCut.Original.resume,simulateQ_bind,simulateQ_spec_query,
        RegistrationNativeIdentityTemplateCensorRecognition.erase,RegistrationNativeIdentityTemplateSelectionCut.resume]
      rfl

/-- The complete actual first-omission source loss is bounded by candidate extraction in the executable identity-free public program, with its key registry learned from actual prior replies. -/
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
      (RegistrationNativeIdentityTemplateLateFamily.program setup.joint selected
        (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
          (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
        (keys setup.joint privateBefore.2.pool)
        (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool)}[
      result.1.1.isSome = true] := by
  have bound := RegistrationNativeIdentityTemplateLatePhysical.loss setup selected bundle accept placeholder frontend defaults work before missing privateBefore prior journal
  have same := congrArg (fun distribution => Pr{let result ← distribution}[result.isSome = true])
    (upper_source setup.joint selected bundle accept placeholder frontend defaults work before missing privateBefore)
  simp only [prEvent_map] at same
  rw [←same] at bound
  exact bound

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateSource.execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateSource.execution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateSource.upper_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateSource.upper_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateSource.loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateSource.loss
