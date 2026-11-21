-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins
/-! The actual guarded public program extracts only genuine fresh valid forgeries. Its entire original source prefix, final audit and warm cache remain in the same distribution. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins
open PqxdhJointIdentity (Primitives PublicIdentity)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec erase recognize)
open RegistrationNativeIdentityTemplateProtocol (source)
open RegistrationNativeIdentityTemplatePolicy (Public execute)
open RegistrationNativeIdentityTemplatePublicRegistry (keys)
open RegistrationNativeIdentityCensorPacketClient (Found)
open RegistrationNativeIdentityTemplateVisitorProbability (Private)
open RegistrationNativeIdentityTemplateLateIdentity (Witness)
open RegistrationNativeIdentityTemplateSelectionCut.Original (Cut)
variable {S V : Type}

/-- Full source-state factorization at the SAME original reached first selector, before late key discovery and captured suffix execution. -/
theorem first_source (joint : Primitives) (selected bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S) (missing : before.1.2.target=none)
    (privateBefore : Private) :
    (simulateQ (source joint)
      (RegistrationNativeIdentityTemplateGuardedLateSource.program joint selected
        (simulateQ (erase placeholder) (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
        (keys joint privateBefore.2.pool)
        (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool = (do
      let cut ← (simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
        (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
          (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore
      execute joint selected
        (RegistrationNativeIdentityTemplateGuardedLateIdentity.resume joint selected
          (RegistrationNativeIdentityTemplateSelectionCut.Original.erased placeholder cut.1) (keys joint cut.2.2.pool))
        ((cut.2.1,RegistrationNativeIdentityTemplateFirstOmitted.install cut.2.2),cut.2.2.pool)) := by
  rw [RegistrationNativeIdentityTemplateGuardedLateSource.execution]
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
            (simulateQ (erase placeholder)
              (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)))).run
          (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool := by
    simpa only [RegistrationNativeIdentityTemplatePublicPrefix.project,RegistrationNativeIdentityTemplatePublicCtx.install,
      RegistrationNativeIdentityTemplateFirstOmitted.install,show (fun value :
        (RegistrationNativeIdentityTemplateSelectionCut.Cut (Option Found) × Public) × PqxdhDynamicIdentityPool.SourceState => value)=id from rfl,id_map] using observed
  rw [←shared,bind_map_left]
  rfl

private theorem bind_apply {X Y State : Type} {m : Type → Type} [Monad m]
    (work : StateT State m X) (next : X → StateT State m Y) (before : State) :
    (work >>= next) before=(do let result ← work before;next result.1 result.2) := rfl

private theorem map_apply {X Y State : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT State m X) (before : State) :
    (f <$> work) before=Prod.map f id <$> work before := StateT.run_map f work before

private theorem resume_positive (joint : Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (message : Pqxdh.Bytes)
    (continued : Bool → OracleComp RegistrationNativeIdentityCensorOperational.Spec (Option Found))
    (after : Private) (identity : PublicIdentity)
    (known : keys joint after.2.pool selected=some identity)
    (picked : RegistrationNativeIdentityAdaptiveCensor.Policy)
    (choice : RegistrationNativeIdentityCensorPolicySource.choose message after.1=(true,picked)) :
    execute joint selected
      (RegistrationNativeIdentityTemplateGuardedLateIdentity.resume joint selected
        (RegistrationNativeIdentityTemplateSelectionCut.Original.erased placeholder (Cut.selected message continued)) (keys joint after.2.pool))
      ((after.1,RegistrationNativeIdentityTemplateFirstOmitted.install after.2),after.2.pool) =
    (fun result => ((RegistrationNativeIdentityTemplateLateIdentity.raw joint identity result.1.1,result.1.2),result.2)) <$>
      execute joint selected
        (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint identity) (simulateQ (erase placeholder) (continued true)))
        ((picked,RegistrationNativeIdentityTemplateFirstOmitted.install after.2),after.2.pool) := by
  simp only [execute,RegistrationNativeIdentityTemplateGuardedLateIdentity.resume,
    RegistrationNativeIdentityTemplateSelectionCut.Original.erased,known,simulateQ_bind,simulateQ_spec_query,
    RegistrationNativeIdentityTemplatePolicy.handler,StateT.run,bind_apply,choice,pure_bind,ite_true,
    simulateQ_map,map_apply]
  rfl

/-- Every returned candidate of the actual guarded program wins against its complete genuine selected-handle history. The fixed-message scope and positive fresh choice are derived from the actual source cut. -/
theorem supported {S V : Type} (joint : Primitives) (selected bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S) (missing : before.1.2.target=none)
    (privateBefore : Private) (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2)
    (result : (Option Witness × Public) × PqxdhDynamicIdentityPool.SourceState)
    (reached : result ∈ support ((simulateQ (source joint)
      (RegistrationNativeIdentityTemplateGuardedLateSource.program joint selected
        (simulateQ (erase placeholder) (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
        (keys joint privateBefore.2.pool)
        (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool)) :
    ∀ candidate,result.1.1=some candidate→
      PqxdhJointIdentity.wins joint candidate.1 candidate.2
        (RegistrationNativeIdentityHistory.history selected result.2.transcript)=true := by
  rw [first_source joint selected bundle accept placeholder frontend defaults work before missing privateBefore,mem_support_bind_iff] at reached
  obtain ⟨cut,called,observed⟩ := reached
  rcases cut with ⟨cut,after⟩
  cases cut with
  | returned value =>
    simp only [RegistrationNativeIdentityTemplateSelectionCut.Original.erased,RegistrationNativeIdentityTemplateGuardedLateIdentity.resume,
      execute,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at observed
    cases observed
    intro candidate impossible
    cases impossible
  | selected message continued =>
    cases row : keys joint after.2.pool selected with
    | none =>
      simp only [RegistrationNativeIdentityTemplateSelectionCut.Original.erased,RegistrationNativeIdentityTemplateGuardedLateIdentity.resume,
        row,execute,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at observed
      cases observed
      intro candidate impossible
      cases impossible
    | some identity =>
      cases choice : RegistrationNativeIdentityCensorPolicySource.choose message after.1 with
      | mk decision picked =>
        cases decision with
        | false =>
          simp only [execute,RegistrationNativeIdentityTemplateSelectionCut.Original.erased,
            RegistrationNativeIdentityTemplateGuardedLateIdentity.resume,row,simulateQ_bind,simulateQ_spec_query,
            RegistrationNativeIdentityTemplatePolicy.handler,StateT.run,bind_apply,choice,pure_bind] at observed
          cases observed
          intro candidate impossible
          cases impossible
        | true =>
          rw [resume_positive joint selected placeholder message continued after identity row picked choice,support_map] at observed
          obtain ⟨middle,reached,rfl⟩ := observed
          intro candidate extracted
          have actual := RegistrationNativeIdentityTemplateCaptureWins.actual_witness joint selected bundle accept placeholder frontend defaults work before missing
            privateBefore prior journal message continued after called identity picked choice _ middle reached candidate extracted
          simpa only [actual.1] using actual.2.2

def GenuineWins (joint : Primitives) (selected : Nat)
    (result : (Option Witness × Public) × PqxdhDynamicIdentityPool.SourceState) : Bool :=
  result.1.1.any (fun candidate => PqxdhJointIdentity.wins joint candidate.1 candidate.2
    (RegistrationNativeIdentityHistory.history selected result.2.transcript))

/-- Candidate extraction in the actual guarded public program is bounded by genuine weak-EUF wins, with all final audit state retained. -/
theorem candidate_mass {S V : Type} (joint : Primitives) (selected bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S) (missing : before.1.2.target=none)
    (privateBefore : Private) (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2)
 :
    Pr{let result ← ((simulateQ (source joint)
      (RegistrationNativeIdentityTemplateGuardedLateSource.program joint selected
        (simulateQ (erase placeholder) (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
        (keys joint privateBefore.2.pool)
        (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool)}[result.1.1.isSome=true] ≤
      Pr{let result ← ((simulateQ (source joint)
      (RegistrationNativeIdentityTemplateGuardedLateSource.program joint selected
        (simulateQ (erase placeholder) (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
        (keys joint privateBefore.2.pool)
        (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool)}[GenuineWins joint selected result=true] := by
  apply prEvent_mono_of_support
  intro result reached hasCandidate
  cases returned : result.1.1 with
  | none => simp only [returned,Option.isSome_none,Bool.false_eq_true] at hasCandidate
  | some candidate =>
    have wins := supported joint selected bundle accept placeholder frontend defaults work before missing privateBefore prior journal result reached candidate returned
    simp only [GenuineWins,returned,Option.any_some,wins]


/-- The original same-cut fresh-row physical success has one guarded genuine-forgery probability bound. -/
theorem loss {S V I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (selected bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S) (missing : before.1.2.target=none)
    (privateBefore : Private) (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2)
 :
    Pr{let result ← (RegistrationNativeIdentityTemplateVisitorProbability.coupled setup.joint selected bundle accept placeholder frontend defaults work before privateBefore)}[
      RegistrationNativeIdentityTemplateLatePhysical.Success setup.joint selected result.1 result.2.1] ≤
      Pr{let result ← ((simulateQ (source setup.joint)
      (RegistrationNativeIdentityTemplateGuardedLateSource.program setup.joint selected
        (simulateQ (erase placeholder) (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
        (keys setup.joint privateBefore.2.pool)
        (privateBefore.1,RegistrationNativeIdentityTemplateFirstOmitted.install privateBefore.2))).run privateBefore.2.pool)}[GenuineWins setup.joint selected result=true] := by
  exact (RegistrationNativeIdentityTemplateGuardedLateSource.loss setup selected bundle accept placeholder frontend defaults work before missing privateBefore prior journal).trans
    (candidate_mass setup.joint selected bundle accept placeholder frontend defaults work before missing privateBefore prior journal)

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins.first_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins.first_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins.supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins.supported

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins.candidate_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins.candidate_mass

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins.loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedWins.loss
