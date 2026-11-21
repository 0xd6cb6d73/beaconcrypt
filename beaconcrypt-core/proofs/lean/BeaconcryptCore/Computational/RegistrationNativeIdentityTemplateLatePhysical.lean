-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorProbability
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity
/-! The generated row used by the local omission bound is chosen at the actual reached selector. This integrates over the existing random seed table without an infinite union over seeds or a future-key-dependent client. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLatePhysical
open PqxdhJointIdentity (Primitives)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorPublicClient (ClientState)
open RegistrationNativeIdentityCensorPacketClient (Found)
open RegistrationNativeIdentityTemplateVisitorProbability (Private OriginalCut coupled)
open RegistrationNativeIdentityTemplateLateIdentity (Witness)
variable {A S : Type}
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec

def Success (joint : Primitives) (selected : Nat) (cut : OriginalCut (Option Found) × Private) (returned : Option Found) : Prop :=
  match cut.1 with
  | .returned _ => False
  | .selected message _ => match cut.2.2.pool.seeds[selected]? with
    | none => False
    | some seed => message ∉ RegistrationNativeIdentityCensorPolicySource.messages selected cut.2.2.pool ∧
        (RegistrationNativeIdentityCensorPacketClient.candidate joint (joint.publicKeys seed) returned).isSome = true

noncomputable def continuation (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (cut : OriginalCut (Option Found) × Private) : ProbComp (Option Witness) :=
  match cut.1 with
  | .returned _ => pure none
  | .selected _ _ => match cut.2.2.pool.seeds[selected]? with
    | none => pure none
    | some seed => (fun result => RegistrationNativeIdentityTemplateLateIdentity.raw joint (joint.publicKeys seed) result.1.1) <$>
        RegistrationNativeIdentityTemplateOmissionPublic.execute joint (joint.publicKeys seed) selected placeholder
          (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1) cut.2.1
          (RegistrationNativeIdentityTemplateFirstOmitted.install cut.2.2) cut.2.2.pool

noncomputable def upper (joint : Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (privateBefore : Private) : ProbComp (Option Witness) := do
  let cut ← (simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
    (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
      (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore
  continuation joint selected placeholder cut

private theorem raw_success (joint : Primitives) (identity : PqxdhJointIdentity.PublicIdentity)
    (result : RegistrationNativeIdentityAdaptiveHashCapture.Candidate joint identity ⊕ Option Found) :
    ((RegistrationNativeIdentityTemplateLateIdentity.raw joint identity result).isSome = true) =
      RegistrationNativeIdentityTemplateOmissionPublic.Succeeds
        (fun found => (RegistrationNativeIdentityCensorPacketClient.candidate joint identity found).isSome = true) result := by
  cases result with
  | inl candidate => simp only [RegistrationNativeIdentityTemplateLateIdentity.raw,Option.isSome_some,RegistrationNativeIdentityTemplateOmissionPublic.Succeeds]
  | inr found =>
    simp only [RegistrationNativeIdentityTemplateLateIdentity.raw,Option.isSome_map,RegistrationNativeIdentityTemplateOmissionPublic.Succeeds]

/-- Integrating the local loss chooses the actual existing row at each reached first selector. Row absence and no-selection paths contribute no source success; all failed callbacks and the same original continuation remain attached. -/
theorem loss {I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (missing : before.1.2.target = none) (privateBefore : Private)
    (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2) :
    Pr{let result ← (coupled setup.joint selected bundle accept placeholder frontend defaults work before privateBefore)}[
      Success setup.joint selected result.1 result.2.1] ≤
    Pr{let result ← (upper setup.joint selected bundle accept placeholder frontend defaults work before privateBefore)}[result.isSome = true] := by
  classical
  simp only [coupled,upper]
  apply prEvent_bind_mono_of_forall_le_of_support
  intro cut reached
  simp only [bind_pure_comp,prEvent_map]
  rcases cut with ⟨cut,after⟩
  cases cut with
  | returned value =>
    simp only [Success,continuation,prEvent_false,prEvent_pure,Option.isSome_none,Bool.false_eq_true,ite_false]
    exact le_rfl
  | selected message continued =>
    cases row : after.2.pool.seeds[selected]? with
    | none =>
      simp only [Success,continuation,row,prEvent_false,prEvent_pure,Option.isSome_none,Bool.false_eq_true,ite_false]
      exact le_rfl
    | some seed =>
      simp only [Success,continuation,row,prEvent_map,raw_success]
      by_cases fresh : message ∉ RegistrationNativeIdentityCensorPolicySource.messages selected after.2.pool
      · simp only [fresh,not_false_eq_true,true_and]
        simpa only [RegistrationNativeIdentityTemplateSelectionCut.Original.resume] using
          RegistrationNativeIdentityTemplateIssuedGame.cut_loss setup selected bundle accept placeholder frontend defaults work before missing privateBefore prior journal
            message continued after reached seed row fresh
              (fun found => (RegistrationNativeIdentityCensorPacketClient.candidate setup.joint (setup.joint.publicKeys seed) found).isSome = true)
      · simp only [fresh,false_and,prEvent_false]
        exact zero_le

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLatePhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLatePhysical.loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLatePhysical.loss
