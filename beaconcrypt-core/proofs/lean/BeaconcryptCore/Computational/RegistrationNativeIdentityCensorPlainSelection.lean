-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLatePhysical
/-! Erasing only the executable forwarding-policy ghost from the first-selector receipt leaves the exact literal private-source stop/resume coupling and the same physical success probability. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelection
open RegistrationNativeIdentityTemplateSelectionCut.Original (Old Cut stop resume)
open RegistrationNativeIdentityCensorSource (State)
open RegistrationNativeRawAdapter (TypedSpec)
variable {A S : Type}

noncomputable def coupled (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (work : OracleComp Old A) (before : State) := do
  let cut ← (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) (stop work)).run before
  let final ← (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) (resume cut.1)).run cut.2
  pure (cut,final)

def project (result : (Cut A × (RegistrationNativeIdentityAdaptiveCensor.Policy × State)) × (A × State)) :=
  ((result.1.1,result.1.2.2),result.2)

def Success (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (result : (Cut (Option RegistrationNativeIdentityCensorPacketClient.Found) × State) ×
      (Option RegistrationNativeIdentityCensorPacketClient.Found × State)) : Prop :=
  match result.1.1 with
  | .returned _=>False
  | .selected message _=>match result.1.2.pool.seeds[selected]? with
    | none=>False
    | some seed=>message∉RegistrationNativeIdentityCensorPolicySource.messages selected result.1.2.pool ∧
      (RegistrationNativeIdentityCensorPacketClient.candidate joint (joint.publicKeys seed) result.2.1).isSome=true

/-- Only the public forwarding-policy coordinate is erased. The exact original first-selector continuation and complete reached private source state remain joint. -/
theorem source (joint : PqxdhJointIdentity.Primitives) (selected bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S)
    (privateBefore : RegistrationNativeIdentityAdaptiveCensor.Policy × State) :
    project <$>RegistrationNativeIdentityTemplateVisitorProbability.coupled joint selected bundle accept placeholder frontend defaults work before privateBefore=
      coupled joint selected placeholder (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before) privateBefore.2 := by
  unfold RegistrationNativeIdentityTemplateVisitorProbability.coupled coupled
  simp only [map_bind,map_pure]
  rw [←RegistrationNativeIdentityCensorPolicySource.program_erasure joint selected placeholder
    (stop (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)) privateBefore,bind_map_left]
  rfl

/-- The checked ordinary reduction's physical event is exactly the success event on this same plain source coupling, with no history or candidate premise. -/
theorem probability (joint : PqxdhJointIdentity.Primitives) (selected bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S)
    (privateBefore : RegistrationNativeIdentityAdaptiveCensor.Policy × State) :
    Pr{let result←(coupled joint selected placeholder (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before) privateBefore.2)}[
      Success joint selected result]=
    Pr{let result←(RegistrationNativeIdentityTemplateVisitorProbability.coupled joint selected bundle accept placeholder frontend defaults work before privateBefore)}[
      RegistrationNativeIdentityTemplateLatePhysical.Success joint selected result.1 result.2.1] := by
  rw [←source,prEvent_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelection.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelection.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelection.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelection.probability
