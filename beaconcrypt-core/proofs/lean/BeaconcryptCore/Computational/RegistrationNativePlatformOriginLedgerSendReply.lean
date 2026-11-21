-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendSyntax
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendReply
open PqxdhDeploymentInterface (Spec FullSpec Handle FreshBounds)
open RegistrationNativePlatformOriginLedgerSendSyntax (Reply SendSyntax)
open RegistrationNativeStageTrace (Call)
variable {S A Reader Response : Type}

inductive Sending : Spec.Domain → Prop where
  | server (keyId : U64) (message : Pqxdh.Bytes) : Sending (.inr (.serverSend keyId message))
  | beacon (owner : Nat) (message : Pqxdh.Bytes) : Sending (.inr (.beaconSend owner message))

def nativeReply : (query : Spec.Domain) → Spec.Range query → Reply
  | .inr (.serverSend ..),output=>output
  | .inr (.beaconSend ..),output=>output
  | _,_=>none

private theorem inherited (implementation : QueryImpl Spec (StateT S ProbComp))
    {project : A → Reply} {work : OracleComp Spec A} (syntaxProof : SendSyntax project work)
    (before : S) (prior : List (Call Spec S)) (result : A × (S × List (Call Spec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,prior))) :
    ∀call∈result.2.2,Sending call.query → call∈prior ∨ nativeReply call.query call.reply=project result.1 := by
  induction syntaxProof generalizing before prior result with
  | refused value absent=>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    intro call member _
    exact Or.inl member
  | send handle message after same=>
    cases handle with
    | peer keyId=>
      simp only [PqxdhDeploymentSecrecy.send,simulateQ_map,simulateQ_spec_query] at supported
      change result ∈ support ((after <$> RegistrationNativeStageTrace.handler implementation (.inr (.serverSend keyId message))).run (before,prior)) at supported
      rw [StateT.run_map] at supported
      simp only [RegistrationNativeStageTrace.handler,StateT.run,Functor.map_map,support_map] at supported
      obtain ⟨inner,_called,equal⟩ := supported
      subst result
      intro call member _
      rcases List.mem_append.mp member with old | current
      · exact Or.inl old
      · simp only [List.mem_singleton] at current
        subst call
        exact Or.inr (same inner.1).symm
    | owner index=>
      simp only [PqxdhDeploymentSecrecy.send,simulateQ_map,simulateQ_spec_query] at supported
      change result ∈ support ((after <$> RegistrationNativeStageTrace.handler implementation (.inr (.beaconSend index message))).run (before,prior)) at supported
      rw [StateT.run_map] at supported
      simp only [RegistrationNativeStageTrace.handler,StateT.run,Functor.map_map,support_map] at supported
      obtain ⟨inner,_called,equal⟩ := supported
      subst result
      intro call member _
      rcases List.mem_append.mp member with old | current
      · exact Or.inl old
      · simp only [List.mem_singleton] at current
        subst call
        exact Or.inr (same inner.1).symm
  | coin bound next later ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    simp only [RegistrationNativeStageTrace.handler,StateT.run,support_map] at called
    obtain ⟨inner,_actual,equal⟩ := called
    subst middle
    intro call member sending
    rcases ih inner.1 inner.2 (prior++[⟨.inl bound,before,inner.1,inner.2⟩]) result continued call member sending with old | same
    · rcases List.mem_append.mp old with old | coin
      · exact Or.inl old
      · simp only [List.mem_singleton] at coin
        subst call
        cases sending
    · exact Or.inr same

/-- Every actual inner send in the same supported journal has exactly the outer optional reply, after arbitrary experiment coins and refusals. -/
theorem program (implementation : QueryImpl Spec (StateT S ProbComp))
    (project : A → Reply) (work : OracleComp Spec A) (syntaxProof : SendSyntax project work)
    (before : S) (result : A × (S × List (Call Spec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,[])))
    (call : Call Spec S) (member : call∈result.2.2) (sending : Sending call.query) :
    nativeReply call.query call.reply=project result.1 := by
  rcases inherited implementation syntaxProof before [] result supported call member sending with impossible | same
  · cases impossible
  · exact same

/-- All four original public send classes retain the exact optional native output in the full same-run source journal, including test and fresh prefixes. -/
theorem ledger (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (sending : RegistrationNativePlatformOriginLedgerSendSyntax.Sending query)
    (ledgerBefore : PqxdhDeploymentSecrecy.Ledger) (implementation : QueryImpl Spec (StateT S ProbComp)) (before : S)
    (result : (FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) × (S × List (Call Spec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation)
      ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKeyId bounds query).run ledgerBefore)).run (before,[])))
    (call : Call Spec S) (member : call∈result.2.2) (inner : Sending call.query) :
    nativeReply call.query call.reply=RegistrationNativePlatformOriginLedgerSendSyntax.reply query result.1.1 :=
  program implementation _ _ (RegistrationNativePlatformOriginLedgerSendSyntax.ledger_syntax crypto codec serverKeyId bounds query sending ledgerBefore)
    before result supported call member inner

/-- An inner refused native send is the same refused outer public send; unused later callbacks do not repair its reply. -/
theorem none (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (sending : RegistrationNativePlatformOriginLedgerSendSyntax.Sending query)
    (ledgerBefore : PqxdhDeploymentSecrecy.Ledger) (implementation : QueryImpl Spec (StateT S ProbComp)) (before : S)
    (result : (FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) × (S × List (Call Spec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation)
      ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKeyId bounds query).run ledgerBefore)).run (before,[])))
    (call : Call Spec S) (member : call∈result.2.2) (inner : Sending call.query)
    (refused : nativeReply call.query call.reply=none) :
    RegistrationNativePlatformOriginLedgerSendSyntax.reply query result.1.1=none :=
  (ledger crypto codec serverKeyId bounds query sending ledgerBefore implementation before result supported call member inner).symm.trans refused
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendReply
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendReply.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendReply.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendReply.ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendReply.ledger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendReply.none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendReply.none
