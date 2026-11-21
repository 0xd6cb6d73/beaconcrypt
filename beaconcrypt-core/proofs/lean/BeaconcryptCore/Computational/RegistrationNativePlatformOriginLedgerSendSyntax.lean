-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSecrecy
/-! The literal secrecy ledger has only experiment coins followed by refusal or one actual native send, with exactly the same optional public reply and complete updated ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendSyntax
open PqxdhDeploymentInterface (Spec FullSpec Handle FreshBounds)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl send uniformBytes coin drawBit)
variable {A X Reader Response : Type}
abbrev Reply := Option RawCtxSourceSend.Encrypted

inductive SendSyntax (reply : A → Reply) : OracleComp Spec A → Prop where
  | refused (value : A) (absent : reply value=none) : SendSyntax reply (pure value)
  | send (handle : Handle) (message : Pqxdh.Bytes) (after : Reply → A)
      (same : ∀output,reply (after output)=output) : SendSyntax reply (after <$>PqxdhDeploymentSecrecy.send handle message)
  | coin (bound : Nat) (next : Fin (bound+1) → OracleComp Spec A)
      (later : ∀value,SendSyntax reply (next value)) : SendSyntax reply ((Spec.query (.inl bound) : OracleComp Spec _) >>=next)

/-- Pure result transport preserves the exact same public optional send reply and every coin prefix. -/
theorem SendSyntax.map {B : Type} {observe : A → Reply} {work : OracleComp Spec A}
    (syntaxProof : SendSyntax observe work) (change : A → B) (afterReply : B → Reply)
    (same : ∀value,afterReply (change value)=observe value) :
    SendSyntax afterReply (change <$>work) := by
  induction syntaxProof with
  | refused value absent=>
    rw [map_pure]
    exact .refused _ ((same value).trans absent)
  | send handle message after observed=>
    rw [Functor.map_map]
    exact .send handle message _ (fun output=>(same (after output)).trans (observed output))
  | coin bound next _later ih=>
    rw [map_bind]
    exact .coin bound _ ih

inductive Sending : FullSpec.Domain → Prop where
  | server (keyId : U64) (message : Pqxdh.Bytes) : Sending (.inl (.inr (.serverSend keyId message)))
  | beacon (owner : Nat) (message : Pqxdh.Bytes) : Sending (.inl (.inr (.beaconSend owner message)))
  | test (handle : Handle) (left right : Pqxdh.Bytes) : Sending (.inr (.test handle left right))
  | fresh (handle : Handle) (length : Nat) : Sending (.inr (.fresh handle length))

def reply : (query : FullSpec.Domain) → FullSpec.Range query → Reply
  | .inl (.inr (.serverSend ..)),output=>output
  | .inl (.inr (.beaconSend ..)),output=>output
  | .inr (.test ..),output=>output
  | .inr (.fresh ..),output=>output
  | _,_=>none

/-- Every actual uniform-byte experiment prefix keeps its original coins and then its literal dependent continuation. -/
theorem uniform_prefix (observe : A → Reply) (length : Nat) (next : Pqxdh.Bytes → OracleComp Spec A)
    (later : ∀message,SendSyntax observe (next message)) :
    SendSyntax observe (uniformBytes length >>=next) := by
  induction length generalizing next with
  | zero=>simpa only [uniformBytes,pure_bind] using later []
  | succ length ih=>
    simp only [uniformBytes,PqxdhDeploymentSecrecy.coin,bind_assoc,pure_bind]
    apply SendSyntax.coin
    intro value
    exact ih _ (fun rest=>later (UInt8.ofNat value.val::rest))

/-- All four original send-producing classes are coin-only prefixes followed by refusal or their one real native send. Public replies and complete ledger updates are preserved exactly. -/
theorem ledger_syntax (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : U64) (bounds : FreshBounds) (query : FullSpec.Domain) (sending : Sending query) (before : Ledger) :
    SendSyntax (fun result=>reply query result.1) ((ledgerImpl crypto codec serverKeyId bounds query).run before) := by
  classical
  cases sending with
  | server keyId message=>
    change SendSyntax _ ((fun output=>(output,before.record (.inl (.inr (.serverSend keyId message))) output)) <$>
      send (.peer keyId) message)
    exact .send _ _ _ (fun _=>rfl)
  | beacon owner message=>
    change SendSyntax _ ((fun output=>(output,before.record (.inl (.inr (.beaconSend owner message))) output)) <$>
      send (.owner owner) message)
    exact .send _ _ _ (fun _=>rfl)
  | test handle left right=>
    by_cases admissible : PqxdhDeploymentSecrecy.Admissible left right
    · cases held : before.test with
      | none=>
        simp only [ledgerImpl,StateT.run,admissible,ite_true,held,drawBit,PqxdhDeploymentSecrecy.coin,bind_map_left,bind_pure_comp]
        apply SendSyntax.coin
        intro value
        exact .send _ _ _ (fun _=>rfl)
      | some session=>
        by_cases same : PqxdhDeploymentSecrecy.SameSession crypto codec serverKeyId before.transcript session.first handle
        · simp only [ledgerImpl,StateT.run,admissible,ite_true,held,same,bind_pure_comp]
          exact .send _ _ _ (fun _=>rfl)
        · simp only [ledgerImpl,StateT.run,admissible,ite_true,held,same,ite_false]
          exact .refused _ rfl
    · simp only [ledgerImpl,StateT.run,admissible,ite_false]
      exact .refused _ rfl
  | fresh handle length=>
    by_cases admitted : bounds.min≤length ∧ length≤bounds.max
    · simp only [ledgerImpl,StateT.run,admitted]
      apply uniform_prefix
      intro message
      rw [bind_pure_comp]
      exact .send _ _ _ (fun _=>rfl)
    · simp only [ledgerImpl,StateT.run,admitted,ite_false]
      exact .refused _ rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendSyntax
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendSyntax.uniform_prefix' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendSyntax.uniform_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendSyntax.ledger_syntax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendSyntax.ledger_syntax

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendSyntax.SendSyntax.map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendSyntax.SendSyntax.map
