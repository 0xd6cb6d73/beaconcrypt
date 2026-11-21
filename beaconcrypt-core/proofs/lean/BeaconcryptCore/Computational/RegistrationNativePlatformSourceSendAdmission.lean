-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordWorldClient
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission
open CborRecordWorldClient (nextFits Shell)
variable {n : Nat}
/-- The actual inclusive complete-frame check bounds the entire plaintext and its fixed authentication overhead. -/
theorem payload_bound (plaintext sequence sender : Nat) (fits : nextFits plaintext sequence sender=true) :
    plaintext+80≤CborSizing.maxMessageSize := by
  simp only [nextFits,decide_eq_true_eq] at fits
  unfold CborSizing.frameLen CborSizing.byteStringLen at fits
  omega
private theorem message_size : CborSizing.maxMessageSize≤Usize.max := by
  cases System.Platform.numBits_eq with
  | inl bits=>simp [CborSizing.maxMessageSize,Usize.max,Usize.numBits,UScalarTy.numBits,bits]
  | inr bits=>simp [CborSizing.maxMessageSize,Usize.max,Usize.numBits,UScalarTy.numBits,bits]
/-- Every admitted plaintext has a genuine source Slice length on either supported pointer width. -/
theorem representable (plaintext sequence sender : Nat) (fits : nextFits plaintext sequence sender=true) :
    plaintext≤Usize.max :=
  (Nat.le_add_right plaintext 80).trans ((payload_bound plaintext sequence sender fits).trans message_size)
/-- An existing actual Server peer can be forwarded only with a source-representable plaintext. -/
theorem server (shell : Shell) (selected : CborRecordWorldClient.Server) (keyId : U64)
    (plaintext : Pqxdh.Bytes) (sequence : Nat) (present : shell.server=some selected)
    (peer : selected.peers keyId=some sequence)
    (forwarded : CborRecordWorldClient.refusal (n:=n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell=none) :
    plaintext.length≤Usize.max := by
  cases fits : nextFits plaintext.length sequence selected.sender.val with
  | false=>simp only [CborRecordWorldClient.refusal,present,peer,fits,Bool.false_eq_true,ite_false,reduceCtorEq] at forwarded
  | true=>exact representable plaintext.length sequence selected.sender.val fits
/-- An existing actual Beacon cursor can be forwarded only with a source-representable plaintext. -/
theorem owner (shell : Shell) (selected : CborRecordWorldClient.Cursor) (index : Nat)
    (plaintext : Pqxdh.Bytes) (present : shell.owners index=some selected)
    (forwarded : CborRecordWorldClient.refusal (n:=n) (.inr (.inr (.inr (index,.inl plaintext)))) shell=none) :
    plaintext.length≤Usize.max := by
  cases fits : nextFits plaintext.length selected.sequence selected.sender.val with
  | false=>simp only [CborRecordWorldClient.refusal,present,fits,Bool.false_eq_true,ite_false,reduceCtorEq] at forwarded
  | true=>exact representable plaintext.length selected.sequence selected.sender.val fits
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission.payload_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission.payload_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission.representable' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission.representable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission.owner
