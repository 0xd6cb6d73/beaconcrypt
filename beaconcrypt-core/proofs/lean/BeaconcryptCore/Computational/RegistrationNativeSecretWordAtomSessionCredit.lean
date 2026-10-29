-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialSessions

/-! Stored atom capabilities provide an exact one-use credit. Taking any native handle removes precisely its own possible atom credit before cancellation or any later failure; completion cannot create another stored reference. Equality of public keys or descriptor aliases does not identify different handles. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit
open RegistrationNativeSecretWordMessage (ServerReady ServerState)
open RegistrationNativeSecretWordServerMaterial (take)
variable {n : Nat}

def weight : Option ServerReady → Nat
  | none => 0
  | some ready => match ready.reference.kem with
      | .atom => 1
      | .literal _ => 0

def count : List (Option ServerReady) → Nat
  | [] => 0
  | entry :: rest => weight entry + count rest

/-- Appending one actual capability creates exactly its own possible atom credit. -/
theorem append (before after : List (Option ServerReady)) : count (before ++ after) = count before + count after := by
  induction before with
  | nil => simp only [List.nil_append, count, Nat.zero_add]
  | cons first rest ih => simp only [List.cons_append, count, ih, Nat.add_assoc]

/-- Every ordinary literal reference contributes zero atom credit. -/
theorem nonatom (ready : ServerReady) (ordinary : ready.reference.kem ≠ RegistrationNativeSecretWord.Word.atom) :
    weight (some ready) = 0 := by
  cases formed : ready.reference.kem with
  | atom => exact False.elim (ordinary formed)
  | literal value => simp only [weight, formed]

/-- The actual moved handle removes exactly its own credit, even when other handles have equal descriptors. -/
theorem set_credit (sessions : List (Option ServerReady)) (handle : Nat) (ready : ServerReady)
    (found : sessions[handle]? = some (some ready)) :
    count (sessions.set handle none) + weight (some ready) = count sessions := by
  induction sessions generalizing handle with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | cons first rest ih =>
      cases handle with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst first
          simp only [List.set_cons_zero, count, weight]
          omega
      | succ handle =>
          simp only [List.getElem?_cons_succ] at found
          have remaining := ih handle found
          simp only [List.set_cons_succ, count]
          omega

/-- Native take preserves total atom credit when its returned moved capability is included. -/
theorem take_credit (handle : Nat) (before : ServerState) :
    count (take handle before).2.sessions + weight (take handle before).1 = count before.sessions := by
  unfold take
  cases found : before.sessions[handle]? with
  | none => simp only [weight, Nat.add_zero]
  | some selected => cases selected with
    | none => simp only [weight, Nat.add_zero]
    | some ready => exact set_credit before.sessions handle ready found

/-- Every actual build consumes the moved atom credit before all later cancellation, preflight, publication and installation outcomes. -/
theorem build_credit (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (handle : Nat)
    (application : Option (Slice U8)) (before : ServerState)
    (result : RegistrationNativeSecretWordServerMaterial.Result × ServerState)
    (supported : result ∈ support ((RegistrationNativeSecretWordServerMaterial.build (n := n) wire reservePeer handle application).run before)) :
    count result.2.sessions + weight (take handle before).1 = count before.sessions := by
  rw [RegistrationNativeSecretWordMaterialSessions.build_sessions wire reservePeer handle application before result supported]
  exact take_credit handle before

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit.append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit.append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit.nonatom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit.nonatom
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit.set_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit.set_credit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit.take_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit.take_credit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit.build_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit.build_credit
