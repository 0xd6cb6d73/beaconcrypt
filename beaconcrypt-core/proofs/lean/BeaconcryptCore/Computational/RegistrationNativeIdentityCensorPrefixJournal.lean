-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal

/-! Before the fixed bundle guess is armed, the client recorder equals the entire physical input journal. This includes warm startup inputs and every failed source callback; the selected prefix scan therefore covers every existing physical cache address. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPrefix (SourceSpec record)
open RegistrationNativeIdentityCensorSource (State)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {Value : Type}

def Aligned (mode : Mode) (before : State) : Prop := mode.knownInputs = before.hash.2

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : SourceSpec.Domain) (mode : Mode) (before : State) (prior : Aligned mode before)
    (result : (SourceSpec.Range request × Mode) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode))).run before)) :
    Aligned result.1.2 result.2 := by
  cases request with
  | inl protocol =>
    simp only [record, StateT.run, bind_pure_comp, simulateQ_map, RegistrationNativeIdentityCensorPrefix.embed,
      RegistrationNativeIdentityCensorCompiler.protocol, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol, map_apply, Functor.map_map, support_map] at supported
    obtain ⟨actual, _called, rfl⟩ := supported
    exact prior
  | inr input =>
    simp only [record, StateT.run, bind_pure_comp, simulateQ_map, RegistrationNativeIdentityCensorPrefix.embed,
      simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.physical, map_apply, Functor.map_map, support_map] at supported
    obtain ⟨actual, called, rfl⟩ := supported
    have journal := RegistrationNativePlatformCtxBackend.physical_journal input before.hash actual called
    exact (congrArg (fun inputs => inputs ++ [input]) prior).trans journal.symm

private theorem recorded (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp SourceSpec Value) (mode : Mode) (before : State) (prior : Aligned mode before)
    (result : (Value × Mode) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (simulateQ RegistrationNativeIdentityCensorOperational.embed ((simulateQ record work).run mode))).run before)) :
    Aligned result.1.2 result.2 := by
  induction work using OracleComp.inductionOn generalizing mode before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  | query_bind request next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind, simulateQ_bind,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    exact ih middle.1.1 middle.1.2 middle.2 (query joint selected placeholder request mode before prior middle called) result continued

/-- The literal source recorder preserves the full physical journal relation for arbitrary mode controls, including an armed prefix before selection. -/
theorem recorded_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp SourceSpec Value) (mode : Mode) (before : State) (prior : Aligned mode before)
    (result : (Value × Mode) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (simulateQ RegistrationNativeIdentityCensorOperational.embed ((simulateQ record work).run mode))).run before)) :
    Aligned result.1.2 result.2 :=
  recorded joint selected placeholder work mode before prior result supported

/-- All client-known inputs are exactly the same warm physical journal throughout a literal unarmed adaptive source computation. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp SourceSpec Value) (mode : Mode) (before : State) (prior : Aligned mode before)
    (unarmed : RegistrationNativeIdentityCensorPrefix.Unarmed mode) (result : (Value × Mode) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before)) :
    Aligned result.1.2 result.2 := by
  rw [RegistrationNativeIdentityCensorOperationalPrefix.program selected placeholder work mode unarmed] at supported
  exact recorded joint selected placeholder work mode before prior result supported

/-- A negative result from the literal public prefix scanner covers every earlier physical input, using the derived recorder equality. -/
theorem scan (joint : PqxdhJointIdentity.Primitives) (identity : PqxdhJointIdentity.PublicIdentity) (message : Pqxdh.Bytes)
    (mode : Mode) (before : State) (prior : Aligned mode before)
    (missing : RegistrationNativeIdentityRecognitionJournal.scan joint.verify identity.ed25519 message mode.knownInputs = none) :
    ∀ input ∈ before.hash.2, RegistrationNativeIdentityRecognition.recognize joint.verify identity.ed25519 message input = none := by
  intro input member
  apply List.findSome?_eq_none_iff.mp missing input
  rw [prior]
  exact member

section Main
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}

/-- Main retains this same full-journal equality, including every actual native/P callback effect before selection. -/
theorem main (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source Value)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source))
    (prior : Aligned before.1.2 before.2) (unarmed : RegistrationNativeIdentityCensorPrefix.Unarmed before.1.2)
    (result : Value × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source))
    (supported : result ∈ support ((interpret joint selected placeholder true work).run before)) :
    Aligned result.2.1.2 result.2.2 := by
  simp only [interpret, StateT.run, ite_true, mem_support_bind_iff] at supported
  obtain ⟨returned, called, completed⟩ := supported
  obtain rfl := eq_of_mem_support_pure _ completed
  exact program joint selected placeholder (work.run before.1.1) before.1.2 before.2 prior unarmed returned called
/-- Every actual callback strictly before the fixed bundle guess preserves the exact client/physical journal relation, including parsed failures and failed writers. -/
theorem callback (joint : PqxdhJointIdentity.Primitives) (selected position : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source))
    (prior : Aligned before.1.2 before.2) (target : before.1.2.target = none) (earlier : before.1.2.bundles < position)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source))
    (supported : result ∈ support ((RegistrationNativeIdentityCensorPublicSource.callback
      (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend) query).run before)) :
    Aligned result.2.1.2 result.2.2 := by
  have entered := RegistrationNativeIdentityCensorUnarmedMain.enter position query before.1.2 target
    (fun _ _ => Nat.ne_of_lt earlier)
  have recorded : Aligned (RegistrationNativeIdentityCensorCompiler.enter position query before.1.2) before.2 := by
    rcases query with query | command
    · exact prior
    · cases command <;> exact prior
  have law := RegistrationNativeIdentityCensorPublicSource.current joint selected position placeholder true frontend query before
  simp only [ite_true] at law
  rw [law] at supported
  exact main joint selected placeholder (frontend query)
    ((before.1.1, RegistrationNativeIdentityCensorCompiler.enter position query before.1.2), before.2) recorded entered result supported

end Main

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal.main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal.main

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal.scan' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal.scan

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal.recorded_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal.recorded_program
