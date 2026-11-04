-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaMap

/-! Private ML keys are indexed by successful-generation handles. The additive opaque source supplies only the type of these handles and the unchanged verifier; its dummy closed generation/signing fields are never the interpreter used here. The actual private interpreter executes the original source leaves and retains their exact draw counts. Every generation attempt advances its ordinal, and all reached signing attempts retain complete operands and optional replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaCapability (Request Reply)
open RegistrationSigningShared (SignReply)
variable (source : Source)

abbrev handleSource : Source := ⟨Nat, pure none, (fun _ _ => pure .None), source.verify⟩

structure Attempt where
  handle : Nat
  publicKey : Std.Array Std.U8 1952#usize
  request : registration.MldsaSigningRequest
  reply : SignReply

structure Pool where
  keys : List (Credential source) := []
  bornAt : List Nat := []
  attempts : Nat := 0
  signing : List Attempt := []

def record (before : Pool source) (credential : Credential (handleSource source))
    (request : registration.MldsaSigningRequest) (reply : SignReply) : Pool source :=
  { before with signing := before.signing ++ [⟨credential.secret, credential.publicKey, request, reply⟩] }

def birth (before : Pool source) (generated : Option (Credential source) × Nat) :
    (Option (Credential (handleSource source)) × Nat) × Pool source :=
  match generated.1 with
  | none => ((none, generated.2), { before with attempts := before.attempts + 1 })
  | some credential => ((some ⟨credential.publicKey, before.keys.length⟩, generated.2),
      { before with keys := before.keys ++ [credential], bornAt := before.bornAt ++ [before.attempts], attempts := before.attempts + 1 })

noncomputable def actual : QueryImpl (RegistrationNativeMldsaCapability.Spec (handleSource source)) (StateT (Pool source) ProbComp) := by
  classical
  exact fun query => match query with
    | .generate => fun before => birth source before <$> RegistrationNativeMldsaCapability.actual source .generate
    | .sign credential request => fun before =>
        match before.keys[credential.secret]? with
        | none => pure ((.None, 0), record source before credential request .None)
        | some key => if credential.publicKey = key.publicKey then
            (fun result => (result, record source before credential request result.1)) <$>
              RegistrationNativeMldsaCapability.actual source (.sign key request)
          else pure ((.None, 0), record source before credential request .None)

def Live (before : Pool source) (handle : Credential (handleSource source)) (key : Credential source) : Prop :=
  before.keys[handle.secret]? = some key ∧ handle.publicKey = key.publicKey

/-- A fallback is needed only to make a total private representation map; live handles never use it. -/
def restore (fallback : Credential source) (before : Pool source) : RegistrationNativeMldsaMap.Map (handleSource source) source :=
  ⟨fun index => ((before.keys[index]?).getD fallback).secret⟩

theorem birth_attempt (before : Pool source) (generated : Option (Credential source) × Nat) :
    (birth source before generated).2.attempts = before.attempts + 1 := by
  rcases generated with ⟨generated, count⟩
  cases generated <;> rfl

theorem birth_live (before : Pool source) (key : Credential source) (count : Nat) :
    Live source (birth source before (some key, count)).2 ⟨key.publicKey, before.keys.length⟩ key := by
  exact ⟨List.getElem?_concat_length, rfl⟩

theorem birth_preserves (before : Pool source) (generated : Option (Credential source) × Nat)
    (handle : Credential (handleSource source)) (key : Credential source) (live : Live source before handle key) :
    Live source (birth source before generated).2 handle key := by
  rcases generated with ⟨generated, count⟩
  cases generated with
  | none => exact live
  | some added =>
      refine ⟨?_, live.2⟩
      have present := (List.getElem?_eq_some_iff.mp live.1).1
      exact (List.getElem?_append_left present).trans live.1

/-- Successful handle lookup restores the literal generated credential, without a key-injectivity condition. -/
theorem restore_live (fallback : Credential source) (before : Pool source)
    (handle : Credential (handleSource source)) (key : Credential source) (live : Live source before handle key) :
    RegistrationNativeMldsaMap.credential (restore source fallback before) handle = key := by
  cases handle with
  | mk publicKey index =>
      cases key with
      | mk original secret =>
          obtain ⟨found, same⟩ := live
          cases same
          simp only [RegistrationNativeMldsaMap.credential, restore, found, Option.getD_some]

/-- The exact optional result and actual primitive draw count determine the new private pool. -/
theorem generate_source (before : Pool source) :
    (actual source .generate).run before = birth source before <$> RegistrationNativeMldsaCapability.actual source .generate := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A reached owned handle invokes the literal original signer, including failed replies and its exact actual draw count. -/
theorem sign_source (before : Pool source) (handle : Credential (handleSource source)) (key : Credential source)
    (live : Live source before handle key) (request : registration.MldsaSigningRequest) :
    (actual source (.sign handle request)).run before =
      (fun result => (result, record source before handle request result.1)) <$>
        RegistrationNativeMldsaCapability.actual source (.sign key request) := by
  classical
  simp only [actual, StateT.run, live.1, live.2, ite_true]
  rfl

/-- Every reached attempt is appended before later controller continuations can reject. -/
theorem record_history (before : Pool source) (handle : Credential (handleSource source))
    (request : registration.MldsaSigningRequest) (reply : SignReply) :
    (record source before handle request reply).signing = before.signing ++ [⟨handle.secret, handle.publicKey, request, reply⟩] ∧
      (record source before handle request reply).keys = before.keys ∧
      (record source before handle request reply).attempts = before.attempts := ⟨rfl, rfl, rfl⟩

def Aligned (before : Pool source) : Prop := before.keys.length = before.bornAt.length

theorem birth_aligned (before : Pool source) (generated : Option (Credential source) × Nat) (aligned : Aligned source before) :
    Aligned source (birth source before generated).2 := by
  rcases generated with ⟨generated, count⟩
  cases generated with
  | none => exact aligned
  | some key =>
      simp only [Aligned, birth, List.length_append, List.length_singleton]
      exact congrArg (fun count => count + 1) aligned

theorem birth_ordinal (before : Pool source) (key : Credential source) (count : Nat) (aligned : Aligned source before) :
    (birth source before (some key, count)).2.bornAt[before.keys.length]? = some before.attempts := by
  change (before.bornAt ++ [before.attempts])[before.keys.length]? = some before.attempts
  rw [aligned]
  exact List.getElem?_concat_length

end BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.birth_attempt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.birth_attempt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.birth_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.birth_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.birth_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.birth_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.restore_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.restore_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.generate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.generate_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.sign_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.sign_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.record_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.record_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.birth_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.birth_aligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.birth_ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque.birth_ordinal
