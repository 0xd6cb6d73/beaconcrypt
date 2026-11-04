-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque
import BeaconcryptCore.Computational.RegistrationNativeMldsaEuf

/-! A chosen generation attempt is represented by a public challenge tag; its private signing key is absent from wrapper state. Other generated keys remain ordinary private source keys. Selected signing forwards the complete owned request to the ordinary EUF oracle. The zero count on that external branch is explicitly private placeholder accounting; no equality with the actual complete source profile is asserted here. Such comparison requires an independently proved uniform-erasing native observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaChosen
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource Attempt)
open RegistrationSigningShared (SignReply)
open RegistrationNativeMldsaEuf (PublicKey)
variable (source : Source)

inductive Key where
  | ordinary (credential : Credential source)
  | challenge (publicKey : PublicKey)

structure Pool where
  keys : List (Key source) := []
  bornAt : List Nat := []
  attempts : Nat := 0
  signing : List Attempt := []

def coins : QueryImpl unifSpec (OracleComp RegistrationNativeMldsaEuf.Spec) :=
  fun query => RegistrationNativeMldsaEuf.Spec.query (.inl query)

def lift {Value : Type} (work : ProbComp Value) : OracleComp RegistrationNativeMldsaEuf.Spec Value := simulateQ coins work

def record (before : Pool source) (credential : Credential (handleSource source))
    (request : registration.MldsaSigningRequest) (reply : SignReply) : Pool source :=
  { before with signing := before.signing ++ [⟨credential.secret, credential.publicKey, request, reply⟩] }

def birth (before : Pool source) (generated : Option (Credential source) × Nat) :
    (Option (Credential (handleSource source)) × Nat) × Pool source :=
  match generated.1 with
  | none => ((none, generated.2), { before with attempts := before.attempts + 1 })
  | some credential => ((some ⟨credential.publicKey, before.keys.length⟩, generated.2),
      { before with keys := before.keys ++ [.ordinary credential], bornAt := before.bornAt ++ [before.attempts], attempts := before.attempts + 1 })

def challengeBirth (before : Pool source) (publicKey : PublicKey) :
    (Option (Credential (handleSource source)) × Nat) × Pool source :=
  ((some ⟨publicKey, before.keys.length⟩, 0),
    { before with keys := before.keys ++ [.challenge publicKey], bornAt := before.bornAt ++ [before.attempts], attempts := before.attempts + 1 })

noncomputable def capability (selected : Nat) (publicKey : PublicKey) :
    QueryImpl (RegistrationNativeMldsaCapability.Spec (handleSource source))
      (StateT (Pool source) (OracleComp RegistrationNativeMldsaEuf.Spec)) := by
  classical
  exact fun query => match query with
    | .generate => fun before => if before.attempts = selected then pure (challengeBirth source before publicKey)
        else birth source before <$> lift (RegistrationNativeMldsaCapability.actual source .generate)
    | .sign credential request => fun before =>
        match before.keys[credential.secret]? with
        | none => pure ((.None, 0), record source before credential request .None)
        | some (.ordinary key) => if credential.publicKey = key.publicKey then
            (fun result => (result, record source before credential request result.1)) <$>
              lift (RegistrationNativeMldsaCapability.actual source (.sign key request))
          else pure ((.None, 0), record source before credential request .None)
        | some (.challenge key) => if credential.publicKey = key ∧ request.public_key = key then
            (fun reply => ((reply, 0), record source before credential request reply)) <$>
              RegistrationNativeMldsaEuf.Spec.query (.inr request)
          else pure ((.None, 0), record source before credential request .None)

noncomputable def handler (selected : Nat) (publicKey : PublicKey) :
    QueryImpl (RegistrationNativeMldsaProgram.Spec (handleSource source))
      (StateT (Pool source) (OracleComp RegistrationNativeMldsaEuf.Spec))
  | .inl query => StateT.lift (coins query)
  | .inr query => capability source selected publicKey query

/-- The chosen attempt stores only the challenge public key and its actual successful-handle ordinal. -/
theorem challenge_birth (before : Pool source) (publicKey : PublicKey) :
    (challengeBirth source before publicKey).2.keys[before.keys.length]? = some (.challenge publicKey) ∧
      (challengeBirth source before publicKey).2.attempts = before.attempts + 1 :=
  ⟨List.getElem?_concat_length, rfl⟩

theorem generate_chosen (before : Pool source) (selected : Nat) (publicKey : PublicKey) (chosen : before.attempts = selected) :
    (capability source selected publicKey .generate).run before = pure (challengeBirth source before publicKey) := by
  simp only [capability, StateT.run, ite_eq_left chosen]
  rfl

theorem generate_ordinary (before : Pool source) (selected : Nat) (publicKey : PublicKey) (other : before.attempts ≠ selected) :
    (capability source selected publicKey .generate).run before =
      birth source before <$> lift (RegistrationNativeMldsaCapability.actual source .generate) := by
  simp only [capability, StateT.run, ite_eq_right other]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The selected owned request makes exactly the corresponding ordinary EUF signing query. -/
theorem sign_chosen (before : Pool source) (selected : Nat) (publicKey : PublicKey)
    (handle : Credential (handleSource source)) (request : registration.MldsaSigningRequest)
    (found : before.keys[handle.secret]? = some (.challenge publicKey))
    (owned : handle.publicKey = publicKey) (matching : request.public_key = publicKey) :
    (capability source selected publicKey (.sign handle request)).run before =
      (fun reply => ((reply, 0), record source before handle request reply)) <$>
        RegistrationNativeMldsaEuf.Spec.query (.inr request) := by
  simp only [capability, StateT.run, found, owned, matching, and_self, ite_true]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary row keeps its actual owned-source reply and exact source draw count. -/
theorem sign_ordinary (before : Pool source) (selected : Nat) (publicKey : PublicKey)
    (handle : Credential (handleSource source)) (request : registration.MldsaSigningRequest) (key : Credential source)
    (found : before.keys[handle.secret]? = some (.ordinary key)) (owned : handle.publicKey = key.publicKey) :
    (capability source selected publicKey (.sign handle request)).run before =
      (fun result => (result, record source before handle request result.1)) <$>
        lift (RegistrationNativeMldsaCapability.actual source (.sign key request)) := by
  simp only [capability, StateT.run, found, owned, ite_true]
  rfl

def IsUniform : RegistrationNativeMldsaEuf.Spec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

def IsSigning : RegistrationNativeMldsaEuf.Spec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

open Classical in
set_option backward.isDefEq.respectTransparency false in
/-- A selected owned sign has zero ordinary random draws and one external complete-request signing query, including a failed oracle reply. -/
theorem chosen_bill (before : Pool source) (selected : Nat) (publicKey : PublicKey)
    (handle : Credential (handleSource source)) (request : registration.MldsaSigningRequest)
    (found : before.keys[handle.secret]? = some (.challenge publicKey))
    (owned : handle.publicKey = publicKey) (matching : request.public_key = publicKey) :
    ((capability source selected publicKey (.sign handle request)).run before).IsQueryBoundP IsUniform 0 ∧
      ((capability source selected publicKey (.sign handle request)).run before).IsQueryBoundP IsSigning 1 := by
  rw [sign_chosen source before selected publicKey handle request found owned matching]
  constructor
  · change OracleComp.IsQueryBoundP ((fun reply => ((reply, (0 : Nat)), record source before handle request reply)) <$>
      (RegistrationNativeMldsaEuf.Spec.query (.inr request) : OracleComp RegistrationNativeMldsaEuf.Spec SignReply)) IsUniform 0
    simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsUniform]
    trivial
  · change OracleComp.IsQueryBoundP ((fun reply => ((reply, (0 : Nat)), record source before handle request reply)) <$>
      (RegistrationNativeMldsaEuf.Spec.query (.inr request) : OracleComp RegistrationNativeMldsaEuf.Spec SignReply)) IsSigning 1
    simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsSigning]
    trivial

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

end BeaconcryptCore.Computational.RegistrationNativeMldsaChosen

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.challenge_birth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.challenge_birth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.generate_chosen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.generate_chosen

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.generate_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.generate_ordinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.sign_chosen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.sign_chosen

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.sign_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.sign_ordinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.chosen_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.chosen_bill

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.birth_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.birth_aligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.birth_ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosen.birth_ordinal
