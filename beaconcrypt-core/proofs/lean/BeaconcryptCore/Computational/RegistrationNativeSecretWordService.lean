-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterface
import BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf

/-! The alias observer interprets symbolic root references using only public input heads and opaque KEM words. Protected inputs use the symbolic persistent108-byte table. Off-protected atoms use the additional ordinary suffix-key oracle; off-protected literals keep the actual public source schedule. The executing service never receives the candidate bytes. This is the alias observer service, not a replacement of the off-protected source branch in the main selective G3 experiment. Successful preparation echoes its exact descriptor, and material demand retains the descriptor flags. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordService
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativePairedChoice (Choice)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat}
attribute [local irreducible] RegistrationNativeSuffixKeyPrf.value

abbrev Flags := Message → Bool
abbrev Spec (n : Nat) := RegistrationNativeSecretWordMessage.PrepareSpec +
  (Message →ₒ Option (Choice n))
abbrev Combined := RegistrationNativeSecretWord.Spec + RegistrationNativeSuffixKeyPrf.Oracle

def coins : QueryImpl unifSpec (OracleComp Combined) :=
  fun coin => Combined.query (.inl (.inl coin))

def material (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (key : Key) :
    OracleComp Combined PqxdhServerAuthKeySchedule.Output :=
  if inside key.head then Combined.query (.inl (.inr key))
  else match key.word with
  | .atom => Combined.query (.inr key.head)
  | .literal secret => pure (RegistrationNativeSuffixKeyPrf.value source secret key.head)

def handler (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) :
    QueryImpl (Spec n) (StateT Flags (OracleComp Combined))
  | .inl message => fun before =>
      pure ((input message).map (fun _ => message),
        Function.update before message (input message).isSome)
  | .inr message => fun before =>
      if before message then match input message with
      | none => pure (none, before)
      | some key => (fun output => (some (Choice.known output), before)) <$>
          material source inside key
      else pure (none, before)

/-- Preparation returns its queried symbolic descriptor and records precisely whether the actual optional DH input exists. -/
theorem prepare_run (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (message : Message) (before : Flags) :
    (handler (n := n) source input inside (.inl message)).run before =
      pure ((input message).map (fun _ => message),
        Function.update before message (input message).isSome) := rfl

/-- Every successful preparation stores a live receipt for that same descriptor; no inverse for an arbitrary returned name is used. -/
theorem prepare_some (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (message : Message) (key : Key)
    (realized : input message = some key) (before : Flags) :
    (handler (n := n) source input inside (.inl message)).run before =
      pure (some message, Function.update before message true) := by
  simp only [prepare_run, realized, Option.map_some, Option.isSome_some]

/-- Unprepared descriptors cannot access either the symbolic key table or the added suffix-key oracle. -/
theorem demand_missing (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (message : Message) (before : Flags)
    (missing : before message = false) :
    (handler (n := n) source input inside (.inr message)).run before = pure (none, before) := by
  simp only [handler, StateT.run, missing, Bool.false_eq_true, ite_false]

/-- A prepared valid descriptor asks its actual material branch while retaining the entire descriptor-flag map. -/
theorem demand_ready (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (message : Message) (key : Key)
    (before : Flags) (prepared : before message = true) (realized : input message = some key) :
    (handler (n := n) source input inside (.inr message)).run before =
      (fun output => (some (Choice.known output), before)) <$> material source inside key := by
  simp only [handler, StateT.run, prepared, ite_true, realized]

/-- Protected queries retain the complete symbolic input, including the opaque atom or its public literal. -/
theorem material_protected (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (key : Key)
    (protectedInput : inside key.head = true) :
    material source inside key = Combined.query (.inl (.inr key)) := by
  simp only [material, protectedInput, ite_true]

/-- An off-protected atom is handled by the explicit additional ordinary primitive, without revealing or testing its key. -/
theorem material_atom (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (head : RegistrationNativeSuffixKeyPrf.Prefix)
    (outside : inside head = false) :
    material source inside ⟨head, .atom⟩ = Combined.query (.inr head) := by
  simp only [material, outside, Bool.false_eq_true, ite_false]

/-- An off-protected literal keeps the complete actual public source schedule under that literal key. -/
theorem material_literal (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (head : RegistrationNativeSuffixKeyPrf.Prefix)
    (secret : RegistrationNativeSuffixKeyPrf.Secret) (outside : inside head = false) :
    material source inside ⟨head, .literal secret⟩ =
      pure (RegistrationNativeSuffixKeyPrf.value source secret head) := by
  simp only [material, outside, Bool.false_eq_true, ite_false]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordService
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordService.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordService.prepare_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordService.prepare_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordService.prepare_some
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordService.demand_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordService.demand_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordService.demand_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordService.demand_ready
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordService.material_protected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordService.material_protected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordService.material_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordService.material_atom
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordService.material_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordService.material_literal
