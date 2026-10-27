-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation

/-! Stop at an actual source encapsulation occurrence before its reply. The executable scanner forwards every other private service and evaluates every earlier public encapsulation locally, keeping the exact remaining source program. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut
open PqxdhServerAuthExperiment PqxdhRegistrationJointKemEncapsulation
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

abbrev Request := Pqxdh.Bytes × PqxdhKemIndCca.MlKem768PublicKey
abbrev Reply := Option (PqxdhBeaconPhase2Preparation.Ciphertext × PqxdhBeaconPhase2Preparation.Word32)

/-- The cut saves only the original public callback input and its literal continuation. It has no selected private-key field. -/
inductive Cut (KemSK Result : Type) where
  | complete (result : Result)
  | pending (request : Request) (next : Reply → OracleComp (Spec KemSK) Result)

/-- Count actual encapsulation attempts, including repeated public keys. Earlier optional failures and every private-service reply keep their source positions. -/
noncomputable def scan (setup : Setup baseSpec KemSK) (work : OracleComp (Spec KemSK) Result) :
    Nat → OracleComp (PqxdhLiveKemBirth.Spec KemSK) (Cut KemSK Result) :=
  OracleComp.recOn work
    (fun result _ => pure (.complete result))
    (fun query next recurse index => match query with
      | .inl request => do
        let answer ← (PqxdhLiveKemBirth.Spec KemSK).query request
        recurse answer index
      | .inr request => match index with
        | 0 => pure (.pending request next)
        | index + 1 => do
          let answer ← actual setup (.inr request)
          recurse answer index)

/-- Finish the saved source callback with its real encapsulator, or retain the original early completion. -/
noncomputable def finish (setup : Setup baseSpec KemSK) : Cut KemSK Result → OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result
  | .complete result => pure result
  | .pending request next => do
    let answer ← actual setup (.inr request)
    simulateQ (actual setup) (next answer)

/-- The selected actual encapsulation is retained before sampling its ciphertext or secret. -/
theorem scan_target (setup : Setup baseSpec KemSK) (request : Request)
    (next : Reply → OracleComp (Spec KemSK) Result) :
    scan setup ((Spec KemSK).query (.inr request) >>= next) 0 = pure (.pending request next) := rfl

/-- Every earlier encapsulation executes the same original source distribution and advances exactly one occurrence. -/
theorem scan_prior (setup : Setup baseSpec KemSK) (request : Request)
    (next : Reply → OracleComp (Spec KemSK) Result) (index : Nat) :
    scan setup ((Spec KemSK).query (.inr request) >>= next) (index + 1) =
      (actual setup (.inr request) >>= fun answer => scan setup (next answer) index) := rfl

/-- All other private and uniform requests keep their complete reply continuation and do not consume an encapsulation occurrence. -/
theorem scan_other (setup : Setup baseSpec KemSK) (request : (PqxdhLiveKemBirth.Spec KemSK).Domain)
    (next : (PqxdhLiveKemBirth.Spec KemSK).Range request → OracleComp (Spec KemSK) Result) (index : Nat) :
    scan setup ((Spec KemSK).query (.inl request) >>= next) index =
      (((PqxdhLiveKemBirth.Spec KemSK).query request : OracleComp (PqxdhLiveKemBirth.Spec KemSK) _) >>= fun answer => scan setup (next answer) index) := rfl

/-- Scanning and resuming the original callback restores the entire original oracle program, including completion before the requested occurrence. -/
theorem scan_finish (setup : Setup baseSpec KemSK) (work : OracleComp (Spec KemSK) Result) (index : Nat) :
    (scan setup work index >>= finish setup) = simulateQ (actual setup) work := by
  induction work using OracleComp.inductionOn generalizing index with
  | pure result => rfl
  | query_bind query next ih =>
    cases query with
    | inl request =>
      simp only [scan_other, bind_assoc, ih, simulateQ_bind, simulateQ_spec_query, actual]
      rfl
    | inr request =>
      cases index with
      | zero => rw [scan_target]; rfl
      | succ index => simp only [scan_prior, bind_assoc, ih, simulateQ_bind, simulateQ_spec_query]

/-- The selected occurrence cut and exact saved continuation belong to the original source14 command program, with the full native/owner output retained. -/
theorem commands_cut {Reader Response : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (identityIndex : Nat)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Result)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : PqxdhServerAuthNative.NativeState KemSK)
    (index : Nat) :
    (scan setup (commands setup codec checks identityIndex publicIdentity work owners state) index >>= finish setup) =
      PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex publicIdentity work owners state := by
  rw [scan_finish, commands_actual]

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut.scan_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut.scan_target

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut.scan_prior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut.scan_prior

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut.scan_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut.scan_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut.scan_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut.scan_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut.commands_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut.commands_cut
