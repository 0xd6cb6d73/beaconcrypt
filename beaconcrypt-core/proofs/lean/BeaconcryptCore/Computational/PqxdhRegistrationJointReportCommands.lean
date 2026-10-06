-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointRawReports

/-! Compile the actual adaptive registration commands and their public candidate reports into the same open constructor/private-service program. The complete owner/native state survives erasure; private pools remain in the external interpreters. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointReportLift (Spec lift erase extend)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Next : Type}
abbrev State (KemSK : Type) := List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × NativeState KemSK
abbrev Birth (KemSK : Type) := PqxdhRegistrationJointServerBirth.Spec KemSK

/-- The existing full source command compiler, with its owner/native pair reassociated and all service requests forwarded through the real constructor interface. -/
noncomputable def commands (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    StateT (State KemSK) (OracleComp (Birth KemSK)) Result := fun state =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    simulateQ PqxdhRegistrationJointOpenInitialization.poolLift
      ((PqxdhRegistrationJointOpenBackend.compile setup codec checks identityIndex publicIdentity
        (simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec) program) state.1).run state.2)

/-- Compilation retains the complete owner/native state under the whole continuation, not just an individual callback result. -/
theorem commands_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (next : Result → OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Next) (state : State KemSK) :
    commands setup codec checks identityIndex publicIdentity (program >>= next) state =
      (commands setup codec checks identityIndex publicIdentity program state >>= fun result =>
        commands setup codec checks identityIndex publicIdentity (next result.1) result.2) := by
  simp only [commands, simulateQ_bind, PqxdhRegistrationJointOpenBackend.compile,
    StateT.run_bind, map_bind, bind_map_left]

/-- The literal per-command compiler reconstructs exactly the existing whole initialized command compiler. -/
theorem commands_simulate (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK) :
    (simulateQ (fun query => commands setup codec checks identityIndex publicIdentity
      ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query query)) program).run state =
        commands setup codec checks identityIndex publicIdentity program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, commands_bind, ih]
      rfl

/-- The executable reported program compiles each literal source command; public reports occur only after its exact reply and keep both source state coordinates unchanged. -/
noncomputable def reported (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    StateT (State KemSK) (OracleComp (Spec (Birth KemSK))) Result :=
  simulateQ (extend (fun query => commands setup codec checks identityIndex publicIdentity
    ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query query)))
      (simulateQ (PqxdhRegistrationJointRawReports.instrument codec count) program)

/-- Erasing public reports from the actual compiled adaptive command execution restores the complete original owner/native result, including all private-service requests in the same order. -/
theorem reported_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK) :
    simulateQ erase ((reported setup codec checks identityIndex publicIdentity count program).run state) =
      commands setup codec checks identityIndex publicIdentity program state := by
  rw [reported, PqxdhRegistrationJointReportLift.extend_erase,
    PqxdhRegistrationJointRawReports.instrument_erase, commands_simulate]

/-- Actual Server initialization followed by the complete reported source commands. Generated/imported origin and every rejected constructor branch are retained. -/
noncomputable def initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    OracleComp (Spec (Birth KemSK)) (Option (PqxdhRegistrationJointOpenInitialization.Outcome KemSK Result)) := do
  let born ← lift (PqxdhRegistrationJointServerBirth.client (P := Unit) setup.serverKeyId supplied)
  match born with
  | none => pure none
  | some created =>
    (fun result => some (created, result.1, result.2.2, result.2.1)) <$>
      (reported setup codec checks created.server.server.metadata.identityIndex created.publicIdentity count program).run
        ([], PqxdhRegistrationJointInitializedAccept.initial created)

/-- Public successful-accept reports preserve the exact existing initialized source client tree, including its full private/native/runtime continuation after interpretation. -/
theorem initialized_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    simulateQ erase (initialized setup codec checks supplied count program) =
      PqxdhRegistrationJointOpenInitialization.client setup codec checks supplied program := by
  simp only [initialized, simulateQ_bind, PqxdhRegistrationJointReportLift.erase_lift,
    PqxdhRegistrationJointOpenInitialization.client]
  apply bind_congr
  rintro (_ | created)
  · rfl
  · simp only [simulateQ_map, reported_erase, commands, Functor.map_map]

end BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands.commands_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands.commands_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands.commands_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands.commands_simulate

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands.reported_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands.reported_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands.initialized_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands.initialized_erase
