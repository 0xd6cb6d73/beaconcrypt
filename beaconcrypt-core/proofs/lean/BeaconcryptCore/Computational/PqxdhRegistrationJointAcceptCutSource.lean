-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCut

/-! Apply the raw-attempt cut to the actual complete command compiler. Private source state remains in the same outer oracle execution across suspension and resumption. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutSource
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointKemEncapsulation (commands)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Next : Type}

/-- The exposed source compiler retains both complete owner and native states across the original arbitrary continuation. -/
theorem commands_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (Spec KemSK) Result) (next : Result → OracleComp (Spec KemSK) Next)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK) :
    commands setup codec checks identityIndex publicIdentity (work >>= next) owners state =
      (commands setup codec checks identityIndex publicIdentity work owners state >>= fun result =>
        commands setup codec checks identityIndex publicIdentity (next result.1.1) result.1.2 result.2) := by
  simp only [commands, simulateQ_bind, StateT.run_bind]

/-- The actual source execution splits at the chosen raw attempt with every private-service query, owner, cache and native continuation in its original position. -/
theorem commands_resume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (Spec KemSK) Result) (index : Nat)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK) :
    (commands setup codec checks identityIndex publicIdentity (PqxdhRegistrationJointAcceptCut.scan work index) owners state >>= fun result =>
      commands setup codec checks identityIndex publicIdentity
        (PqxdhRegistrationJointAcceptCut.finish result.1.1) result.1.2 result.2) =
    commands setup codec checks identityIndex publicIdentity work owners state := by
  rw [← commands_bind, PqxdhRegistrationJointAcceptCut.scan_finish]

/-- At a pending raw attempt, the next primitive computation is the original complete accept, followed by its actual optional reply continuation. Acceptance leaves the owner registry untouched. -/
theorem pending_command (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp (Spec KemSK) Result)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK) :
    commands setup codec checks identityIndex publicIdentity
      (PqxdhRegistrationJointAcceptCut.finish (.pending raw next)) owners state =
      ((PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw).run state >>= fun result =>
        commands setup codec checks identityIndex publicIdentity (next result.1) owners result.2) := by
  simp only [PqxdhRegistrationJointAcceptCut.finish, commands, StateT.run_bind,
    simulateQ_bind, simulateQ_spec_query, PqxdhRegistrationJointRevealSchedule.client,
    PqxdhRegistrationJointServiceSchedule.handler, StateT.run_lift, bind_assoc, pure_bind,
    PqxdhRegistrationJointKemEncapsulation.impl]
  rfl

end BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutSource

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutSource.commands_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutSource.commands_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutSource.commands_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutSource.commands_resume

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutSource.pending_command' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutSource.pending_command
