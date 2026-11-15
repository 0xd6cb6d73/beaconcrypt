-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot
import BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling

/-!
The complete source execution continues after acceptance. Its private first-stop snapshot has the same native state and public source journal as the existing CE-A1 reduction's root-labelled audit. The relation forgets only the existing analysis histories at this projection; the real execution's result and final native state are preserved by the independent exact erasure theorem.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionExecution

open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentServerAuthEmbed (SourceSpec dflt stopAt)
open PqxdhDeploymentServerAuthLocal (base Bad)
open PqxdhDeploymentSessionCoupling (initial audited auditedView ReducedResult)
open PqxdhRegistrationR1Restriction (eraseShared)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result X : Type}

def prefixView (outcome : Result × PqxdhDeploymentSessionSnapshot.State (SourceSpec KemSK)
    (PqxdhRegistrationSchedule.State KemSK)) :
    PqxdhDeploymentSessionSnapshot.Journal (SourceSpec KemSK) × PqxdhRegistrationSchedule.State KemSK :=
  let snapshot := PqxdhDeploymentSessionSnapshot.view outcome.2
  (snapshot.1, eraseShared snapshot.2)

noncomputable def auditPrefixView (setup : Setup baseSpec KemSK)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK (ReducedResult KemSK Result)) :
    PqxdhDeploymentSessionSnapshot.Journal (SourceSpec KemSK) × PqxdhRegistrationSchedule.State KemSK :=
  ((auditedView setup audit).1.2, (auditedView setup audit).2)

/-- A real complete run and its source root audit have the same full acceptance-prefix view. -/
theorem source_snapshot_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result)
    (unread : program.IsQueryBoundP (Bad (KemSK := KemSK)) 0) :
    EvalDistEq (prefixView <$>
      PqxdhDeploymentSessionSnapshot.run (base setup codec checks seed) (stopAt c) program (initial setup seed))
      (auditPrefixView setup <$> audited setup codec checks seed c program) := by
  have snapshot := (PqxdhDeploymentSessionSnapshot.view_frozen (base setup codec checks seed)
    dflt (stopAt c) program (initial setup seed) (PqxdhDeploymentServerAuthFreeze.stopAt_nil c)).map
      (fun value => (value.1, eraseShared value.2))
  have root := (PqxdhDeploymentSessionCoupling.frozen_root_state setup codec checks seed c program unread).map
    (fun result => (result.1.2, result.2))
  simp only [Functor.map_map] at snapshot root
  exact snapshot.trans root

/-- Both observation modes have the actual acceptance-prefix distribution of the root audit. -/
theorem compiled_snapshot_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (c : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    EvalDistEq (prefixView <$>
      PqxdhDeploymentSessionSnapshot.run (base setup codec checks seed) (stopAt c)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) (initial setup seed))
      (auditPrefixView setup <$> audited setup codec checks seed c
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)) :=
  source_snapshot_root setup codec checks seed c _
    (PqxdhDeploymentServerAuthChain.compiled_unread setup codec route bounds mode adversary)

/-- The complete compiled run retains its exact output, secrecy ledger and final native state. -/
theorem compiled_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (c : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    (fun result => (result.1, result.2.native)) <$>
      PqxdhDeploymentSessionSnapshot.run (base setup codec checks seed) (stopAt c)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) (initial setup seed) =
      (simulateQ (base setup codec checks seed)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run (initial setup seed) :=
  PqxdhDeploymentSessionSnapshot.erase _ _ _ _

end BeaconcryptCore.Computational.PqxdhDeploymentSessionExecution

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionExecution.source_snapshot_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionExecution.source_snapshot_root

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionExecution.compiled_snapshot_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionExecution.compiled_snapshot_root

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionExecution.compiled_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionExecution.compiled_erase
