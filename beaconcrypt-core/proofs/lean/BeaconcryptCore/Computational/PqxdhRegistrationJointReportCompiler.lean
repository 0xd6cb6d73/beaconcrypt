-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportCommands

/-! The actual initialized raw-accept reporter as an executable client of the existing ordinary generated joint-use endpoint and public Phase-1 field-report interface. The same local KEM/runtime execution and generated/imported index router are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointReportCompiler
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhServerAuthExperiment
open PqxdhRegistrationJointReportLift (Spec lift erase extend)
open PqxdhRegistrationJointIdentityCompiler (Local)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Result Reader Response : Type}

/-- Local actual KEM/runtime work and known imports remain inside the executable identity reduction. Only the existing generated joint-game interface receives private requests; original public field reports pass through unchanged. -/
def reduction (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)) Result)
    (localState : Local KemSK A) (registry : PqxdhRegistrationJointIdentityRouting.Registry) :
    OracleComp PqxdhJointPhase1Reports.ProtocolSpec
      ((Result × Local KemSK A) × PqxdhRegistrationJointIdentityRouting.Registry) :=
  (simulateQ (extend (PqxdhRegistrationJointIdentityRouting.route setup.joint))
    ((simulateQ (extend (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit)) program).run localState)).run registry

/-- Forgetting only public reports recovers the exact previously proved complete ordinary joint-identity source simulation. -/
theorem reduction_erase (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)) Result)
    (localState : Local KemSK A) (registry : PqxdhRegistrationJointIdentityRouting.Registry) :
    simulateQ erase (reduction setup ensureInit program localState registry) =
      PqxdhRegistrationJointIdentityCompiler.reduction setup ensureInit
        (simulateQ erase program) localState registry := by
  simp only [reduction, PqxdhRegistrationJointReportLift.extend_erase,
    PqxdhRegistrationJointIdentityCompiler.reduction]

/-- Actual initialized source commands, including successful raw-accept reports, start with empty local KEM and source-owner registries. Generated seeds never enter this client. -/
noncomputable def initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A) :=
  reduction setup ensureInit (PqxdhRegistrationJointReportCommands.initialized setup codec checks supplied count program)
    (PqxdhLiveKemBirth.empty, runtime) ⟨[], []⟩

/-- The entire reported initialized reduction erases to the earlier actual source reduction, preserving every ordinary request, complete private/local state and adaptive continuation. -/
theorem initialized_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A) :
    simulateQ erase (initialized setup codec checks ensureInit supplied count program runtime) =
      PqxdhRegistrationJointIdentityCompiler.initialized setup codec checks ensureInit supplied program runtime := by
  rw [initialized, reduction_erase, PqxdhRegistrationJointReportCommands.initialized_erase]
  rfl

end BeaconcryptCore.Computational.PqxdhRegistrationJointReportCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportCompiler.reduction_erase' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportCompiler.reduction_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportCompiler.initialized_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportCompiler.initialized_erase
