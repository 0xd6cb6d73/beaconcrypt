-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized

/-! The actual complete deployment execution with its existing private constructor and all-attempt signing ledger. Every failed Fresh writer remains in this source run. Forgetting the ledger and merging the compiled record kernels preserves the exact complete CE outcome and runtime, in either observation mode. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityExecution
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

abbrev Result (X : Type) := (X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local
abbrev Outcome (KemSK A X : Type) := Option (PqxdhRegistrationJointAttemptInitialized.Outcome KemSK (Result X)) ×
  PqxdhRegistrationJointServerPrefix.State KemSK A

/-- The real initialized scheduler, with an additional private ledger of constructor fields and every complete signing attempt. -/
noncomputable def actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    ProbComp (Outcome KemSK A X) :=
  (PqxdhRegistrationJointAttemptInitialized.run setup codec checks ensureInit none
    (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)

/-- Forget the private service and attempt ledgers, retaining the complete actual merged deployment state and runtime. -/
def deployment (outcome : Outcome KemSK A X) : PqxdhDeploymentPublicationSecurityEvents.Outcome KemSK A X :=
  PqxdhDeploymentCompileSecrecy.mergeFull
    (outcome.1.map (PqxdhRegistrationJointInitializedSchedule.eraseOutcome ∘
      PqxdhRegistrationJointAttemptInitialized.erase), outcome.2.2)

/-- Exact complete-run erasure, including initialization rejection, generated Server data, the full secrecy ledger, merged live kernels, both caches, every owner and the final runtime. Only the original CE-COMPILE codec contracts are used. -/
theorem actual_deployment (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    deployment <$> actual setup codec checks route ensureInit bounds mode adversary runtime =
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime := by
  have erased := congrArg (Functor.map (fun result => PqxdhDeploymentCompileSecrecy.mergeFull
      (result.1.map PqxdhRegistrationJointInitializedSchedule.eraseOutcome, result.2.2)))
    (PqxdhRegistrationJointAttemptInitialized.source setup codec checks ensureInit none
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))
  have compiled := PqxdhDeploymentCompileSecrecy.compile_full_source setup codec checks route ensureInit phase1 phase2
    bounds mode adversary ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  change (fun outcome : Outcome KemSK A X => PqxdhDeploymentCompileSecrecy.mergeFull
    (outcome.1.map (PqxdhRegistrationJointInitializedSchedule.eraseOutcome ∘
      PqxdhRegistrationJointAttemptInitialized.erase), outcome.2.2)) <$> _ = _
  simpa only [actual, Functor.map_map, Option.map_map, PqxdhDynamicIdentityPool.initialState, List.length_nil] using
    erased.trans compiled

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityExecution

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityExecution.actual_deployment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityExecution.actual_deployment
