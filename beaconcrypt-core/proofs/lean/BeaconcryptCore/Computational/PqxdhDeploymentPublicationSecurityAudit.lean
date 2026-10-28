-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityExecution
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace

/-! The global bundle-occurrence audit starts at the actual Server constructor and executes the full adaptive source program. Its erasure preserves every native and private service field, including Server converted-DH observations. The compiled full-run projection is exactly the common deployment experiment. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit
open PqxdhServerAuthExperiment
open PqxdhRegistrationJointServerBirth (ClientCreated encode)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentPublicationSuppressionTrace (Audit handler)
variable {ι KemSK Reader Response A Result X : Type} {baseSpec : OracleSpec ι}

abbrev SourceOutcome (KemSK Result : Type) := ClientCreated Unit × Result ×
  PqxdhDeploymentPublicationSuppressionTrace.State KemSK

def erase (outcome : SourceOutcome KemSK Result) :
    PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result :=
  (outcome.1, outcome.2.1, outcome.2.2.1)

/-- The original constructor and original all-reply source scheduler, with only a private chronological bundle-call audit added. -/
noncomputable def initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    StateT (PqxdhRegistrationJointServerPrefix.State KemSK A) ProbComp (Option (SourceOutcome KemSK Result)) := fun state => do
  let born ← (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
      (fun result => (some (encode created, result.1, result.2), (result.2.1.pool, born.2.2))) <$>
        (simulateQ (handler setup codec checks created.seed created.server.server.metadata.identityIndex) program).run
          (PqxdhRegistrationJointSchedule.initial born.2.1 (PqxdhRegistrationSchedule.initial created).shared, Audit.empty)

/-- Erasing the global audit preserves the exact complete original initialized source program and every private/native/runtime field. -/
theorem source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => (result.1.map erase, result.2)) <$>
      (initialized setup codec checks ensureInit supplied program).run state =
      (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied program).run state := by
  simp only [initialized, PqxdhRegistrationJointInitializedSchedule.source, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨(_ | created), after⟩
  · rfl
  · simpa only [StateT.run, Functor.map_map, erase, Option.map_some] using congrArg
      (fun execution => (fun result : Result × PqxdhRegistrationJointSchedule.State KemSK =>
        (some (encode created, result.1, result.2), (result.2.pool, after.2))) <$> execution)
      (PqxdhDeploymentPublicationSuppressionTrace.program_source setup codec checks created.seed
        created.server.server.metadata.identityIndex program
        (PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared, Audit.empty))

/-- Every actual source outcome has a same-execution global occurrence audit, with the entire reached source and runtime state fixed. -/
theorem source_witness (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (runtime : A) (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result)
    (supported : (some outcome, after) ∈ support
      ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))) :
    ∃ audit, (some (outcome.1, outcome.2.1, (outcome.2.2, audit)), after) ∈ support
      ((initialized setup codec checks ensureInit supplied program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) := by
  rw [← source, support_map] at supported
  obtain ⟨⟨(_ | annotated), final⟩, visited, equal⟩ := supported
  · simp only [Option.map_none, Prod.mk.injEq, reduceCtorEq, false_and] at equal
  · have same : erase annotated = outcome := Option.some.inj (congrArg Prod.fst equal)
    have runtimeSame : final = after := congrArg Prod.snd equal
    cases same
    subst after
    exact ⟨annotated.2.2.2, visited⟩

abbrev Outcome (KemSK A X : Type) := Option (SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X)) ×
  PqxdhRegistrationJointServerPrefix.State KemSK A

noncomputable def actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    ProbComp (Outcome KemSK A X) :=
  (initialized setup codec checks ensureInit none
    (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)

def deployment (outcome : Outcome KemSK A X) : PqxdhDeploymentPublicationSecurityEvents.Outcome KemSK A X :=
  PqxdhDeploymentCompileSecrecy.mergeFull
    (outcome.1.map (PqxdhRegistrationJointInitializedSchedule.eraseOutcome ∘ erase), outcome.2.2)

/-- The complete real global-audit experiment projects exactly to CE in both modes, including rejected initialization and the complete merged final state. -/
theorem actual_deployment (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    deployment <$> actual setup codec checks route ensureInit bounds mode adversary runtime =
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime := by
  have erased := congrArg (Functor.map (fun result => PqxdhDeploymentCompileSecrecy.mergeFull
      (result.1.map PqxdhRegistrationJointInitializedSchedule.eraseOutcome, result.2.2)))
    (source setup codec checks ensureInit none
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))
  have compiled := PqxdhDeploymentCompileSecrecy.compile_full_source setup codec checks route ensureInit phase1 phase2
    bounds mode adversary ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  change (fun outcome : Outcome KemSK A X => PqxdhDeploymentCompileSecrecy.mergeFull
    (outcome.1.map (PqxdhRegistrationJointInitializedSchedule.eraseOutcome ∘ erase), outcome.2.2)) <$> _ = _
  simpa only [actual, Functor.map_map, Option.map_map, PqxdhDynamicIdentityPool.initialState, List.length_nil] using
    erased.trans compiled

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.source_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.source_witness

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_deployment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_deployment
