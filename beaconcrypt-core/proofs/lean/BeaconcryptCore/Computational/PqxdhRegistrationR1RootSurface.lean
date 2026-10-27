-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal

/-! Full raw singleton construction and both initialization calls retain the private same-run authentication outcome, including every refusal branch and the final runtime. -/

open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationR1RootAudit
variable {ι KemSK Reader Response Result A : Type} {baseSpec : OracleSpec ι}

/-- The genuine rejected tail remains present; only an allocated Beacon has the private source-occurrence outcome. -/
inductive PrefixOutcome (KemSK Result : Type) where
  | rejected (result : Result × PqxdhRegistrationSchedule.State KemSK)
  | created (audit : RootAudit KemSK Result)

/-- Forget the additional callback receipts while retaining the previous complete source audit. -/
def toPrefix : PrefixOutcome KemSK Result → PqxdhRegistrationR1Surface.PrefixOutcome KemSK Result
  | .rejected result => .rejected result
  | .created audit => .created (toAudit audit)

/-- The actual second initialization call determines whether the concrete owner is created. On refusal the original missing-owner tail runs and no Beacon material is drawn. -/
noncomputable def rootPrefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (origin : PqxdhLiveServerConstruction.Origin)
    (ensureInit : StateT A ProbComp Bool) (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result)
    (runtime : A) : ProbComp (PrefixOutcome KemSK Result × A) := do
  let initialized ← ensureInit.run runtime
  let continuation := fun created published =>
    work created ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩
  if initialized.1 then
    (fun audit => (PrefixOutcome.created audit, initialized.2)) <$>
      rootAudited setup codec checks serverSeed (continuation (some 0))
  else
    (fun result => (PrefixOutcome.rejected result, initialized.2)) <$>
      PqxdhRegistrationR1Surface.tail setup codec checks serverSeed (continuation none)
        (PqxdhRegistrationSchedule.initial
          (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed))

/-- The complete original prefix audit is the exact projection of this same execution, for every initialization outcome and result-dependent continuation. -/
theorem prefix_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (origin : PqxdhLiveServerConstruction.Origin)
    (ensureInit : StateT A ProbComp Bool) (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result)
    (runtime : A) :
    Prod.map toPrefix id <$> rootPrefix setup codec checks serverSeed origin ensureInit work runtime =
      PqxdhRegistrationR1Journal.prefixAuditWith setup codec checks serverSeed origin ensureInit work runtime := by
  simp only [rootPrefix, PqxdhRegistrationR1Journal.prefixAuditWith, map_bind]
  refine bind_congr fun initialized => ?_
  split <;> simp only [Functor.map_map, Prod.map, id_eq, toPrefix]
  rw [← audited_root setup codec checks serverSeed]
  simp only [Functor.map_map]

/-- Both source initialization calls and the complete generated or supplied Server constructor precede the same-run root audit. Only the final runtime is returned. -/
noncomputable def rootExperiment (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result) (runtime : A) :
    ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × PrefixOutcome KemSK Result) × A) := do
  let started ← (PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit 0 setup.serverKeyId supplied).run runtime
  match started.1 with
  | none => pure (none, started.2)
  | some created =>
      (fun result => (some (created, result.1), result.2)) <$>
        rootPrefix setup codec checks created.seed created.origin ensureInit work started.2

/-- Project only the added occurrence receipts, retaining the constructor and final runtime. -/
def toExperiment (result : Option (PqxdhLiveServerConstruction.Created Unit × PrefixOutcome KemSK Result) × A) :
    Option (PqxdhLiveServerConstruction.Created Unit × PqxdhRegistrationR1Surface.PrefixOutcome KemSK Result) × A :=
  (result.1.map (Prod.map id toPrefix), result.2)

/-- The unconditioned source audit factors through the same occurrence execution, for both generated and supplied Server seeds and every refusal outcome. -/
theorem experiment_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result) (runtime : A) :
    toExperiment <$> rootExperiment setup codec checks ensureInit supplied work runtime =
      PqxdhRegistrationR1Journal.auditedExperimentWith setup codec checks ensureInit supplied work runtime := by
  simp only [rootExperiment, PqxdhRegistrationR1Journal.auditedExperimentWith, map_bind]
  refine bind_congr fun started => ?_
  cases started.1 <;> simp only [map_pure, Functor.map_map, toExperiment, Option.map_none, Option.map_some]
  rw [← prefix_audit]
  simp only [Functor.map_map, Prod.map, id_eq]

/-- The actual raw singleton API execution is the operational projection of this same root-audited run, including both initialization refusals and the supplied-seed branch. -/
theorem surface_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result) (runtime : A) :
    PqxdhRegistrationR1Surface.eraseExperiment <$>
      PqxdhRegistrationSchedule.surfaceExperiment setup codec checks ensureInit supplied
        (fun identity sender => PqxdhRegistrationR1Journal.programWith identity sender work) runtime =
      (PqxdhRegistrationR1Surface.observeExperiment ∘ toExperiment) <$>
        rootExperiment setup codec checks ensureInit supplied work runtime := by
  rw [PqxdhRegistrationR1Journal.experimentWith_audit, ← experiment_audit, Functor.map_map]
  rfl

/-- Logging every actual surface request gives the same complete source run with its common-event occurrence outcome still attached privately. No journal or accepted record is supplied as a premise. -/
theorem surface_journal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (runtime : A) :
    PqxdhRegistrationR1Surface.eraseExperiment <$>
      PqxdhRegistrationSchedule.surfaceExperiment setup codec checks ensureInit supplied
        (fun identity sender => PqxdhRegistrationCells.journal
          (PqxdhRegistrationR1Surface.program identity sender work)) runtime =
      (PqxdhRegistrationR1Surface.observeExperiment ∘ toExperiment) <$>
        rootExperiment setup codec checks ensureInit supplied
          (PqxdhRegistrationR1Journal.journalWork work) runtime := by
  simp_rw [PqxdhRegistrationR1Journal.program_journal]
  exact surface_audit setup codec checks ensureInit supplied (PqxdhRegistrationR1Journal.journalWork work) runtime

end BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface.prefix_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface.prefix_audit
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface.experiment_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface.experiment_audit
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface.surface_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface.surface_audit
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface.surface_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface.surface_journal
