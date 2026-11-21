-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag

/-! Split the initialized report run of the actual source14 program at the selected raw accept, and relate the report run of the selected prefix to the report run of the raw-accept scan. The split keeps every report, local, registry and source coordinate at the cut and resumes the literal continuation from them. The result-map lemmas change only the program-result component of a report outcome. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports
open PqxdhServerAuthExperiment
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointAcceptCut (Cut scan choice selected)
open PqxdhRegistrationJointAcceptCutTag (Tag tagFinish tag)
open PqxdhRegistrationJointInitializedReports (ReportResult sourceResult)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response X Y : Type}

/-- Resume the reported command compiler from a recorded initialized outcome: the same Server, owner registry and native state, and the literal continuation `next` applied to the recorded program result. A failed constructor stays failed. -/
noncomputable def resume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (count : Nat) (next : X → OracleComp (Spec KemSK) Y) :
    Option (PqxdhRegistrationJointOpenInitialization.Outcome KemSK X) →
      OracleComp (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointServerBirth.Spec KemSK))
        (Option (PqxdhRegistrationJointOpenInitialization.Outcome KemSK Y))
  | none => pure none
  | some outcome => (fun result => some (outcome.1, result.1, result.2.2, result.2.1)) <$>
      (PqxdhRegistrationJointReportCommands.reported setup codec checks
        outcome.1.server.server.metadata.identityIndex outcome.1.publicIdentity count (next outcome.2.1)).run
          (outcome.2.2.2, outcome.2.2.1)

/-- Continue a reached report outcome: the resumed commands run under the same identity reduction from the reached local KEM/runtime state and source registry, and under the same report interpreter from the reached monitor and reporting state. -/
noncomputable def continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (count : Nat) (next : X → OracleComp (Spec KemSK) Y)
    (reached : ReportResult KemSK A X count) : ProbComp (ReportResult KemSK A Y count) :=
  (simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
    (PqxdhRegistrationJointReportCompiler.reduction setup ensureInit
      (resume setup codec checks count next reached.1.1.1) reached.1.1.2 reached.1.2)).run reached.2

/-- The initialized reported commands of a bind are the commands of the prefix followed by their resumption. -/
theorem commands_initialized_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (Spec KemSK) X) (next : X → OracleComp (Spec KemSK) Y) :
    PqxdhRegistrationJointReportCommands.initialized setup codec checks supplied count (program >>= next) =
      (PqxdhRegistrationJointReportCommands.initialized setup codec checks supplied count program >>=
        resume setup codec checks count next) := by
  simp only [PqxdhRegistrationJointReportCommands.initialized, PqxdhRegistrationJointReportCommands.reported,
    simulateQ_bind, StateT.run_bind, bind_assoc]
  apply bind_congr
  rintro (_ | created)
  · rfl
  · simp only [bind_map_left, resume, map_bind, PqxdhRegistrationJointReportCommands.reported, Prod.mk.eta]

/-- The initialized report compiler of a bind is the compiler of the prefix followed by the identity reduction of the resumed commands from the reached local state and registry. -/
theorem initialized_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (Spec KemSK) X) (next : X → OracleComp (Spec KemSK) Y) (runtime : A) :
    PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
        (program >>= next) runtime =
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime >>=
        fun reached => PqxdhRegistrationJointReportCompiler.reduction setup ensureInit
          (resume setup codec checks count next reached.1.1) reached.1.2 reached.2) := by
  simp only [PqxdhRegistrationJointReportCompiler.initialized, commands_initialized_bind,
    PqxdhRegistrationJointTerminalReports.compiler_bind]

/-- The report run of a bind is the report run of the prefix followed by `continuation` from the complete reached outcome. -/
theorem run_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (Spec KemSK) X) (next : X → OracleComp (Spec KemSK) Y) (runtime : A) :
    PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
        (program >>= next) runtime) =
      (PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime) >>=
        continuation setup codec checks ensureInit count next) := by
  rw [initialized_bind]
  simp only [PqxdhJointPhase1Reports.run, simulateQ_bind, StateT.run_bind]
  rfl

/-- The report run of the original program is the report run of the raw-accept scan followed by the literal resumption of the original continuation from the reached state. -/
theorem cut_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A) :
    PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count work runtime) =
      (PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
          (scan work index) runtime) >>=
        continuation setup codec checks ensureInit count PqxdhRegistrationJointAcceptCut.finish) := by
  conv_lhs => rw [← PqxdhRegistrationJointAcceptCut.scan_finish work index]
  exact run_bind setup codec checks ensureInit supplied count _ _ runtime

/-- The coupling of the report run at the cut with the report run of the tagged program: both components come from one execution, the first is the reached outcome at the raw cut and the second is the final outcome after the recording finish and the original continuation. -/
noncomputable def split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A) :
    ProbComp (ReportResult KemSK A (Cut KemSK X) count × ReportResult KemSK A (X × Tag) count) := do
  let reached ← PqxdhJointPhase1Reports.run setup.joint count
    (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
      (scan work index) runtime)
  let final ← continuation setup codec checks ensureInit count tagFinish reached
  pure (reached, final)

/-- The final component of the coupling is exactly the report run of the tagged program. -/
theorem split_snd (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A) :
    Prod.snd <$> split setup codec checks ensureInit supplied count work index runtime =
      PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
          (tag work index) runtime) := by
  rw [PqxdhRegistrationJointAcceptCutTag.tag_split, run_bind]
  simp only [split, map_bind, map_pure, bind_pure]

/-- Every countable observation of the cut component has exactly its distribution under the report run of the raw-accept scan. The continuation is an ordinary probabilistic computation and cannot fail, so it does not change the marginal. Taking a Boolean observation gives the probability of any cut-time event. -/
theorem split_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A) {Observation : Type} [MeasurableSpace Observation]
    [MeasurableSingletonClass Observation] [Countable Observation]
    (observe : ReportResult KemSK A (Cut KemSK X) count → Observation) :
    𝒟[(fun pair => observe pair.1) <$> split setup codec checks ensureInit supplied count work index runtime] =
      𝒟[observe <$> PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
          (scan work index) runtime)] := by
  have shape : (fun pair => observe pair.1) <$> split setup codec checks ensureInit supplied count work index runtime =
      (PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
          (scan work index) runtime) >>= fun reached =>
        continuation setup codec checks ensureInit count tagFinish reached >>= fun _ => pure (observe reached)) := by
    simp only [split, map_bind, map_pure]
  rw [shape]
  refine EvalDistEq.evalDist_eq ?_
  rw [map_eq_bind_pure_comp]
  exact EvalDistEq.bind_right _ fun reached => OracleComp.EvalDistEq.bind_const _ _

/-- The initialized reported commands are natural in the program result. -/
theorem commands_initialized_map (f : X → Y) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (supplied : Option Pqxdh.Bytes) (count : Nat) (program : OracleComp (Spec KemSK) X) :
    PqxdhRegistrationJointReportCommands.initialized setup codec checks supplied count (f <$> program) =
      Option.map (fun outcome => (outcome.1, f outcome.2.1, outcome.2.2)) <$>
        PqxdhRegistrationJointReportCommands.initialized setup codec checks supplied count program := by
  simp only [PqxdhRegistrationJointReportCommands.initialized, PqxdhRegistrationJointReportCommands.reported,
    simulateQ_map, StateT.run_map, map_bind]
  apply bind_congr
  rintro (_ | created)
  · rfl
  · simp only [Functor.map_map, Option.map_some]

/-- The identity reduction is natural in the program result. -/
theorem reduction_map {P Q : Type} (h : P → Q) (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)) P)
    (localState : PqxdhRegistrationJointIdentityCompiler.Local KemSK A)
    (registry : PqxdhRegistrationJointIdentityRouting.Registry) :
    PqxdhRegistrationJointReportCompiler.reduction setup ensureInit (h <$> program) localState registry =
      (fun result => ((h result.1.1, result.1.2), result.2)) <$>
        PqxdhRegistrationJointReportCompiler.reduction setup ensureInit program localState registry := by
  simp only [PqxdhRegistrationJointReportCompiler.reduction, simulateQ_map, StateT.run_map]

/-- The initialized report compiler is natural in the program result; the map touches only the program-result component of the outcome. -/
theorem initialized_map (f : X → Y) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (Spec KemSK) X) (runtime : A) :
    PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count (f <$> program) runtime =
      (fun result => ((result.1.1.map (fun outcome => (outcome.1, f outcome.2.1, outcome.2.2)), result.1.2), result.2)) <$>
        PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime := by
  simp only [PqxdhRegistrationJointReportCompiler.initialized, commands_initialized_map, reduction_map]

/-- The report game is natural in the client result and leaves the report state unchanged. -/
theorem run_map {P Q : Type} (g : P → Q) (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (client : OracleComp PqxdhJointPhase1Reports.ProtocolSpec P) :
    PqxdhJointPhase1Reports.run joint count (g <$> client) =
      (fun result => (g result.1, result.2)) <$> PqxdhJointPhase1Reports.run joint count client := by
  simp only [PqxdhJointPhase1Reports.run, simulateQ_map, StateT.run_map]

/-- Replace the program result of a report outcome at the raw cut by the final choice of `AcceptCut.selected`. Every other coordinate, including local state, registry, monitor, snapshot and reporting state, is kept. -/
def mapChoice (owner : Nat) (fallback : Pqxdh.Bytes) {count : Nat}
    (result : ReportResult KemSK A (Cut KemSK X) count) :
    ReportResult KemSK A PqxdhRegistrationJointFinalCandidate.Choice count :=
  (((result.1.1.1.map (fun outcome => (outcome.1, choice owner fallback outcome.2.1, outcome.2.2)),
    result.1.1.2), result.1.2), result.2)

/-- The report run of the selected prefix program is the `mapChoice` image of the report run of the raw-accept scan. -/
theorem selected_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (index owner : Nat) (fallback : Pqxdh.Bytes) :
    PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
        (selected work index owner fallback) runtime) =
      mapChoice owner fallback <$>
        PqxdhJointPhase1Reports.run setup.joint count
          (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
            (scan work index) runtime) := by
  rw [selected, initialized_map, run_map]
  rfl

/-- The source projection of a mapped outcome is the source projection of the original outcome with the same program-result map; the reattached pools and the source state are unchanged. -/
theorem sourceResult_map (owner : Nat) (fallback : Pqxdh.Bytes) {count : Nat}
    (result : ReportResult KemSK A (Cut KemSK X) count) :
    sourceResult (mapChoice owner fallback result) =
      ((sourceResult result).1.map (fun encoded => (encoded.1, choice owner fallback encoded.2.1, encoded.2.2)),
        (sourceResult result).2) := by
  rcases result with ⟨⟨⟨_ | outcome, localState⟩, registry⟩, state⟩ <;> rfl

/-- A pending cut maps to the final choice `(owner, raw)` with the same Server and encoded state. -/
theorem raw_eq (owner : Nat) (fallback : Pqxdh.Bytes) {count : Nat}
    (result : ReportResult KemSK A (Cut KemSK X) count)
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (Cut KemSK X))
    (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) X)
    (finished : (sourceResult result).1 = some encoded) (pending : encoded.2.1 = .pending raw next) :
    (sourceResult (mapChoice owner fallback result)).1 = some (encoded.1, (owner, raw), encoded.2.2) := by
  rw [sourceResult_map, finished]
  simp only [Option.map_some, pending, choice]

end BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.commands_initialized_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.commands_initialized_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.initialized_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.initialized_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.run_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.cut_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.cut_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.split_snd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.split_snd

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.split_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.split_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.commands_initialized_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.commands_initialized_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.reduction_map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.reduction_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.initialized_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.initialized_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.run_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.run_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.selected_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.selected_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.sourceResult_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.sourceResult_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.raw_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports.raw_eq
