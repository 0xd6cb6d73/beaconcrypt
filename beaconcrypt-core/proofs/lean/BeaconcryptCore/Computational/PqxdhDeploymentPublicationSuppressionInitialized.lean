-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule
import BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource
import BeaconcryptCore.Computational.PqxdhDeploymentInterface

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhDeploymentPublicationSuppression (Selection)
open PqxdhRegistrationJointServerBirth (ClientCreated)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry EncodedState encodeState)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

abbrev Outcome (KemSK Result : Type) := ClientCreated Unit × Result × NativeState KemSK × ((List EncodedEntry × (Nat → Option PqxdhEd25519EufCma.Phase1Candidate)) × Selection)
abbrev SourceOutcome (KemSK Result : Type) := ClientCreated Unit × Result × PqxdhDeploymentPublicationSuppressionSchedule.State KemSK
abbrev EncodedOutcome (KemSK Result : Type) := ClientCreated Unit × Result × (EncodedState KemSK × Selection)

/-- The actual generated/imported Server constructor and open indexed backend execute the modified handle schedule; generated identity seeds remain outside this program. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    OracleComp (PqxdhRegistrationJointServerBirth.Spec KemSK) (Option (Outcome KemSK Result)) := do
  let born ← PqxdhRegistrationJointServerBirth.client (P := Unit) setup.serverKeyId supplied
  match born with
  | none => pure none
  | some created =>
    (fun result => some (created, result.1.1, result.2, result.1.2)) <$>
      simulateQ PqxdhRegistrationJointOpenInitialization.poolLift
        ((simulateQ (PqxdhRegistrationJointOpenBackend.impl setup codec checks
            created.server.server.metadata.identityIndex created.publicIdentity)
          ((simulateQ (PqxdhDeploymentPublicationSuppressionSchedule.handler setup codec) program).run
            (([], fun _ => none), Selection.initial ordinal))).run (PqxdhRegistrationJointInitializedAccept.initial created))

def attach (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (result : Outcome KemSK Result) :
    EncodedOutcome KemSK Result :=
  (result.1, result.2.1, (⟨pool, result.2.2.1, result.2.2.2.1.1, result.2.2.2.1.2⟩, result.2.2.2.2))

def encodeOutcome (setup : Setup baseSpec KemSK) (result : SourceOutcome KemSK Result) :
    EncodedOutcome KemSK Result :=
  (result.1, result.2.1, (encodeState setup result.2.2.1, result.2.2.2))

/-- This mathematical source interpretation uses the same actual constructor and retains every native/private/runtime coordinate. -/
noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    StateT (PqxdhRegistrationJointServerPrefix.State KemSK A) ProbComp (Option (SourceOutcome KemSK Result)) := fun state => do
  let born ← (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result.1, result.2),
      (result.2.1.pool, born.2.2))) <$>
      (simulateQ (PqxdhDeploymentPublicationSuppressionSchedule.source setup codec checks created.seed
        created.server.server.metadata.identityIndex) program).run
          (PqxdhRegistrationJointSchedule.initial born.2.1 (PqxdhRegistrationSchedule.initial created).shared,
            Selection.initial ordinal)

noncomputable def run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    ProbComp (Option (EncodedOutcome KemSK Result) × PqxdhRegistrationJointServerPrefix.State KemSK A) :=
  (fun result => (result.1.map (attach result.2.1), result.2)) <$>
    (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
      (client setup codec checks supplied ordinal program)).run state

/-- The initialized modified handle program is exactly its complete actual-source execution, with ownership derived from the genuine constructor. -/
theorem run_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    run setup codec checks ensureInit supplied ordinal program state =
      (fun result => (result.1.map (encodeOutcome setup), result.2)) <$>
        (source setup codec checks ensureInit supplied ordinal program).run state := by
  have born := PqxdhRegistrationJointServerBirth.client_source (P := Unit) setup ensureInit setup.serverKeyId supplied state
  simp only [run, client, simulateQ_bind, StateT.run_bind, map_bind]
  rw [born]
  conv_rhs => dsimp only [source, StateT.run]
  simp only [bind_map_left, map_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨(_ | created), after⟩ supported
  · simp only [Option.map_none, simulateQ_pure, StateT.run_pure, map_pure]
  · have owned : PqxdhRegistrationJointServerSchedule.Owned created.seed
        created.server.server.metadata.identityIndex
        (PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared) :=
      ⟨PqxdhRegistrationJointSchedule.initial_owned _ _,
        PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit setup.serverKeyId supplied state after created supported⟩
    simp only [Option.map_some, simulateQ_map, StateT.run_map, PqxdhRegistrationJointOpenInitialization.lifted_run,
      PqxdhRegistrationJointServerBirth.encode]
    have publicSame := PqxdhRegistrationJointInitializedAccept.source_public setup.joint ensureInit setup.serverKeyId supplied state after created supported
    rw [publicSame]
    have initialState : PqxdhRegistrationJointInitializedAccept.initial
        (PqxdhRegistrationJointServerBirth.encode created) = (PqxdhRegistrationSchedule.initial created).shared :=
      congrArg (fun value : EncodedState KemSK => value.shared)
        (PqxdhRegistrationJointInitializedSchedule.initial_encode setup after.1 created)
    simp only [PqxdhRegistrationJointServerBirth.encode, publicSame] at initialState
    rw [initialState]
    have commands := PqxdhDeploymentPublicationSuppressionSchedule.program_source setup codec checks created.seed
      created.server.server.metadata.identityIndex program
      (PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared,
        Selection.initial ordinal) owned
    have backend := PqxdhRegistrationJointOpenBackend.program_run setup codec checks
      created.server.server.metadata.identityIndex (setup.joint.publicKeys created.seed)
      ((simulateQ (PqxdhDeploymentPublicationSuppressionSchedule.handler setup codec) program).run
        (([], fun _ => none), Selection.initial ordinal))
      (after.1, (PqxdhRegistrationSchedule.initial created).shared)
    simp only [PqxdhDeploymentPublicationSuppressionSchedule.execute, encodeState,
      PqxdhRegistrationJointSchedule.initial, List.map_nil] at commands
    rw [← backend] at commands
    have mapped := congrArg
      (fun work : ProbComp (Result × (EncodedState KemSK × Selection)) =>
        (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result.1, result.2),
          (result.2.1.pool, after.2))) <$> work) commands
    simpa only [PqxdhRegistrationJointOpenBackend.run, Functor.map_map, attach, encodeOutcome, StateT.run,
      Option.map_some, PqxdhRegistrationJointServerBirth.encode, publicSame, encodeState,
      PqxdhRegistrationJointSchedule.initial] using mapped

/-- The executable ordinary-game client owns only public identity handles, private local KEM/runtime state and the suppression countdown. -/
noncomputable def initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A) :=
  PqxdhRegistrationJointIdentityCompiler.reduction setup ensureInit (client setup codec checks supplied ordinal program)
    (PqxdhLiveKemBirth.empty, runtime) ⟨[], []⟩

/-- Source-state reconstruction is applied only after interpreting the external ordinary challenger. -/
def initializedResult
    (result : (((Option (Outcome KemSK Result) × PqxdhRegistrationJointIdentityCompiler.Local KemSK A) ×
      PqxdhRegistrationJointIdentityRouting.Registry) × PqxdhDynamicIdentityPool.SourceState)) :
    Option (EncodedOutcome KemSK Result) × PqxdhRegistrationJointServerPrefix.State KemSK A :=
  let decoded := PqxdhRegistrationJointIdentityCompiler.projectResult result
  (decoded.1.map (attach decoded.2.1), decoded.2)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine ordinary joint-game client reconstructs the full modified initialized source, including every suppressed private-history omission. -/
theorem initialized_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A) :
    initializedResult <$>
      (simulateQ (PqxdhDynamicIdentityPool.lazyImpl setup.joint)
        (initialized setup codec checks ensureInit supplied ordinal program runtime)).run PqxdhDynamicIdentityPool.initialState =
      (fun result => (result.1.map (encodeOutcome setup), result.2)) <$>
        (source setup codec checks ensureInit supplied ordinal program).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) := by
  rw [← run_source]
  have correspondence := PqxdhRegistrationJointIdentityCompiler.reduction_source setup ensureInit
    (client setup codec checks supplied ordinal program) (PqxdhLiveKemBirth.empty, runtime)
    (⟨[], []⟩, PqxdhDynamicIdentityPool.initialState) PqxdhRegistrationJointIdentityRouting.initial_valid
  have mapped := congrArg
    (fun work : ProbComp (Option (Outcome KemSK Result) × PqxdhRegistrationJointServerPrefix.State KemSK A) =>
      (fun result => (result.1.map (attach result.2.1), result.2)) <$> work) correspondence
  simp only [initialized, run, Functor.map_map] at mapped ⊢
  convert mapped using 1
  all_goals rfl

/-- The source client leaves the existing report protocol and indexed router transparent; no terminal report or extra identity service is added here. -/
noncomputable def sourceClient (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A) :=
  PqxdhRegistrationJointReportCompiler.reduction setup ensureInit
    (PqxdhRegistrationJointReportLift.lift (client setup codec checks supplied ordinal program))
    (PqxdhLiveKemBirth.empty, runtime) ⟨[], []⟩

/-- Erasing only report instrumentation recovers the exact ordinary source reduction. -/
theorem sourceClient_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A) :
    simulateQ PqxdhRegistrationJointReportLift.erase
      (sourceClient setup codec checks ensureInit supplied ordinal program runtime) =
      initialized setup codec checks ensureInit supplied ordinal program runtime := by
  rw [sourceClient, PqxdhRegistrationJointReportCompiler.reduction_erase,
    PqxdhRegistrationJointReportLift.erase_lift]
  rfl

/-- The actual report-game source execution has precisely the modified initialized source distribution after forgetting public monitors. -/
theorem sourceClient_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A) :
    (fun result => initializedResult (result.1, result.2.2.source.2)) <$>
      PqxdhJointPhase1Reports.run setup.joint count
        (sourceClient setup codec checks ensureInit supplied ordinal program runtime) =
      (fun result => (result.1.map (encodeOutcome setup), result.2)) <$>
        (source setup codec checks ensureInit supplied ordinal program).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) := by
  have projection := PqxdhRegistrationJointReportSource.program_projection setup.joint count
    (sourceClient setup codec checks ensureInit supplied ordinal program runtime)
    (PqxdhJointPhase1Reports.initialMonitor count,
      ⟨PqxdhDynamicIdentityReports.initialSource count, PqxdhDynamicIdentityReports.initialSnapshot count, false, []⟩)
  have complete := congrArg (fun work => initializedResult <$> work) projection
  rw [sourceClient_erase] at complete
  simpa only [PqxdhJointPhase1Reports.run, Functor.map_map] using
    complete.trans (initialized_source setup codec checks ensureInit supplied ordinal program runtime)

/-- The public deployment transcript extractor ignores all source-private analysis and suppression bookkeeping. -/
def finalTranscript
    (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (output : (Option (Outcome KemSK Result) × PqxdhRegistrationJointIdentityCompiler.Local KemSK A) ×
      PqxdhRegistrationJointIdentityRouting.Registry) : List PqxdhDeploymentInterface.Entry :=
  (output.1.1.map fun result => transcript result.2.1).getD []

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized.run_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized.initialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized.initialized_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized.sourceClient_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized.sourceClient_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized.sourceClient_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized.sourceClient_source
