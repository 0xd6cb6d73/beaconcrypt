-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationR1Surface
import BeaconcryptCore.Computational.PqxdhRegistrationCellSurface

/-! The exact chronological public journal of the singleton raw-surface program. The actual raw-create and first-bundle replies are recorded at their source positions, and every restricted suffix entry is the original R1 query and reply under the surface request that the route issues. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationR1Journal
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationR1Restriction PqxdhRegistrationR1Initial PqxdhRegistrationR1Surface
open PqxdhRegistrationSchedule (SurfaceSpec SurfaceRequest IsConstructor)
variable {ι KemSK Reader Response Result A : Type} {baseSpec : OracleSpec ι}

/-- Each original public entry is recorded under the exact surface request issued by `surfaceRoute`, with the same reply. A finish entry names owner zero, as the route does. -/
def routeEntry : ((query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) →
    ((query : SurfaceSpec.Domain) × SurfaceSpec.Range query)
  | ⟨.inl coin, reply⟩ => ⟨.inl coin, reply⟩
  | ⟨.inr (.accept raw), reply⟩ => ⟨.inr (.call ⟨.accept raw, by simp [IsConstructor]⟩), reply⟩
  | ⟨.inr (.build index payload), reply⟩ =>
      ⟨.inr (.call ⟨.build index payload, by simp [IsConstructor]⟩), reply⟩
  | ⟨.inr (.finish raw), reply⟩ => ⟨.inr (.call ⟨.finish 0 raw, by simp [IsConstructor]⟩), reply⟩
  | ⟨.inr (.hmac key bytes), reply⟩ => ⟨.inr (.call ⟨.hmac key bytes, by simp [IsConstructor]⟩), reply⟩
  | ⟨.inr (.hash bytes), reply⟩ => ⟨.inr (.call ⟨.hash bytes, by simp [IsConstructor]⟩), reply⟩
  | ⟨.inr (.reveal index), reply⟩ => ⟨.inr (.call ⟨.reveal index, by simp [IsConstructor]⟩), reply⟩

/-- The original R1 journal, entry by entry, in surface coordinates. No entry is added, removed or reordered. -/
def restrictLog (log : QueryLog ServerAuthSpec) : QueryLog SurfaceSpec :=
  log.map routeEntry

/-- Journaling the routed suffix is the routed original journal: the surface log is the original R1 log mapped entry by entry, with the same result. This is a syntactic program equality before any interpretation. -/
theorem route_journal {Output : Type} (work : OracleComp ServerAuthSpec Output) :
    PqxdhRegistrationCells.journal (simulateQ surfaceRoute work) =
      Prod.map id restrictLog <$> simulateQ surfaceRoute ((simulateQ loggingOracle work).run) := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [PqxdhRegistrationCells.journal] at ih ⊢
      rw [run_simulateQ_loggingOracle_query_bind]
      simp only [simulateQ_bind (impl := surfaceRoute), simulateQ_spec_query (impl := surfaceRoute),
        simulateQ_map (impl := surfaceRoute), map_bind, Functor.map_map]
      rcases query with coin | (_ | _ | _ | _ | _ | _)
      all_goals simp only [surfaceRoute, run_simulateQ_loggingOracle_query_bind, ih, Functor.map_map]
      all_goals rfl

/-- The singleton program whose restricted continuation may also read the actual raw-create reply. `program` is the case that ignores it. -/
def programWith (identity : PublicIdentity) (sender : Std.U64)
    (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result) : OracleComp SurfaceSpec Result := do
  let created ← SurfaceSpec.query (.inr (.create identity.ed25519.toList sender))
  let published ← SurfaceSpec.query (.inr (.call ⟨.bundle 0, by simp [IsConstructor]⟩))
  simulateQ surfaceRoute (work created ⟨identity, sender, published, none⟩)

/-- The checked `program` is literally the create-reply-ignoring instance. -/
theorem program_with (identity : PublicIdentity) (sender : Std.U64)
    (work : AuthInput → OracleComp ServerAuthSpec Result) :
    program identity sender work = programWith identity sender (fun _ => work) := rfl

/-- The raw-create and first-bundle entries, with the actual create reply and the actual bundle reply delivered to the continuation as its Phase1 input. -/
def prefixLog (input : AuthInput) (created : Option Nat) : QueryLog SurfaceSpec :=
  [⟨.inr (.create input.server.ed25519.toList input.serverKeyId), created⟩,
    ⟨.inr (.call ⟨.bundle 0, by simp [IsConstructor]⟩), input.phase1⟩]

/-- The original continuation, journaled over its own seven-API interface and returned with the complete surface journal. -/
def journalWork (work : AuthInput → OracleComp ServerAuthSpec Result) (created : Option Nat) (input : AuthInput) :
    OracleComp ServerAuthSpec (Result × QueryLog SurfaceSpec) :=
  (fun result => (result.1, prefixLog input created ++ restrictLog result.2)) <$>
    (simulateQ loggingOracle (work input)).run

/-- Journaling the whole singleton program records the actual create reply, the actual bundle reply and then the original R1 journal in surface coordinates. The result is unchanged. -/
theorem program_journal (identity : PublicIdentity) (sender : Std.U64)
    (work : AuthInput → OracleComp ServerAuthSpec Result) :
    PqxdhRegistrationCells.journal (program identity sender work) =
      programWith identity sender (journalWork work) := by
  simp only [PqxdhRegistrationCells.journal, program, programWith, journalWork]
  rw [run_simulateQ_loggingOracle_query_bind]
  refine bind_congr fun created => ?_
  rw [run_simulateQ_loggingOracle_query_bind, map_bind]
  refine bind_congr fun published => ?_
  have routed := route_journal (work ⟨identity, sender, published, none⟩)
  simp only [PqxdhRegistrationCells.journal] at routed
  rw [routed, simulateQ_map]
  simp only [Functor.map_map]
  rfl

/-- The typed constructor replies with the prior owner count after every actual draw. -/
theorem create_reply (setup : Setup baseSpec KemSK) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (keyId : Std.U64) (state : PqxdhRegistrationSchedule.State KemSK) :
    (fun result => (state.owners.length, result.2)) <$> PqxdhRegistrationSchedule.create setup pin keyId state =
      PqxdhRegistrationSchedule.create setup pin keyId state := by
  rw [PqxdhRegistrationSchedule.create_source]
  simp only [map_bind, map_pure]

/-- On the constructed Server's initial state, which has no owner yet, the actual typed constructor reply is owner index zero. -/
theorem create_initial (setup : Setup baseSpec KemSK) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (keyId : Std.U64) (created : PqxdhLiveServerConstruction.Created Unit) :
    (fun result => (0, result.2)) <$>
        PqxdhRegistrationSchedule.create setup pin keyId (PqxdhRegistrationSchedule.initial created) =
      PqxdhRegistrationSchedule.create setup pin keyId (PqxdhRegistrationSchedule.initial created) := by
  have reply := create_reply setup pin keyId (PqxdhRegistrationSchedule.initial created)
  rwa [show (PqxdhRegistrationSchedule.initial (KemSK := KemSK) created).owners.length = 0 from rfl] at reply

set_option backward.isDefEq.respectTransparency false in
/-- Complete raw creation, optional bundle and adaptive continuation, where the continuation also receives the actual raw-create reply. -/
theorem programWith_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (ensureInit : StateT A ProbComp Bool) (identity : PublicIdentity)
    (sender : Std.U64) (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result)
    (runtime : A) (state : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationSchedule.surfaceHandler setup codec checks serverSeed ensureInit)
      (programWith identity sender work)).run (runtime, state) =
    (do
      let created ← (PqxdhRegistrationSchedule.rawCreate setup checks ensureInit identity.ed25519.toList sender).run
        (runtime, state)
      (fun result => (result.1, created.2.1, result.2)) <$> (do
        let published ← (PqxdhRegistrationSchedule.bundle setup codec 0).run created.2.2
        (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks serverSeed)
          (simulateQ route (work created.1 ⟨identity, sender, published.1, none⟩))).run published.2)) := by
  simp only [programWith, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    PqxdhRegistrationSchedule.surfaceHandler, PqxdhRegistrationSchedule.handler]
  refine bind_congr fun created => ?_
  rw [show (PqxdhRegistrationSchedule.onProtocol
    (PqxdhRegistrationSchedule.bundle setup codec 0)).run created.2 =
    (fun result => (result.1, created.2.1, result.2)) <$>
      (PqxdhRegistrationSchedule.bundle setup codec 0).run created.2.2 from rfl]
  simp only [bind_map_left, route_program, map_bind]

/-- `prefixAudit` for a continuation that also reads the create reply: `some 0` after actual creation of owner zero, `none` after initialization refusal. -/
noncomputable def prefixAuditWith (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (origin : PqxdhLiveServerConstruction.Origin)
    (ensureInit : StateT A ProbComp Bool) (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result)
    (runtime : A) : ProbComp (PrefixOutcome KemSK Result × A) := do
  let initialized ← ensureInit.run runtime
  let publicIdentity := setup.joint.publicKeys serverSeed
  let continuation := fun created published => work created ⟨publicIdentity, setup.serverKeyId, published, none⟩
  let rejected := (fun result => (PrefixOutcome.rejected result, initialized.2)) <$>
    tail setup codec checks serverSeed (continuation none) (PqxdhRegistrationSchedule.initial
      (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed))
  if initialized.1 then
    (fun audit => (PrefixOutcome.created audit, initialized.2)) <$>
      audited setup codec checks serverSeed (continuation (some 0))
  else rejected

/-- The checked `prefixAudit` is literally the create-reply-ignoring instance. -/
theorem prefix_with (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (origin : PqxdhLiveServerConstruction.Origin)
    (ensureInit : StateT A ProbComp Bool) (work : AuthInput → OracleComp ServerAuthSpec Result) (runtime : A) :
    prefixAudit setup codec checks serverSeed origin ensureInit work runtime =
      prefixAuditWith setup codec checks serverSeed origin ensureInit (fun _ => work) runtime := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The raw-surface prefix law of `initial_audit`, for a continuation that also reads the actual create reply. -/
theorem initialWith_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (origin : PqxdhLiveServerConstruction.Origin)
    (ensureInit : StateT A ProbComp Bool) (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result)
    (runtime : A) :
    (fun result => (result.1, result.2.1, eraseShared result.2.2)) <$>
      PqxdhRegistrationSchedule.surfaceExecute setup codec checks ensureInit
        (fun identity sender => programWith identity sender work)
        (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed) runtime =
    (fun result => ((observePrefix (PqxdhRegistrationSchedule.bookkeeping
        (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed)) result.1).1,
      result.2, (observePrefix (PqxdhRegistrationSchedule.bookkeeping
        (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed)) result.1).2)) <$>
      prefixAuditWith setup codec checks serverSeed origin ensureInit work runtime := by
  rw [PqxdhRegistrationSchedule.surfaceExecute, programWith_run]
  simp only [prefixAuditWith, PqxdhRegistrationSchedule.rawCreate, StateT.run, map_bind, bind_assoc]
  refine bind_congr fun initialized => ?_
  rcases initialized with ⟨_ | _, afterRuntime⟩
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, Functor.map_map]
  all_goals first | rfl | rw [parse_public]
  dsimp only [PqxdhLiveServerConstruction.initialized]
  simp only [bind_map_left, observePrefix]
  rw [← create_initial]
  simp only [bind_map_left]
  simpa only [map_bind, Functor.map_map, StateT.run, PqxdhLiveServerConstruction.initialized,
    Prod.map, Function.comp_def, id_eq] using
    congrArg (fun computation => (fun result => (result.1, afterRuntime, result.2)) <$> computation)
      (typed_audit setup codec checks serverSeed origin
        (fun published => work (some 0) ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩))

/-- `auditedExperiment` for a continuation that also reads the create reply. Both real initialization calls and supplied/generated Server creation precede the private source classification. As in `auditedExperiment`, the only runtime coordinate of the output is the final runtime; the runtime after construction is the input of the second initialization call. -/
noncomputable def auditedExperimentWith (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result) (runtime : A) :
    ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × PrefixOutcome KemSK Result) × A) := do
  let started ← (PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit 0 setup.serverKeyId supplied).run runtime
  match started.1 with
  | none => pure (none, started.2)
  | some created =>
      (fun (result : PrefixOutcome KemSK Result × A) => (some (created, result.1), result.2)) <$>
        (prefixAuditWith setup codec checks created.seed created.origin ensureInit work started.2)

/-- The checked `auditedExperiment` is literally the create-reply-ignoring instance. -/
theorem audited_with (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (runtime : A) :
    auditedExperiment setup codec checks ensureInit supplied work runtime =
      auditedExperimentWith setup codec checks ensureInit supplied (fun _ => work) runtime := rfl

/-- The exact full raw-surface singleton experiment of `experiment_audit`, for a continuation that also reads the actual create reply. No constructor-success or generated-seed premise is supplied. -/
theorem experimentWith_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : Option Nat → AuthInput → OracleComp ServerAuthSpec Result) (runtime : A) :
    eraseExperiment <$> PqxdhRegistrationSchedule.surfaceExperiment setup codec checks ensureInit supplied
      (fun identity sender => programWith identity sender work) runtime =
    observeExperiment <$> auditedExperimentWith setup codec checks ensureInit supplied work runtime := by
  simp only [PqxdhRegistrationSchedule.surfaceExperiment, auditedExperimentWith, map_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨_ | created, afterRuntime⟩ supported
  all_goals simp only [map_pure, Functor.map_map, eraseExperiment, observeExperiment, Option.map_none, Option.map_some]
  obtain ⟨seed, rfl, -⟩ := PqxdhLiveServerConstruction.construct_origin setup.joint ensureInit 0
    setup.serverKeyId supplied runtime afterRuntime created supported
  have lifted := congrArg (fun computation => (fun result =>
      (some (PqxdhLiveServerConstruction.initialized (P := Unit) setup.joint 0 setup.serverKeyId
        (if supplied.isNone then .generated else .imported) seed, result.1, result.2.2), result.2.1)) <$>
        computation)
    (initialWith_audit setup codec checks seed (if supplied.isNone then .generated else .imported)
      ensureInit work afterRuntime)
  simp only [Functor.map_map] at lifted
  exact lifted

/-- The journaled singleton experiment. Its complete public journal (actual create reply, actual first-bundle reply, then every restricted query and reply in surface coordinates) is the journal assembled inside the same audited original R1 execution. After rejected creation the journal records the create reply `none` and the actual missing-owner bundle reply. -/
theorem experiment_journal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (runtime : A) :
    eraseExperiment <$> PqxdhRegistrationSchedule.surfaceExperiment setup codec checks ensureInit supplied
      (fun identity sender => PqxdhRegistrationCells.journal (program identity sender work)) runtime =
    observeExperiment <$> auditedExperimentWith setup codec checks ensureInit supplied (journalWork work) runtime := by
  simp only [program_journal]
  exact experimentWith_audit setup codec checks ensureInit supplied (journalWork work) runtime

end BeaconcryptCore.Computational.PqxdhRegistrationR1Journal

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.route_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.route_journal
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.program_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.program_with
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.program_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.program_journal
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.create_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.create_reply
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.create_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.create_initial
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.programWith_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.programWith_run
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.prefix_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.prefix_with
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.initialWith_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.initialWith_audit
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.audited_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.audited_with
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.experimentWith_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.experimentWith_audit
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.experiment_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Journal.experiment_journal
