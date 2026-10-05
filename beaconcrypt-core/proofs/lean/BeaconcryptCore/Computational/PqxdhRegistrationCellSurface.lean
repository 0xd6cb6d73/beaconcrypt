-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationCellState
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-! The raw public constructor and complete adaptive registration surface preserve the exact native source execution under live-cell representation. Runtime effects and both cryptographic caches remain part of the same program. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationCells
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

def encodeRuntime (state : A × Source.State KemSK) : A × State KemSK := (state.1, encode state.2)

/-- Runtime initialization precedes raw pin parsing, even on a failed attempt. Accepted construction uses the same concrete source generators and publishes the old numeric allocation index. -/
noncomputable def rawCreate (setup : Setup baseSpec KemSK) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bytes : Pqxdh.Bytes) (keyId : Std.U64) :
    StateT (A × State KemSK) ProbComp (Option Nat) := fun state => do
  let initialized ← ensureInit.run state.1
  if initialized.1 then
    match PqxdhRegistrationSchedule.parsePin checks bytes with
    | none => pure (none, initialized.2, state.2)
    | some pin => (fun result => (some result.1, initialized.2, result.2)) <$>
        (create setup pin keyId).run state.2
  else pure (none, initialized.2, state.2)

/-- Ordinary requests use the current complete runtime without restarting initialization or resetting protocol state. -/
def onProtocol (work : Game KemSK Result) : StateT (A × State KemSK) ProbComp Result := fun state =>
  (fun result => (result.1, state.1, result.2)) <$> work.run state.2

/-- Only the raw constructor is public; the existing surface type excludes the internal typed-pin bypass. -/
noncomputable def surfaceHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (ensureInit : StateT A ProbComp Bool) :
    QueryImpl PqxdhRegistrationSchedule.SurfaceSpec (StateT (A × State KemSK) ProbComp)
  | .inl coin => onProtocol (handler setup codec checks seed (.inl coin))
  | .inr (.create bytes keyId) => rawCreate setup checks ensureInit bytes keyId
  | .inr (.call request) => onProtocol (handler setup codec checks seed (.inr request.val))

/-- The full runtime/parser/generator continuation is identical, including initialized-runtime changes on every rejected constructor request. -/
theorem rawCreate_source (setup : Setup baseSpec KemSK) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bytes : Pqxdh.Bytes) (keyId : Std.U64)
    (state : A × Source.State KemSK) :
    (rawCreate setup checks ensureInit bytes keyId).run (encodeRuntime state) =
      (fun result => (result.1, encodeRuntime result.2)) <$>
        (PqxdhRegistrationSchedule.rawCreate setup checks ensureInit bytes keyId).run state := by
  simp only [rawCreate, PqxdhRegistrationSchedule.rawCreate, StateT.run, encodeRuntime, map_bind]
  apply bind_congr
  rintro ⟨ready, runtime⟩
  cases ready <;> simp only [Bool.false_eq_true, ite_false, ite_true, map_pure]
  cases parsed : PqxdhRegistrationSchedule.parsePin checks bytes <;> simp only [map_pure]
  simpa only [StateT.run, Functor.map_map] using congrArg
    (fun work => (fun result => (some result.1, runtime, result.2)) <$> work)
    (create_source setup _ keyId state.2)

/-- An ordinary source operation retains the runtime coordinate while its complete native query/state comparison is applied. -/
theorem ordinary_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (query : PqxdhRegistrationSchedule.Spec.Domain)
    (state : A × Source.State KemSK) :
    (onProtocol (handler setup codec checks seed query)).run (encodeRuntime state) =
      (fun result => (result.1, encodeRuntime result.2)) <$>
        (PqxdhRegistrationSchedule.onProtocol
          (PqxdhRegistrationSchedule.handler setup codec checks seed query)).run state := by
  simpa only [onProtocol, PqxdhRegistrationSchedule.onProtocol, StateT.run,
    encodeRuntime, Functor.map_map] using congrArg
    (fun work => (fun result => (result.1, state.1, result.2)) <$> work)
    (handler_source setup codec checks seed query state.2)

/-- Every raw public request has the same full source transition and reply; failed initialization/parsing and missing/future handles remain actual branches. -/
theorem surface_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (ensureInit : StateT A ProbComp Bool)
    (query : PqxdhRegistrationSchedule.SurfaceSpec.Domain) (state : A × Source.State KemSK) :
    (surfaceHandler setup codec checks seed ensureInit query).run (encodeRuntime state) =
      (fun result => (result.1, encodeRuntime result.2)) <$>
        (PqxdhRegistrationSchedule.surfaceHandler setup codec checks seed ensureInit query).run state := by
  rcases query with coin | (⟨bytes, keyId⟩ | request)
  · exact ordinary_source setup codec checks seed (.inl coin) state
  · exact rawCreate_source setup checks ensureInit bytes keyId state
  · exact ordinary_source setup codec checks seed (.inr request.val) state

/-- The complete adaptive raw-interface program preserves every source answer and the injectively represented native/private state. No operation, failure or primitive draw is omitted. -/
theorem surface_program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (ensureInit : StateT A ProbComp Bool)
    (work : OracleComp PqxdhRegistrationSchedule.SurfaceSpec Result) (state : A × Source.State KemSK) :
    (simulateQ (surfaceHandler setup codec checks seed ensureInit) work).run (encodeRuntime state) =
      (fun result => (result.1, encodeRuntime result.2)) <$>
        (simulateQ (PqxdhRegistrationSchedule.surfaceHandler setup codec checks seed ensureInit) work).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq
    (PqxdhRegistrationSchedule.surfaceHandler setup codec checks seed ensureInit)
    (surfaceHandler setup codec checks seed ensureInit) encodeRuntime
    (fun query before => (surface_source setup codec checks seed ensureInit query before).symm)
    work state).symm

/-- The actual public identity and sender of the constructed Server are the adversary's input. Its private seed remains in the original native interpreter. -/
noncomputable def cellExecute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (adversary : PublicIdentity → Std.U64 → OracleComp PqxdhRegistrationSchedule.SurfaceSpec Result)
    (created : PqxdhLiveServerConstruction.Created Unit) (runtime : A) :
    ProbComp (Result × (A × State KemSK)) :=
  (simulateQ (surfaceHandler setup codec checks created.seed ensureInit)
    (adversary created.publicIdentity created.server.server.metadata.sender)).run
    (runtime, encode (PqxdhRegistrationSchedule.initial created))

/-- Both supplied and generated Server initialization paths run the literal source constructor before the first adaptive request. -/
noncomputable def experiment (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp PqxdhRegistrationSchedule.SurfaceSpec Result)
    (runtime : A) :
    ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × (Result × State KemSK)) × A) := do
  let started ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit 0 setup.serverKeyId supplied).run runtime
  match started.1 with
  | none => pure (none, started.2)
  | some created => ((fun result => (some (created, result.1, result.2.2), result.2.1)) <$>
      (cellExecute setup codec checks ensureInit adversary created started.2))

def encodeOutcome
    (outcome : Option (PqxdhLiveServerConstruction.Created Unit × (Result × Source.State KemSK)) × A) :
    Option (PqxdhLiveServerConstruction.Created Unit × (Result × State KemSK)) × A :=
  (outcome.1.map (fun result => (result.1, result.2.1, encode result.2.2)), outcome.2)

/-- The full adversary and its exact public constructor input have the same complete adaptive source execution. -/
theorem execute_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (adversary : PublicIdentity → Std.U64 → OracleComp PqxdhRegistrationSchedule.SurfaceSpec Result)
    (created : PqxdhLiveServerConstruction.Created Unit) (runtime : A) :
    cellExecute setup codec checks ensureInit adversary created runtime =
      (fun result => (result.1, encodeRuntime result.2)) <$>
        PqxdhRegistrationSchedule.surfaceExecute setup codec checks ensureInit adversary created runtime :=
  surface_program_source setup codec checks created.seed ensureInit
    (adversary created.publicIdentity created.server.server.metadata.sender)
    (runtime, PqxdhRegistrationSchedule.initial created)

/-- Complete evaluated experiment equality retains the actual Server constructor, intermediate runtime, all adaptive replies and both full primitive caches. Only owner storage is represented by live cells. -/
theorem experiment_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp PqxdhRegistrationSchedule.SurfaceSpec Result)
    (runtime : A) :
    experiment setup codec checks ensureInit supplied adversary runtime =
      encodeOutcome <$> PqxdhRegistrationSchedule.surfaceExperiment setup codec checks ensureInit supplied adversary runtime := by
  simp only [experiment, PqxdhRegistrationSchedule.surfaceExperiment, map_bind]
  apply bind_congr
  rintro ⟨created, initialized⟩
  cases created <;> simp only [map_pure, encodeOutcome, Option.map_none]
  rw [execute_source]
  simp only [Functor.map_map, encodeOutcome, encodeRuntime, Option.map_some]

/-- Every predicate-based interpreted query certificate is identical; the storage relation does not hide sampling, rejected requests or source callback work. -/
theorem experiment_bound_iff (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp PqxdhRegistrationSchedule.SurfaceSpec Result)
    (runtime : A) (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (cap : Nat) :
    (experiment setup codec checks ensureInit supplied adversary runtime).IsQueryBoundP predicate cap ↔
      (PqxdhRegistrationSchedule.surfaceExperiment setup codec checks ensureInit supplied adversary runtime).IsQueryBoundP predicate cap := by
  rw [experiment_source, isQueryBoundP_map_iff]

/-- The concrete complete source bill includes initial Server construction and every attempted raw registration request. Primitive base randomness remains inside the declared KEM costs. -/
theorem experiment_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp PqxdhRegistrationSchedule.SurfaceSpec Result)
    (budget : Fin 9 → Nat)
    (certified : ∀ identity keyId, PqxdhRegistrationSchedule.UniformBounded (adversary identity keyId) budget)
    (runtime : A) :
    (experiment setup codec checks ensureInit supplied adversary runtime).IsTotalQueryBound
      (qInit + (if supplied.isNone then 32 else 0) +
        ∑ kind, PqxdhRegistrationSchedule.uniformCost caps qInit kind * budget kind) := by
  simpa only [experiment_source, IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhRegistrationSchedule.surfaceExperiment_uniform setup codec checks caps bounded ensureInit qInit
      initBound supplied adversary budget certified runtime

/-- A chronological public-request journal records each actual reply after its request returns. It adds no observation to the adversary's original public interface. -/
def journal (work : OracleComp PqxdhRegistrationSchedule.SurfaceSpec Result) :
    OracleComp PqxdhRegistrationSchedule.SurfaceSpec (Result × QueryLog PqxdhRegistrationSchedule.SurfaceSpec) :=
  (simulateQ loggingOracle work).run

/-- The exact whole chronological API trace is preserved by the cell representation, together with the same original result, constructor, runtime and private state. -/
theorem journal_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp PqxdhRegistrationSchedule.SurfaceSpec Result)
    (runtime : A) :
    experiment setup codec checks ensureInit supplied (fun identity sender => journal (adversary identity sender)) runtime =
      encodeOutcome <$> PqxdhRegistrationSchedule.surfaceExperiment setup codec checks ensureInit supplied
        (fun identity sender => journal (adversary identity sender)) runtime :=
  experiment_source setup codec checks ensureInit supplied _ runtime

/-- Recording every actual reply preserves all nine source request-class caps over every adaptive continuation. -/
theorem journal_classes (work : OracleComp PqxdhRegistrationSchedule.SurfaceSpec Result)
    (budget : Fin 9 → Nat) :
    PqxdhRegistrationSchedule.UniformBounded (journal work) budget ↔
      PqxdhRegistrationSchedule.UniformBounded work budget := by
  exact forall_congr' fun _ => isQueryBoundP_iff_of_map_eq
    (loggingOracle.fst_map_run_simulateQ work)

end BeaconcryptCore.Computational.PqxdhRegistrationCells

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.rawCreate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.rawCreate_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.ordinary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.ordinary_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.surface_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.surface_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.surface_program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.surface_program_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.execute_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.execute_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.experiment_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.experiment_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.experiment_bound_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.experiment_bound_iff
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.experiment_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.experiment_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.journal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.journal_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.journal_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.journal_classes
