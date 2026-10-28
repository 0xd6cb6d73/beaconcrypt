-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptReports
import BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhRegistrationJointAttemptTrace (NativeResult)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- One actual prepared tuple, tagged by its global public bundle-call position and private identity service slot. -/
structure Occurrence where
  ordinal : Nat
  ownerAddress : Nat
  identityIndex : Nat
  keys : Phase1KeyTuple
  reply : Option Pqxdh.Bytes
  deriving DecidableEq

/-- Every public bundle call consumes one position; only actually prepared calls append an occurrence. -/
structure Audit where
  nextBundle : Nat
  occurrences : List Occurrence
  deriving DecidableEq

def Audit.empty : Audit := ⟨0, []⟩

def Audit.record (audit : Audit) (address index : Nat) (reply : Option Pqxdh.Bytes)
    (tuples : List Phase1KeyTuple) : Audit :=
  ⟨audit.nextBundle + 1,
    audit.occurrences ++ tuples.map (fun keys => ⟨audit.nextBundle, address, index, keys, reply⟩)⟩

/-- The same literal one-time draw and native source result are retained alongside the chronological occurrence audit. -/
def trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (audit : Audit) : ProbComp (NativeResult KemSK × Audit) :=
  (fun result => (result.1, audit.record address index result.1.1.1 result.2)) <$>
    PqxdhRegistrationJointAttemptTrace.trace setup codec index owner pool []

/-- Audit erasure preserves the whole actual bundle return, including every private signing reply. -/
theorem trace_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (audit : Audit) :
    Prod.fst <$> trace setup codec address index owner pool audit =
      PqxdhRegistrationJointBundle.trace setup codec index owner pool := by
  simpa only [trace, Functor.map_map] using
    PqxdhRegistrationJointAttemptTrace.trace_source setup codec index owner pool []

/-- The source audit records exactly the fields prepared before signing, independently of writer success. -/
theorem trace_after (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (audit : Audit) :
    trace setup codec address index owner pool audit =
      match owner.beacon.phase with
      | .fresh _ _ _ => (fun scalar =>
          (PqxdhRegistrationJointBundle.after setup codec index owner (some scalar) pool,
            audit.record address index (PqxdhRegistrationJointBundle.after setup codec index owner (some scalar) pool).1.1
              (PqxdhRegistrationJointAttemptTrace.issued setup owner (some scalar)))) <$> sampleScalar
      | .freshWithCoins _ _ _ _ => pure
          (PqxdhRegistrationJointBundle.after setup codec index owner none pool,
            audit.record address index (PqxdhRegistrationJointBundle.after setup codec index owner none pool).1.1
              (PqxdhRegistrationJointAttemptTrace.issued setup owner none))
      | _ => pure (((none, owner), pool), audit.record address index none []) := by
  cases phase : owner.beacon.phase <;>
    simp [trace, PqxdhRegistrationJointAttemptTrace.trace,
      PqxdhRegistrationJointAttemptTrace.after, phase]

abbrev State (KemSK : Type) := PqxdhRegistrationJointSchedule.State KemSK × Audit

/-- Missing and inactive owners still consume their global public bundle-call ordinal. -/
def bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) : StateT (State KemSK) ProbComp (Option Pqxdh.Bytes) := fun state =>
  match state.1.owners[address]? with
  | none => pure (none, (state.1, state.2.record address 0 none []))
  | some entry =>
    (fun result => (result.1.1.1, ({ state.1 with
      pool := (result.1.2, state.1.pool.2),
      owners := state.1.owners.set address { entry with owner := result.1.1.2 } }, result.2))) <$>
        trace setup codec address entry.identityIndex entry.owner state.1.pool.1 state.2

/-- Forgetting only the audit recovers the exact existing source scheduler bundle operation. -/
theorem bundle_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (state : State KemSK) :
    (fun result => (result.1, result.2.1)) <$> (bundle setup codec address).run state =
      (PqxdhRegistrationJointSchedule.bundle setup codec address).run state.1 := by
  cases found : state.1.owners[address]? with
  | none => simp [bundle, PqxdhRegistrationJointSchedule.bundle, StateT.run, found]
  | some entry =>
    simp only [bundle, PqxdhRegistrationJointSchedule.bundle, StateT.run, found, Functor.map_map]
    rw [← trace_source setup codec address entry.identityIndex entry.owner state.1.pool.1 state.2]
    simp only [Functor.map_map]

def onSource (work : StateT (PqxdhRegistrationJointSchedule.State KemSK) ProbComp Result) :
    StateT (State KemSK) ProbComp Result := fun state =>
  (fun result => (result.1, (result.2, state.2))) <$> work.run state.1

theorem onSource_source
    (work : StateT (PqxdhRegistrationJointSchedule.State KemSK) ProbComp Result) (state : State KemSK) :
    (fun result => (result.1, result.2.1)) <$> (onSource work).run state = work.run state.1 := by
  simp only [onSource, StateT.run, Functor.map_map, Prod.mk.eta]
  change id <$> work.run state.1 = work.run state.1
  exact id_map _

/-- This monitor changes no source command or primitive interpretation; only bundle calls append audit data. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat) :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK) (StateT (State KemSK) ProbComp)
  | .inl (.inr (.bundle address)) => bundle setup codec address
  | query => onSource (PqxdhRegistrationJointServerSchedule.source setup codec checks serverSeed serverIndex query)

/-- Each actual source command keeps its complete public reply and native/private poststate after audit erasure. -/
theorem query_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : State KemSK) :
    (fun result => (result.1, result.2.1)) <$> (handler setup codec checks serverSeed serverIndex query).run state =
      (PqxdhRegistrationJointServerSchedule.source setup codec checks serverSeed serverIndex query).run state.1 := by
  rcases query with (coin | command) | read
  · exact onSource_source _ state
  · cases command
    case bundle address => exact bundle_source setup codec address state
    all_goals exact onSource_source _ state
  · exact onSource_source _ state

/-- The whole adaptive monitored source execution erases to the existing initialized scheduler's program semantics. -/
theorem program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (handler setup codec checks serverSeed serverIndex) program).run state =
      (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks serverSeed serverIndex) program).run state.1 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simpa only [bind_map_left] using congrArg
        (fun work => work >>= fun result =>
          (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks serverSeed serverIndex) (next result.1)).run result.2)
        (query_source setup codec checks serverSeed serverIndex query state)

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.trace_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.trace_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.trace_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.trace_after

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.bundle_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.onSource_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.onSource_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace.program_source
