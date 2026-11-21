-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAuditLedger

/-! Every successful prepared occurrence retains the exact tuple of its actual source signing and writer call. The original signing seed is existential bookkeeping only: the concrete key-free client still has no seed access, and the tuple reader ignores identity and signature representations. Phase 1 read-back therefore recovers the recorded tuple without a separate keys law. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppressionTrace
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Each successful occurrence is the original writer result for its recorded tuple, under the identity seed that actually signed it. -/
def Written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (audit : Audit) : Prop :=
  ∀ occurrence ∈ audit.occurrences, ∀ bytes, occurrence.reply = some bytes →
    ∃ seed, codec.write1 (PqxdhJointPhase1SourceWriter.signedCandidate setup.joint seed
      (setup.joint.publicKeys seed).ed25519 occurrence.keys) = some bytes

private theorem issued_written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (generated : Option PqxdhJointGapDh.ScalarBytes) (pool : PqxdhDynamicIdentityPool.SourceState)
    (keys : Phase1KeyTuple) (member : keys ∈ PqxdhRegistrationJointAttemptTrace.issued setup owner generated)
    (bytes : Pqxdh.Bytes)
    (published : (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1.1 = some bytes) :
    ∃ seed, codec.write1 (PqxdhJointPhase1SourceWriter.signedCandidate setup.joint seed
      (setup.joint.publicKeys seed).ed25519 keys) = some bytes := by
  unfold PqxdhRegistrationJointAttemptTrace.issued at member
  cases ready : PqxdhBeaconPhase1Publication.prepare owner generated with
  | none => simp only [ready, Option.map_none, Option.toList_none, List.not_mem_nil] at member
  | some prepared =>
    simp only [ready, Option.map_some, Option.toList_some, List.mem_singleton] at member
    subst keys
    refine ⟨owner.beacon.identity, ?_⟩
    unfold PqxdhRegistrationJointBundle.after at published
    rw [ready] at published
    dsimp only at published
    cases written : codec.write1 (PqxdhJointPhase1SourceWriter.signedCandidate setup.joint owner.beacon.identity
      (setup.joint.publicKeys owner.beacon.identity).ed25519 (PqxdhRegistrationJointAttemptTrace.keys setup prepared)) with
    | none =>
      simp only [PqxdhRegistrationJointAttemptTrace.keys] at written
      rw [written] at published
      cases published
    | some value =>
      simp only [PqxdhRegistrationJointAttemptTrace.keys] at written
      rw [written] at published
      change some value = some bytes at published
      exact published


private theorem after_written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (generated : Option PqxdhJointGapDh.ScalarBytes) (pool : PqxdhDynamicIdentityPool.SourceState) (audit : Audit)
    (held : Written setup codec audit) :
    Written setup codec (audit.record address index
      (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1.1
      (PqxdhRegistrationJointAttemptTrace.issued setup owner generated)) := by
  intro occurrence member bytes published
  rcases List.mem_append.mp member with old | added
  · exact held occurrence old bytes published
  · obtain ⟨keys, issued, same⟩ := List.mem_map.mp added
    subst occurrence
    exact issued_written setup codec index owner generated pool keys issued bytes published

/-- The literal Fresh draw and optional writer preserve all earlier source writer receipts. -/
theorem trace_written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState) (audit : Audit)
    (held : Written setup codec audit) (result : PqxdhRegistrationJointAttemptTrace.NativeResult KemSK × Audit)
    (supported : result ∈ support (trace setup codec address index owner pool audit)) :
    Written setup codec result.2 := by
  rw [trace_after] at supported
  cases phase : owner.beacon.phase <;> simp only [phase] at supported
  case fresh =>
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨scalar, _, same⟩ := supported
    subst result
    exact after_written setup codec address index owner (some scalar) pool audit held
  case freshWithCoins =>
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact after_written setup codec address index owner none pool audit held
  all_goals
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    simpa only [Written, Audit.record, List.map_nil, List.append_nil] using held

/-- Missing and inactive owners cannot introduce a spurious tuple receipt. -/
theorem bundle_written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (held : Written setup codec state.2) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) : Written setup codec result.2.2 := by
  cases found : state.1.owners[address]? with
  | none =>
    simp only [bundle, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    simpa only [Written, Audit.record, List.map_nil, List.append_nil] using held
  | some entry =>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, same⟩ := supported
    subst result
    have original : returned.1 ∈ support (trace setup codec address entry.identityIndex entry.owner
        state.1.pool.1 state.2) := by
      rw [← traceLogged_trace setup codec address entry.identityIndex entry.owner state.1.pool.1 state.2
        (state.1.inits address), support_map]
      exact ⟨returned, member, rfl⟩
    exact trace_written setup codec address entry.identityIndex entry.owner state.1.pool.1 state.2 held returned.1 original

/-- All actual source commands retain the writer/tuple provenance of the same prepared audit. -/
theorem query_written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : State KemSK)
    (held : Written setup codec state.2)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed serverIndex query).run state)) :
    Written setup codec result.2.2 := by
  rcases query with (coin | command) | read
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    exact held
  · cases command
    case bundle address => exact bundle_written setup codec address state held result supported
    all_goals
      simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨_, _, same⟩ := supported
      subst result
      exact held
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    exact held

/-- The whole adaptive source run retains literal original writer receipts for every successful occurrence. -/
theorem program_written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : State KemSK) (held : Written setup codec state.2) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex) program).run state)) :
    Written setup codec result.2.2 := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query _ (fun current => Written setup codec current.2)
    (fun query before valid after member => query_written setup codec checks serverSeed serverIndex query before
      valid after member) program state held result supported

/-- Actual compiled deployment outcomes have source-backed writer receipts, with no supplied tuple/codec law. -/
theorem compileFull_written {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (native : PqxdhRegistrationJointSchedule.State KemSK)
    (result : ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex)
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run (native, Audit.empty))) :
    Written setup codec result.2.2 := by
  exact program_written setup codec checks serverSeed serverIndex _ (native, Audit.empty)
    (by simp [Written, Audit.empty]) result supported

/-- The existing Phase 1 reader recovers exactly the successful occurrence's actual signed tuple. -/
theorem written_tuple (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (audit : Audit) (held : Written setup codec audit)
    (occurrence : Occurrence) (member : occurrence ∈ audit.occurrences) (bytes : Pqxdh.Bytes)
    (published : occurrence.reply = some bytes) :
    (PqxdhDeploymentTranscript.candidateOf codec bytes).bind PqxdhDeploymentPublishedTuple.candidateTuple =
      some occurrence.keys := by
  obtain ⟨seed, written⟩ := held occurrence member bytes published
  rw [PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written]
  exact PqxdhDeploymentPublishedTuple.candidateTuple_signed setup.joint seed _ occurrence.keys

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentPublicationSuppressionTrace (Occurrence)
open PqxdhDeploymentPublicationAuditWritten
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- Actual initialized source outcomes discharge every successful occurrence's original writer receipt. -/
theorem actual_written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime)) :
    Written setup codec outcome.2.2.2 := by
  simp only [actual, initialized, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨(_ | created), born⟩, _, continued⟩ := supported
  · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  · simp only [support_map, Set.mem_image] at continued
    obtain ⟨executed, member, equal⟩ := continued
    have same : outcome = (PqxdhRegistrationJointServerBirth.encode created, executed.1, executed.2) :=
      (Option.some.inj (congrArg Prod.fst equal)).symm
    rw [same]
    exact compileFull_written setup codec checks created.seed created.server.server.metadata.identityIndex route
      bounds mode adversary _ executed member

/-- Successful actual source occurrences decode to their recorded tuples without an assumed candidate-keys law. -/
theorem actual_occurrence_tuple (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime))
    (occurrence : Occurrence) (member : occurrence ∈ outcome.2.2.2.occurrences) (bytes : Pqxdh.Bytes)
    (published : occurrence.reply = some bytes) :
    (PqxdhDeploymentTranscript.candidateOf codec bytes).bind PqxdhDeploymentPublishedTuple.candidateTuple =
      some occurrence.keys := by
  exact written_tuple setup codec phase1 _
    (actual_written setup codec checks route ensureInit bounds mode adversary runtime outcome after supported)
    occurrence member bytes published

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.trace_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.trace_written

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.bundle_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.bundle_written

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.query_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.query_written

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.program_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.program_written

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.compileFull_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.compileFull_written

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.written_tuple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten.written_tuple

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_written

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_tuple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_tuple
