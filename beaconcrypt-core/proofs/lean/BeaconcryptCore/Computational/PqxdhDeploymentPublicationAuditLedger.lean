-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-! The private prepared-tuple audit and the public deployment ledger come from the same adaptive source execution. Successful audited replies are exactly the successful bundle entries in the final public transcript. Registration query logging is pure instrumentation of that identical full native/private state, rather than a second independently sampled source execution. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppressionTrace
open PqxdhDeploymentRegistrationTrace (Logged traceFrom record)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Successful native bundle replies, with the actual addressed owner, in source call order. -/
def publications (audit : Audit) : List (Nat × Pqxdh.Bytes) :=
  audit.occurrences.filterMap fun occurrence => occurrence.reply.map (fun bytes => (occurrence.ownerAddress, bytes))

/-- Successful bundle replies in the existing source registration-query log. -/
def loggedPublications (log : List Logged) : List (Nat × Pqxdh.Bytes) :=
  log.filterMap fun entry => match entry with
    | .bundle address reply => reply.map (fun bytes => (address, bytes))
    | .accept _ _ => none

private theorem after_publications (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (generated : Option PqxdhJointGapDh.ScalarBytes) (pool : PqxdhDynamicIdentityPool.SourceState) (audit : Audit) :
    publications (audit.record address index
        (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1.1
        (PqxdhRegistrationJointAttemptTrace.issued setup owner generated)) =
      publications audit ++ ((PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1.1.map
        (fun bytes => (address, bytes))).toList := by
  unfold PqxdhRegistrationJointBundle.after PqxdhRegistrationJointAttemptTrace.issued
  cases prepared : PqxdhBeaconPhase1Publication.prepare owner generated with
  | none => simp [publications, Audit.record]
  | some prepared =>
    simp only [Option.map_some, Option.toList_some]
    split <;> simp [publications, Audit.record]

/-- The same actual bundle draw appends exactly its successful public reply to the prepared-tuple audit. -/
theorem trace_publications (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState) (audit : Audit)
    (result : PqxdhRegistrationJointAttemptTrace.NativeResult KemSK × Audit)
    (supported : result ∈ support (trace setup codec address index owner pool audit)) :
    publications result.2 = publications audit ++ (result.1.1.1.map (fun bytes => (address, bytes))).toList := by
  rw [trace_after] at supported
  cases phase : owner.beacon.phase <;> simp only [phase] at supported
  case fresh =>
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨scalar, _, same⟩ := supported
    subst result
    exact after_publications setup codec address index owner (some scalar) pool audit
  case freshWithCoins =>
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact after_publications setup codec address index owner none pool audit
  all_goals
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    simp [publications, Audit.record]

/-- Missing and inactive owner calls publish nothing; every other successful source bundle is recorded exactly once. -/
theorem bundle_publications (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) :
    publications result.2.2 = publications state.2 ++ (result.1.map (fun bytes => (address, bytes))).toList := by
  cases found : state.1.owners[address]? with
  | none =>
    simp only [bundle, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    simp [publications, Audit.record]
  | some entry =>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, same⟩ := supported
    subst result
    exact trace_publications setup codec address entry.identityIndex entry.owner state.1.pool.1 state.2 returned member

/-- One actual source query and the existing pure registration log agree on their successful publication append. -/
theorem query_publications (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : State KemSK)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed serverIndex query).run state))
    (log : List Logged) (synced : publications state.2 = loggedPublications log) :
    publications result.2.2 = loggedPublications (record query result.1 log) := by
  rcases query with (coin | command) | read
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    exact synced
  · cases command
    case bundle address =>
      rw [bundle_publications setup codec address state result supported, synced]
      cases result.1 <;> simp [record, loggedPublications]
    all_goals
      simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨_, _, same⟩ := supported
      subst result
      simpa only [record, loggedPublications, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, List.append_nil] using synced
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    exact synced

/-- The registration log and private tuple audit remain synchronized along every actual adaptive source run, with the same full native state. -/
theorem program_publications (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : State KemSK) (log : List Logged) (synced : publications state.2 = loggedPublications log)
    (result : (Result × List Logged) × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex)
      (traceFrom program log)).run state)) :
    publications result.2.2 = loggedPublications result.1.2 := by
  induction program using OracleComp.inductionOn generalizing state log with
  | pure value =>
    simp only [traceFrom, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact synced
  | query_bind query next ih =>
    simp only [PqxdhDeploymentRegistrationTrace.traceFrom_query_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, first, rest⟩ := supported
    exact ih middle.1 middle.2 (record query middle.1 log)
      (query_publications setup codec checks serverSeed serverIndex query state middle first log synced) rest

private theorem interpreted_support {κ κ' σ Value : Type} {source : OracleSpec κ} {target : OracleSpec κ'}
    (impl : QueryImpl source (StateT σ (OracleComp target))) (program : OracleComp source Value) (state : σ)
    (result : Value × σ) (supported : result ∈ support ((simulateQ impl program).run state)) :
    result.1 ∈ support program := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, _, rest⟩ := supported
    exact (mem_support_bind_iff _ _ _).mpr
      ⟨middle.1, mem_support_query query middle.1, ih middle.1 middle.2 rest⟩

/-- Logging the actual registration queries can be coupled to the same source result and complete private audit, rather than merely an independently matching distribution. -/
theorem traced_witness (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : State KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex) program).run state)) :
    ∃ log, ((result.1, log), result.2) ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex)
      (traceFrom program [])).run state) := by
  have erased := congrArg
    (fun work => (simulateQ (handler setup codec checks serverSeed serverIndex) work).run state)
    (PqxdhDeploymentRegistrationTrace.traceFrom_erase program [])
  simp only [simulateQ_map, StateT.run_map] at erased
  rw [← erased, support_map] at supported
  obtain ⟨⟨⟨value, log⟩, after⟩, member, same⟩ := supported
  cases same
  exact ⟨log, member⟩

/-- Successful bundles of the final public transcript, read through its established registration-query projection. -/
def ledgerPublications (transcript : List PqxdhDeploymentInterface.Entry) : List (Nat × Pqxdh.Bytes) :=
  loggedPublications (PqxdhDeploymentKemTransfer.registrations transcript)

/-- In the actual compiled deployment run the private successful occurrence list equals the successful bundle replies in that identical run's final public ledger. -/
theorem compileFull_publications {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (native : PqxdhRegistrationJointSchedule.State KemSK)
    (result : ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex)
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run (native, Audit.empty))) :
    publications result.2.2 = ledgerPublications result.1.1.2.transcript := by
  obtain ⟨log, logged⟩ := traced_witness setup codec checks serverSeed serverIndex _ (native, Audit.empty) result supported
  have synchronized := program_publications setup codec checks serverSeed serverIndex _ (native, Audit.empty) [] rfl
    ((result.1, log), result.2) logged
  have sourceMember := interpreted_support (handler setup codec checks serverSeed serverIndex) _ (native, Audit.empty)
    ((result.1, log), result.2) logged
  have publicLog := PqxdhDeploymentKemTransfer.compiled_trace setup codec route bounds mode adversary (result.1, log)
    sourceMember
  change log = PqxdhDeploymentKemTransfer.registrations result.1.1.2.transcript at publicLog
  rw [publicLog] at synchronized
  exact synchronized

/-- The successful bundle view of one public transcript entry. -/
def publicationOf : PqxdhDeploymentInterface.Entry → Option (Nat × Pqxdh.Bytes)
  | ⟨.inl (.inr (.bundle address)), some bytes⟩ => some (address, bytes)
  | _ => none

private theorem publicationOf_eq_some (entry : PqxdhDeploymentInterface.Entry) (address : Nat) (bytes : Pqxdh.Bytes) :
    publicationOf entry = some (address, bytes) ↔ entry = ⟨.inl (.inr (.bundle address)), some bytes⟩ := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · simp [publicationOf]
  · cases command
    case bundle owner => cases reply <;> simp [publicationOf, Prod.mk.injEq]
    all_goals simp [publicationOf]
  · cases secrecy <;> simp [publicationOf]

/-- The established registration projection preserves exactly the actual successful bundle entries. -/
theorem ledgerPublications_eq (transcript : List PqxdhDeploymentInterface.Entry) :
    ledgerPublications transcript = transcript.filterMap publicationOf := by
  unfold ledgerPublications loggedPublications PqxdhDeploymentKemTransfer.registrations
  rw [List.filterMap_filterMap]
  congr 1
  funext entry
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · rfl
  · cases command
    case bundle owner => cases reply <;> rfl
    all_goals rfl
  · cases secrecy <;> rfl

/-- Every successful reply in the audit therefore refers to an actual bundle entry of that identical public ledger. -/
theorem mem_ledgerPublications (transcript : List PqxdhDeploymentInterface.Entry) (address : Nat) (bytes : Pqxdh.Bytes) :
    (address, bytes) ∈ ledgerPublications transcript ↔
      (⟨.inl (.inr (.bundle address)), some bytes⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript := by
  rw [ledgerPublications_eq, List.mem_filterMap]
  constructor
  · rintro ⟨entry, member, published⟩
    exact (publicationOf_eq_some entry address bytes).mp published ▸ member
  · intro member
    exact ⟨_, member, rfl⟩

/-- The first successful audited publication of an owner, read in complete source call order. -/
def firstPublication (published : List (Nat × Pqxdh.Bytes)) (address : Nat) : Option Pqxdh.Bytes :=
  published.findSome? fun entry => if entry.1 = address then some entry.2 else none

private theorem firstPublication_transcript (transcript : List PqxdhDeploymentInterface.Entry) (address : Nat) :
    firstPublication (transcript.filterMap publicationOf) address = PqxdhDeploymentTranscript.bundleOf transcript address := by
  induction transcript with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨((coin | command) | secrecy), reply⟩
    · simpa only [publicationOf, List.filterMap_cons, firstPublication, PqxdhDeploymentTranscript.bundleOf,
        List.findSome?_cons] using ih
    · cases command
      case bundle owner =>
        cases reply with
        | none =>
          change firstPublication (rest.filterMap publicationOf) address = PqxdhDeploymentTranscript.bundleOf rest address
          exact ih
        | some bytes =>
          by_cases same : owner = address
          · subst owner
            simp [publicationOf, firstPublication, PqxdhDeploymentTranscript.bundleOf]
          · simpa [publicationOf, firstPublication, PqxdhDeploymentTranscript.bundleOf, same] using ih
      all_goals
        simpa only [publicationOf, List.filterMap_cons, firstPublication, PqxdhDeploymentTranscript.bundleOf,
          List.findSome?_cons] using ih
    · cases secrecy <;>
        simpa only [publicationOf, List.filterMap_cons, firstPublication, PqxdhDeploymentTranscript.bundleOf,
          List.findSome?_cons] using ih

/-- The owner's first successful audit reply is exactly the existing public bundle lookup. -/
theorem firstPublication_ledger (transcript : List PqxdhDeploymentInterface.Entry) (address : Nat) :
    firstPublication (ledgerPublications transcript) address = PqxdhDeploymentTranscript.bundleOf transcript address := by
  rw [ledgerPublications_eq]
  exact firstPublication_transcript transcript address

/-- Every successful prepared occurrence in an actual compiled source run has its addressed publication in that same final public transcript. -/
theorem compileFull_occurrence_published {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (native : PqxdhRegistrationJointSchedule.State KemSK)
    (result : ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex)
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run (native, Audit.empty)))
    (occurrence : Occurrence) (member : occurrence ∈ result.2.2.occurrences) (bytes : Pqxdh.Bytes)
    (published : occurrence.reply = some bytes) :
    (⟨.inl (.inr (.bundle occurrence.ownerAddress)), some bytes⟩ : PqxdhDeploymentInterface.Entry) ∈
      result.1.1.2.transcript := by
  have logged : (occurrence.ownerAddress, bytes) ∈ publications result.2.2 := by
    apply List.mem_filterMap.mpr
    exact ⟨occurrence, member, by rw [published]; rfl⟩
  rw [compileFull_publications setup codec checks serverSeed serverIndex route bounds mode adversary native result supported,
    mem_ledgerPublications] at logged
  exact logged

/-- First-success lookup of the actual prepared audit is exactly the final deployment ledger's bundle lookup, with no caller-assumed audit/ledger relation. -/
theorem compileFull_bundleOf {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (native : PqxdhRegistrationJointSchedule.State KemSK)
    (result : ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex)
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run (native, Audit.empty)))
    (address : Nat) :
    PqxdhDeploymentTranscript.bundleOf result.1.1.2.transcript address =
      firstPublication (publications result.2.2) address := by
  rw [compileFull_publications setup codec checks serverSeed serverIndex route bounds mode adversary native result supported]
  exact (firstPublication_ledger _ address).symm

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.trace_publications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.trace_publications

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.bundle_publications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.bundle_publications

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.query_publications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.query_publications

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.program_publications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.program_publications

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.traced_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.traced_witness

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.compileFull_publications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.compileFull_publications

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.ledgerPublications_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.ledgerPublications_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.mem_ledgerPublications' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.mem_ledgerPublications

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.firstPublication_ledger' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.firstPublication_ledger

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.compileFull_occurrence_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.compileFull_occurrence_published

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.compileFull_bundleOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger.compileFull_bundleOf
