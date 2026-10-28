-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditWritten

/-! Actual source publication consumes an owner's Fresh phase. Later failures, finishes, disclosures and source commands never restore it, and constructor append cannot reuse an existing address. Consequently every successful prepared occurrence is the owner's unique final published tuple, without a no-failed-bundle or externally supplied keys law. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppressionTrace
open PqxdhDeploymentEligibility (phaseClass)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- A published owner remains present and has left both Fresh representations. -/
def Nonfresh (state : PqxdhRegistrationJointSchedule.State KemSK) (address : Nat) : Prop :=
  ∃ entry, state.owners[address]? = some entry ∧ phaseClass entry.owner.beacon.phase ≠ .fresh

private theorem trace_stopped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (closed : phaseClass owner.beacon.phase ≠ .fresh) :
    PqxdhRegistrationJointBundle.trace setup codec index owner pool = pure ((none, owner), pool) := by
  cases phase : owner.beacon.phase <;> simp_all [PqxdhRegistrationJointBundle.trace, phaseClass]

private theorem trace_success (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (result : PqxdhRegistrationJointAttemptTrace.NativeResult KemSK)
    (supported : result ∈ support (PqxdhRegistrationJointBundle.trace setup codec index owner pool))
    (bytes : Pqxdh.Bytes) (published : result.1.1 = some bytes) :
    phaseClass owner.beacon.phase = .fresh ∧ phaseClass result.1.2.beacon.phase = .initSent := by
  rcases PqxdhDeploymentSigningHistory.trace_cases setup codec index owner pool result supported with same |
    ⟨_, _, fresh, failed | ⟨_, _, _, _, phase⟩⟩
  · rw [same] at published
    cases published
  · rw [failed] at published
    cases published
  · exact ⟨fresh, phase⟩

private theorem native_finish_nonfresh {Aux : Type} (_setup : Setup baseSpec KemSK)
    (impl : QueryImpl (PqxdhRegistrationJointFinish.NativeSpec KemSK Response) (StateT Aux ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (before : Aux) (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × Aux)
    (supported : result ∈ support ((simulateQ impl (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run before))
    (closed : phaseClass owner.beacon.phase ≠ .fresh) : phaseClass result.1.2.beacon.phase ≠ .fresh := by
  rcases result with ⟨⟨_ | bytes, after⟩, final⟩
  · have failure := PqxdhBeaconPhase2Publication.native_failure impl decode raw owner after before final supported
    cases phase : owner.beacon.phase <;> simp only [phase] at failure closed <;>
      simp_all [phaseClass, PqxdhBeaconPhase2Preparation.abort]
  · obtain ⟨staged, _, _, published⟩ :=
      PqxdhBeaconPhase2Publication.native_success impl decode raw bytes owner after before final supported
    rw [← congrArg Prod.snd published]
    simp [PqxdhBeaconPhase2Publication.publish, phaseClass]

/-- A source bundle cannot restore an owner that has left Fresh. -/
theorem bundle_nonfresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (called address : Nat)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (before : Nonfresh state address)
    (result : Option Pqxdh.Bytes × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointSchedule.bundle setup codec called).run state)) :
    Nonfresh result.2 address := by
  obtain ⟨old, oldFound, closed⟩ := before
  cases found : state.owners[called]? with
  | none =>
    simp only [PqxdhRegistrationJointSchedule.bundle, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨old, oldFound, closed⟩
  | some entry =>
    simp only [PqxdhRegistrationJointSchedule.bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, same⟩ := supported
    subst result
    by_cases sameAddress : called = address
    · subst called
      have sameOwner : entry = old := Option.some.inj (found.symm.trans oldFound)
      subst old
      rw [trace_stopped setup codec entry.identityIndex entry.owner state.pool.1 closed] at member
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst returned
      refine ⟨entry, ?_, closed⟩
      exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1
    · refine ⟨old, ?_, closed⟩
      rw [List.getElem?_set_ne sameAddress]
      exact oldFound

/-- A source finish terminally aborts active Phase 2 or installs Established, and cannot restore Fresh. -/
theorem finish_nonfresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (called address : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (before : Nonfresh state address)
    (result : Option Pqxdh.Bytes × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointSchedule.finish setup codec called raw).run state)) :
    Nonfresh result.2 address := by
  obtain ⟨old, oldFound, closed⟩ := before
  cases found : state.owners[called]? with
  | none =>
    simp only [PqxdhRegistrationJointSchedule.finish, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨old, oldFound, closed⟩
  | some entry =>
    simp only [PqxdhRegistrationJointSchedule.finish, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, same⟩ := supported
    subst result
    by_cases sameAddress : called = address
    · subst called
      have sameOwner : entry = old := Option.some.inj (found.symm.trans oldFound)
      subst old
      refine ⟨{ entry with owner := returned.1.2 }, ?_, ?_⟩
      · exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1
      · exact native_finish_nonfresh setup _ codec.frameRead raw entry.owner (state.pool, state.shared) returned member closed
    · refine ⟨old, ?_, closed⟩
      rw [List.getElem?_set_ne sameAddress]
      exact oldFound

/-- Every actual source request preserves an already published owner's nonfresh phase, including new constructors and current-field disclosures. -/
theorem query_nonfresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (address : Nat) (before : Nonfresh state address)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run state)) :
    Nonfresh result.2 address := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case create pin keyId =>
      obtain ⟨old, oldFound, closed⟩ := before
      simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
        PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.create,
        StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨material, _, same⟩ := supported
      subst result
      refine ⟨old, ?_, closed⟩
      dsimp only [PqxdhRegistrationJointSchedule.created]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp oldFound).1]
      exact oldFound
    case bundle called => exact bundle_nonfresh setup codec called address state before result supported
    case finish called raw => exact finish_nonfresh setup codec called address raw state before result supported
    all_goals
      obtain ⟨old, oldFound, closed⟩ := before
      refine ⟨old, ?_, closed⟩
      rw [(PqxdhDeploymentSigningHistory.quiet_step setup codec checks seed serverIndex _ rfl state result supported).owners]
      exact oldFound
  all_goals
    obtain ⟨old, oldFound, closed⟩ := before
    refine ⟨old, ?_, closed⟩
    rw [(PqxdhDeploymentSigningHistory.quiet_step setup codec checks seed serverIndex _ rfl state result supported).owners]
    exact oldFound

/-- Every successful audited source bundle starts Fresh and leaves its addressed owner present in InitSent. -/
theorem bundle_publication_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state))
    (bytes : Pqxdh.Bytes) (published : result.1 = some bytes) :
    (∃ entry, state.1.owners[address]? = some entry ∧ phaseClass entry.owner.beacon.phase = .fresh) ∧
      Nonfresh result.2.1 address := by
  cases found : state.1.owners[address]? with
  | none =>
    simp only [bundle, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    cases published
  | some entry =>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, same⟩ := supported
    subst result
    have original : returned.1 ∈ support (PqxdhRegistrationJointBundle.trace setup codec entry.identityIndex
        entry.owner state.1.pool.1) := by
      rw [← trace_source setup codec address entry.identityIndex entry.owner state.1.pool.1 state.2, support_map]
      exact ⟨returned, member, rfl⟩
    obtain ⟨fresh, afterPhase⟩ := trace_success setup codec entry.identityIndex entry.owner state.1.pool.1
      returned.1 original bytes published
    refine ⟨⟨entry, rfl, fresh⟩, { entry with owner := returned.1.1.2 }, ?_, ?_⟩
    · exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1
    · rw [afterPhase]
      decide

/-- Every owner with a successful occurrence still exists and cannot make a later successful bundle. -/
def Completed (state : State KemSK) : Prop :=
  ∀ occurrence ∈ state.2.occurrences, ∀ bytes, occurrence.reply = some bytes → Nonfresh state.1 occurrence.ownerAddress

/-- Source publication establishes nonfreshness for the new receipt and preserves it for every older receipt. -/
theorem bundle_completed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (held : Completed state) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) : Completed result.2 := by
  have shape := fun bytes published =>
    (bundle_publication_shape setup codec address state result supported bytes published).2
  have original : (result.1, result.2.1) ∈ support
      ((PqxdhRegistrationJointSchedule.bundle setup codec address).run state.1) := by
    rw [← bundle_source setup codec address state, support_map]
    exact ⟨result, supported, rfl⟩
  cases found : state.1.owners[address]? with
  | none =>
    simp only [bundle, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    simpa only [Completed, Audit.record, List.map_nil, List.append_nil] using held
  | some entry =>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, same⟩ := supported
    subst result
    obtain ⟨tuples, _, recorded⟩ := PqxdhDeploymentPublicationAuditBounds.trace_record setup codec address
      entry.identityIndex entry.owner state.1.pool.1 state.2 returned member
    intro occurrence occurred bytes published
    change occurrence ∈ returned.2.occurrences at occurred
    rw [recorded] at occurred
    rcases List.mem_append.mp occurred with old | added
    · exact bundle_nonfresh setup codec address occurrence.ownerAddress state.1
        (held occurrence old bytes published) _ original
    · obtain ⟨_, _, equal⟩ := List.mem_map.mp added
      subst occurrence
      exact shape bytes published

/-- All actual commands preserve the post-publication lifecycle fact of every receipt. -/
theorem query_completed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (held : Completed state)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks seed serverIndex query).run state)) :
    Completed result.2 := by
  have original : (result.1, result.2.1) ∈ support
      ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run state.1) := by
    rw [← query_source setup codec checks seed serverIndex query state, support_map]
    exact ⟨result, supported, rfl⟩
  have preserved : ∀ audit : Audit, audit.occurrences = state.2.occurrences → Completed (result.2.1, audit) := by
    intro audit same occurrence member bytes published
    rw [same] at member
    exact query_nonfresh setup codec checks seed serverIndex query state.1 occurrence.ownerAddress
      (held occurrence member bytes published) _ original
  rcases query with (coin | request) | read
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    exact preserved state.2 rfl
  · cases request
    case bundle address => exact bundle_completed setup codec address state held result supported
    all_goals
      simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨_, _, same⟩ := supported
      subst result
      exact preserved state.2 rfl
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    exact preserved state.2 rfl

/-- Successful source publication addresses are unique in chronological order. -/
def Unique (audit : Audit) : Prop :=
  (PqxdhDeploymentPublicationAuditLedger.publications audit).map Prod.fst |>.Nodup

/-- A successful new bundle cannot reuse any owner address already published in the source audit. -/
theorem bundle_unique (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (completed : Completed state) (held : Unique state.2)
    (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) : Unique result.2.2 := by
  unfold Unique at held ⊢
  rw [PqxdhDeploymentPublicationAuditLedger.bundle_publications setup codec address state result supported]
  cases published : result.1 with
  | none => simpa only [Option.map_none, Option.toList_none, List.append_nil] using held
  | some bytes =>
    have absent : address ∉ (PqxdhDeploymentPublicationAuditLedger.publications state.2).map Prod.fst := by
      intro previous
      obtain ⟨⟨oldAddress, oldBytes⟩, member, same⟩ := List.mem_map.mp previous
      change oldAddress = address at same
      subst oldAddress
      obtain ⟨occurrence, occurred, observation⟩ := List.mem_filterMap.mp member
      obtain ⟨value, oldReply, samePair⟩ := Option.map_eq_some_iff.mp observation
      have closed := completed occurrence occurred value oldReply
      have sameAddress : occurrence.ownerAddress = address := congrArg Prod.fst samePair
      rw [sameAddress] at closed
      obtain ⟨entry, found, notFresh⟩ := closed
      obtain ⟨other, otherFound, fresh⟩ := (bundle_publication_shape setup codec address state result supported bytes published).1
      have sameOwner := Option.some.inj (found.symm.trans otherFound)
      subst other
      exact notFresh fresh
    simp only [Option.map_some, Option.toList_some, List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨held, by simp, ?_⟩
    intro left member right singleton same
    have rightAddress := List.mem_singleton.mp singleton
    rw [rightAddress] at same
    exact absent (same ▸ member)


/-- Every actual command preserves uniqueness of successful source owner publications. -/
theorem query_unique (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (completed : Completed state) (held : Unique state.2)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks seed serverIndex query).run state)) :
    Unique result.2.2 := by
  rcases query with (coin | request) | read
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    exact held
  · cases request
    case bundle address => exact bundle_unique setup codec address state completed held result supported
    all_goals
      simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨_, _, same⟩ := supported
      subst result
      exact held
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    exact held

/-- The full adaptive source scheduler retains completed-owner lifecycle facts and publication uniqueness together. -/
theorem program_unique (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : State KemSK) (completed : Completed state) (held : Unique state.2) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks seed serverIndex) program).run state)) :
    Completed result.2 ∧ Unique result.2.2 := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query _ (fun current => Completed current ∧ Unique current.2)
    (fun query before valid after member =>
      ⟨query_completed setup codec checks seed serverIndex query before valid.1 after member,
        query_unique setup codec checks seed serverIndex query before valid.1 valid.2 after member⟩)
    program state ⟨completed, held⟩ result supported

/-- Every actual compiled deployment has at most one successful bundle publication per owner, including arbitrary failed Fresh attempts. -/
theorem compileFull_unique {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (serverIndex : Nat)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (native : PqxdhRegistrationJointSchedule.State KemSK)
    (result : ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks seed serverIndex)
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run (native, Audit.empty))) :
    Completed result.2 ∧ Unique result.2.2 := by
  exact program_unique setup codec checks seed serverIndex _ (native, Audit.empty)
    (by simp [Completed, Audit.empty])
    (by simp [Unique, PqxdhDeploymentPublicationAuditLedger.publications, Audit.empty]) result supported

private theorem firstPublication_of_mem (published : List (Nat × Pqxdh.Bytes))
    (unique : (published.map Prod.fst).Nodup) (address : Nat) (bytes : Pqxdh.Bytes)
    (member : (address, bytes) ∈ published) :
    PqxdhDeploymentPublicationAuditLedger.firstPublication published address = some bytes := by
  induction published with
  | nil => simp only [List.not_mem_nil] at member
  | cons first rest ih =>
    rcases first with ⟨firstAddress, firstBytes⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | later
    · cases same
      simp [PqxdhDeploymentPublicationAuditLedger.firstPublication]
    · have different : firstAddress ≠ address := by
        intro sameAddress
        exact unique.1 (List.mem_map.mpr ⟨(address, bytes), later, sameAddress.symm⟩)
      simp only [PqxdhDeploymentPublicationAuditLedger.firstPublication, List.findSome?_cons,
        different, ite_false]
      exact ih unique.2 later

/-- A successful source occurrence is its owner's first publication because actual owner addresses cannot publish twice. -/
theorem occurrence_lookup (audit : Audit) (unique : Unique audit)
    (occurrence : Occurrence) (member : occurrence ∈ audit.occurrences) (bytes : Pqxdh.Bytes)
    (published : occurrence.reply = some bytes) :
    PqxdhDeploymentPublicationAuditLedger.firstPublication
      (PqxdhDeploymentPublicationAuditLedger.publications audit) occurrence.ownerAddress = some bytes := by
  apply firstPublication_of_mem _ unique
  exact List.mem_filterMap.mpr ⟨occurrence, member, by rw [published]; rfl⟩

/-- Every successful actual occurrence is exactly the final public bundle bytes at its original owner address. -/
theorem compileFull_occurrence_bundleOf {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (serverIndex : Nat)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (native : PqxdhRegistrationJointSchedule.State KemSK)
    (result : ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks seed serverIndex)
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run (native, Audit.empty)))
    (occurrence : Occurrence) (member : occurrence ∈ result.2.2.occurrences) (bytes : Pqxdh.Bytes)
    (published : occurrence.reply = some bytes) :
    PqxdhDeploymentTranscript.bundleOf result.1.1.2.transcript occurrence.ownerAddress = some bytes := by
  rw [PqxdhDeploymentPublicationAuditLedger.compileFull_bundleOf setup codec checks seed serverIndex route bounds mode
    adversary native result supported]
  exact occurrence_lookup _ (compileFull_unique setup codec checks seed serverIndex route bounds mode adversary
    native result supported).2 occurrence member bytes published

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentPublicationSuppressionTrace (Occurrence)
open PqxdhDeploymentPublicationAuditUnique
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- Actual initialized publication consumes Fresh permanently, discharging successful-owner uniqueness from the source constructor. -/
theorem actual_unique (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime)) :
    Completed outcome.2.2 ∧ Unique outcome.2.2.2 := by
  simp only [actual, initialized, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨(_ | created), born⟩, _, continued⟩ := supported
  · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  · simp only [support_map, Set.mem_image] at continued
    obtain ⟨executed, member, equal⟩ := continued
    have same : outcome = (PqxdhRegistrationJointServerBirth.encode created, executed.1, executed.2) :=
      (Option.some.inj (congrArg Prod.fst equal)).symm
    rw [same]
    exact compileFull_unique setup codec checks created.seed created.server.server.metadata.identityIndex route
      bounds mode adversary _ executed member

/-- Every successful occurrence of the actual initialized run is that owner's final unique bundle lookup. -/
theorem actual_occurrence_bundleOf (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime))
    (occurrence : Occurrence) (member : occurrence ∈ outcome.2.2.2.occurrences) (bytes : Pqxdh.Bytes)
    (published : occurrence.reply = some bytes) :
    PqxdhDeploymentTranscript.bundleOf outcome.2.1.1.2.transcript occurrence.ownerAddress = some bytes := by
  rw [actual_bundleOf setup codec checks route ensureInit bounds mode adversary runtime outcome after supported]
  exact occurrence_lookup _ (actual_unique setup codec checks route ensureInit bounds mode adversary runtime
    outcome after supported).2 occurrence member bytes published

/-- Every successful actual source occurrence carries exactly the key tuple of its final unique public bundle, with no cleanliness or supplied keys law. -/
theorem actual_occurrence_publishedTuple (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime))
    (occurrence : Occurrence) (member : occurrence ∈ outcome.2.2.2.occurrences) (bytes : Pqxdh.Bytes)
    (published : occurrence.reply = some bytes) :
    PqxdhDeploymentPublishedTuple.publishedTuple codec outcome.2.1.1.2.transcript occurrence.ownerAddress =
      some occurrence.keys := by
  unfold PqxdhDeploymentPublishedTuple.publishedTuple
  rw [actual_occurrence_bundleOf setup codec checks route ensureInit bounds mode adversary runtime outcome after supported
    occurrence member bytes published, Option.bind_some]
  exact actual_occurrence_tuple setup codec checks phase1 route ensureInit bounds mode adversary runtime outcome after
    supported occurrence member bytes published

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.bundle_nonfresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.bundle_nonfresh

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.finish_nonfresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.finish_nonfresh

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.query_nonfresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.query_nonfresh

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.bundle_publication_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.bundle_publication_shape

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.bundle_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.bundle_completed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.query_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.query_completed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.bundle_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.bundle_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.query_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.query_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.program_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.program_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.compileFull_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.compileFull_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.occurrence_lookup' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.occurrence_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.compileFull_occurrence_bundleOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique.compileFull_occurrence_bundleOf

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_bundleOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_bundleOf

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_publishedTuple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_publishedTuple
