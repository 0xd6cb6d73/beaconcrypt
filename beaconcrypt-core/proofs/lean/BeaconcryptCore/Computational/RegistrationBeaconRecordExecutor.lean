-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationRecordPrimitives
import BeaconcryptCore.Refinement.RegistrationReachability
import VCVio.OracleComp.CanReturn

/-!
The Beacon's actual initial-record controller retains its source agreement while following initial HKDF, receive HKDF, shared commitment and AEAD phases. Recursion follows the source continuation rank. Hash absence or mismatch resumes the actual rejection continuation before any AEAD query, and only the actual final source admission returns a CompletedBeacon with its consumed receive kernel.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor

open RegistrationRecordPrimitives (Spec)

abbrev Result := core.result.Result registration.CompletedBeacon pqxdh.BeaconAborted

def rank : registration.BeaconInitialOpen → Nat
  | .KdfRequested pending => pending.pending.pending.remaining.val + 3
  | .CommitmentRequested _ => 2
  | .AeadRequested _ => 1

theorem kdf_rank (pending : registration.BeaconRecordKdf)
    (reply : core.option.Option ratchet.RatchetKdfResponse) (next : registration.BeaconInitialOpen)
    (actual : pending.resume reply = .ok (.Ok next)) : rank next < rank (.KdfRequested pending) := by
  cases reply with
  | none =>
      simp [registration.BeaconRecordKdf.resume, pqxdh.beacon_abort_candidate] at actual
  | some response =>
      obtain ⟨effect, resumed, progress⟩ := pending.pending.pending.resume_progress response
      simp only [registration.BeaconRecordKdf.resume, record_effects.RecordReceiveKdf.resume,
        resumed, bind_tc_ok] at actual
      cases effect with
      | ReceiveRejected kernel context =>
          simp [record_effects.normalize_receive, registration.normalize_beacon_open,
            pqxdh.beacon_abort_candidate] at actual
      | ReceiveKdfRequested later =>
          have nextSame : .KdfRequested ⟨pending.agreement, ⟨later⟩⟩ = next := by
            simpa only [record_effects.normalize_receive, registration.normalize_beacon_open,
              bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] using actual
          cases nextSame
          exact Nat.add_lt_add_right progress.2 3
      | ReceiveOpenRequested opening =>
          cases opened : record.begin_open opening with
          | ok value =>
              cases value with
              | OpenRejected kernel =>
                  simp [record_effects.normalize_receive, opened, registration.normalize_beacon_open,
                    pqxdh.beacon_abort_candidate] at actual
              | OpenCommitmentRequested selected =>
                  have nextSame : .CommitmentRequested ⟨pending.agreement, ⟨selected⟩⟩ = next := by
                    simpa only [record_effects.normalize_receive, opened, registration.normalize_beacon_open,
                      bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] using actual
                  cases nextSame
                  simp only [rank]
                  omega
          | fail error => simp [record_effects.normalize_receive, opened] at actual
          | div => simp [record_effects.normalize_receive, opened] at actual

theorem commitment_rank (pending : registration.BeaconRecordCommitment) (matched : Bool)
    (next : registration.BeaconInitialOpen) (actual : pending.resume matched = .ok (.Ok next)) :
    rank next < rank (.CommitmentRequested pending) := by
  cases matched
  · simp [registration.BeaconRecordCommitment.resume, record_effects.RecordReceiveCommitment.resume,
      record.OpenCommitment.resume, ratchet.concrete.ReceiveOpen.reject,
      registration.normalize_beacon_open, pqxdh.beacon_abort_candidate] at actual
  · have nextSame : .AeadRequested ⟨pending.agreement, ⟨⟨pending.pending.pending.opening⟩⟩⟩ = next := by
      simpa only [registration.BeaconRecordCommitment.resume, record_effects.RecordReceiveCommitment.resume,
        record.OpenCommitment.resume, registration.normalize_beacon_open, bind_tc_ok,
        ite_true, RustM.ok.injEq, core.result.Result.Ok.injEq] using actual
    cases nextSame
    simp only [rank]
    decide

def continueWith {Input : Type} (result : RustM Input) (next : Input → OracleComp Spec (RustM Result)) :
    OracleComp Spec (RustM Result) :=
  match result with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def commitmentMatches (computed : core.option.Option (Std.Array Std.U8 64#usize))
    (supplied : Std.Array Std.U8 64#usize) : Bool :=
  match computed with
  | .None => false
  | .Some digest => decide (absBytes digest = absBytes supplied)

def program (phase : registration.BeaconInitialOpen) : OracleComp Spec (RustM Result) :=
  match phase with
  | .KdfRequested pending =>
      continueWith pending.request fun request => do
        let reply ← Spec.query (.ratchetKdf request)
        match _actual : pending.resume reply with
        | .ok (.Ok next) => program next
        | .ok (.Err aborted) => pure (.ok (.Err aborted))
        | .fail error => pure (.fail error)
        | .div => pure .div
  | .CommitmentRequested pending =>
      continueWith pending.transcript fun transcript => do
        let digest ← Spec.query (.hash transcript)
        continueWith pending.supplied_commitment fun supplied =>
          match _actual : pending.resume (commitmentMatches digest supplied) with
          | .ok (.Ok next) => program next
          | .ok (.Err aborted) => pure (.ok (.Err aborted))
          | .fail error => pure (.fail error)
          | .div => pure .div
  | .AeadRequested pending =>
      continueWith pending.request fun request =>
        match request with
        | .None => pure (pending.finish .None)
        | .Some request => do
            let plaintext ← Spec.query (.openAead request)
            pure (pending.finish plaintext)
termination_by rank phase
decreasing_by
  · exact kdf_rank _ _ _ _actual
  · exact commitment_rank _ _ _ _actual

def fromInitial (pending : registration.BeaconInitialKdf) : OracleComp Spec (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← Spec.query (.initialKdf request)
    match pending.resume reply with
    | .ok (.Ok next) => program next
    | .ok (.Err aborted) => pure (.ok (.Err aborted))
    | .fail error => pure (.fail error)
    | .div => pure .div

def begin (agreement : agreement.BeaconAgreement) : OracleComp Spec (RustM Result) :=
  continueWith (registration.begin_beacon_completion agreement) fromInitial

noncomputable def execute {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (agreement : agreement.BeaconAgreement) :=
  simulateQ (RegistrationRecordPrimitives.implementation (Auxiliary := Auxiliary) source writer) (begin agreement)

private theorem continueWith_support {Input : Type} (result : RustM Input)
    (next : Input → OracleComp Spec (RustM Result)) (completed : registration.CompletedBeacon)
    (supported : .ok (.Ok completed) ∈ support (continueWith result next)) :
    ∃ value, result = .ok value ∧ .ok (.Ok completed) ∈ support (next value) := by
  cases result <;> simp_all [continueWith]

private theorem resume_support
    (result : RustM (core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted))
    (completed : registration.CompletedBeacon)
    (supported : .ok (.Ok completed) ∈ support (match _actual : result with
      | .ok (.Ok next) => program next
      | .ok (.Err aborted) => pure (.ok (.Err aborted))
      | .fail error => pure (.fail error)
      | .div => pure .div)) :
    ∃ next, result = .ok (.Ok next) ∧ .ok (.Ok completed) ∈ support (program next) := by
  cases result with
  | ok value => cases value <;> simp_all
  | fail error => simp_all
  | div => simp_all

/-- Every successful interpreted phase reaches an actual source-owned AEAD admission and its actual optional plaintext reply. -/
theorem program_reaches (initial : registration.BeaconInitialKdf) (phase : registration.BeaconInitialOpen)
    (completed : registration.CompletedBeacon)
    (reached : BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial phase)
    (supported : .ok (.Ok completed) ∈ support (program phase)) :
    ∃ (pending : registration.BeaconRecordAead) (plaintext : core.option.Option (Slice Std.U8)),
      BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial (.AeadRequested pending) ∧
      pending.finish plaintext = .ok (.Ok completed) := by
  cases phaseShape : phase with
  | KdfRequested pending =>
      rw [program.eq_def, phaseShape] at supported
      rw [phaseShape] at reached
      obtain ⟨request, _, called⟩ := continueWith_support _ _ completed supported
      simp only [mem_support_bind_iff] at called
      obtain ⟨reply, _, continued⟩ := called
      obtain ⟨next, actual, continued⟩ := resume_support (pending.resume reply) completed continued
      exact program_reaches initial next completed (.kdf pending reply next reached actual) continued
  | CommitmentRequested pending =>
      rw [program.eq_def, phaseShape] at supported
      rw [phaseShape] at reached
      obtain ⟨transcript, _, called⟩ := continueWith_support _ _ completed supported
      simp only [mem_support_bind_iff] at called
      obtain ⟨digest, _, continued⟩ := called
      obtain ⟨supplied, _, continued⟩ := continueWith_support _ _ completed continued
      obtain ⟨next, actual, continued⟩ := resume_support (pending.resume (commitmentMatches digest supplied))
        completed continued
      exact program_reaches initial next completed
        (.commitment pending (commitmentMatches digest supplied) next reached actual) continued
  | AeadRequested pending =>
      rw [program.eq_def, phaseShape] at supported
      rw [phaseShape] at reached
      obtain ⟨request, _, called⟩ := continueWith_support _ _ completed supported
      cases request with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at called
          exact ⟨pending, .None, reached, called.symm⟩
      | some request =>
          simp only [mem_support_bind_iff] at called
          obtain ⟨reply, _, returned⟩ := called
          simp only [support_pure, Set.mem_singleton_iff] at returned
          exact ⟨pending, reply, reached, returned.symm⟩
termination_by rank phase
decreasing_by
  · simpa only [phaseShape] using kdf_rank _ _ _ actual
  · simpa only [phaseShape] using commitment_rank _ _ _ actual

theorem fromInitial_reaches (initial : registration.BeaconInitialKdf) (completed : registration.CompletedBeacon)
    (supported : .ok (.Ok completed) ∈ support (fromInitial initial)) :
    ∃ (pending : registration.BeaconRecordAead) (plaintext : core.option.Option (Slice Std.U8)),
      BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial (.AeadRequested pending) ∧
      pending.finish plaintext = .ok (.Ok completed) := by
  obtain ⟨request, _, called⟩ := continueWith_support _ _ completed supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨reply, _, continued⟩ := called
  cases actual : initial.resume reply with
  | ok value =>
      cases value with
      | Err aborted => simp [actual] at continued
      | Ok next =>
          simp only [actual] at continued
          exact program_reaches initial next completed (.start reply next actual) continued
  | fail error => simp [actual] at continued
  | div => simp [actual] at continued

theorem execute_reaches {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (agreement : agreement.BeaconAgreement)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (completed : registration.CompletedBeacon)
    (supported : (.ok (.Ok completed), after) ∈ support ((execute source writer agreement).run before)) :
    ∃ (initial : registration.BeaconInitialKdf) (pending : registration.BeaconRecordAead)
      (plaintext : core.option.Option (Slice Std.U8)),
      registration.begin_beacon_completion agreement = .ok initial ∧
      BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial (.AeadRequested pending) ∧
      pending.finish plaintext = .ok (.Ok completed) := by
  have native : .ok (.Ok completed) ∈ support (begin agreement) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationRecordPrimitives.implementation source writer) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  obtain ⟨initial, started, continued⟩ := continueWith_support _ _ completed native
  obtain ⟨pending, plaintext, reached, finished⟩ := fromInitial_reaches initial completed continued
  exact ⟨initial, pending, plaintext, started, reached, finished⟩

/-- Native completion retains the actual agreement supplied by the authenticated response and key-agreement controller. -/
theorem initial_agreement (agreement : agreement.BeaconAgreement) (initial : registration.BeaconInitialKdf)
    (actual : registration.begin_beacon_completion agreement = .ok initial) : initial.agreement = agreement := by
  obtain ⟨pending, pendingRun⟩ :=
    BeaconcryptCore.PanicFreedom.Structural.pqxdh_concrete_start_beacon_candidate_ratchet_kdf_total
      agreement.candidate agreement.root.bytes
  have expected : registration.begin_beacon_completion agreement = .ok ⟨agreement, pending⟩ := by
    simp only [registration.begin_beacon_completion, ratchet.RatchetChain.as_bytes, pendingRun, bind_tc_ok]
  have same : (⟨agreement, pending⟩ : registration.BeaconInitialKdf) = initial :=
    RustM.ok.inj (expected.symm.trans actual)
  cases same
  rfl

/-- Actual success publishes the kernel of the completed sequence-one receive, the retained populated binding and precisely the admitted application suffix. -/
theorem execute_consumed {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (agreement : agreement.BeaconAgreement)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (completed : registration.CompletedBeacon)
    (supported : (.ok (.Ok completed), after) ∈ support ((execute source writer agreement).run before)) :
    completed.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
        agreement.binding agreement.candidate.assigned_key_id ∧
      ∃ (pending : registration.BeaconRecordAead) (plaintext : Slice Std.U8),
        pending.agreement = agreement ∧
        pending.pending.finish (.Some plaintext) = .ok (completed.kernel,
          .Some (⟨plaintext, agreement.candidate.server_binding.identity_key_id, 1#u64⟩ :
            record.OpenedRecord (Slice Std.U8))) ∧
        completed.application = plaintext.drop 8#usize := by
  obtain ⟨initial, pending, plaintext, started, reached, finished⟩ :=
    execute_reaches source writer agreement before after completed supported
  obtain ⟨kernel, own, specification⟩ :=
    BeaconcryptCore.Refinement.RegistrationReachability.reachable_completion initial pending plaintext reached
  have sameAgreement : pending.agreement = agreement := own.trans (initial_agreement agreement initial started)
  have admitted := specification.2.2
  rw [finished] at admitted
  cases plaintext with
  | none => simp at admitted
  | some bytes =>
      simp only [RustM.ok.injEq] at admitted
      change core.result.Result.Ok completed =
        (if 8 < bytes.val.length ∧ (bytes.val.take 8).map absByte =
            Pqxdh.LE64 pending.agreement.candidate.assigned_key_id.val
          then .Ok (BeaconcryptCore.Refinement.RegistrationRecords.completedBeacon pending kernel bytes)
          else .Err (⟨pending.agreement.candidate.server_binding.identity_key_id⟩ : pqxdh.BeaconAborted)) at admitted
      split at admitted
      · have same : completed = BeaconcryptCore.Refinement.RegistrationRecords.completedBeacon pending kernel bytes := by
          simpa using admitted
        rw [same]
        refine ⟨?_, pending, bytes, sameAgreement, ?_, rfl⟩
        · simp only [BeaconcryptCore.Refinement.RegistrationRecords.completedBeacon, sameAgreement]
        · simpa only [BeaconcryptCore.Refinement.RegistrationRecords.completedBeacon, sameAgreement] using specification.2.1
      · simp at admitted

end BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.kdf_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.kdf_rank
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.commitment_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.commitment_rank
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.program_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.program_reaches
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.fromInitial_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.fromInitial_reaches
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.execute_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.execute_reaches
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.initial_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.initial_agreement
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.execute_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor.execute_consumed
