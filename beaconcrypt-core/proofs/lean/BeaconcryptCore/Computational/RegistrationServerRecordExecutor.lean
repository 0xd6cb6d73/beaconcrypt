-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationRecordPrimitives
import BeaconcryptCore.Refinement.RegistrationRecords

/-!
The first Server record follows the actual extracted completion, initial KDF, ratchet KDF, detached seal, shared commitment and raw-write continuations. A successful result is the source ServerResponseHash capability, including its advanced kernel and retained binding; it is ready for the existing response-hash/sign/publication controller. No freshly reset kernel is installed. The open primitive interface retains every optional failure and the enclosing stateful interpretation retains every reached primitive effect.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationServerRecordExecutor

open RegistrationRecordPrimitives (Spec)
open BeaconcryptCore.Refinement.RegistrationRecords

abbrev Result := core.result.Result registration.ServerResponseHash pqxdh.ServerState

def continueWith {Input : Type} (result : RustM Input) (next : Input → OracleComp Spec (RustM Result)) :
    OracleComp Spec (RustM Result) :=
  match result with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def continueResult {Input : Type} (result : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp Spec (RustM Result)) : OracleComp Spec (RustM Result) :=
  match result with
  | .ok (.Ok value) => next value
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

def fromWrite (pending : registration.ServerRecordWrite) : OracleComp Spec (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← Spec.query (.write request)
    pure (pending.resume reply)

def fromCommitment (pending : registration.ServerRecordCommitment) : OracleComp Spec (RustM Result) :=
  continueWith pending.transcript fun transcript => do
    let reply ← Spec.query (.hash transcript)
    continueResult (pending.resume reply) fromWrite

def fromAead (pending : registration.ServerRecordAead) : OracleComp Spec (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← Spec.query (.seal request)
    continueResult (pending.resume reply) fromCommitment

def fromRatchet (pending : registration.ServerInitialSeal) : OracleComp Spec (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← Spec.query (.ratchetKdf request)
    continueResult (pending.resume reply) fromAead

def fromInitial (pending : registration.ServerInitialKdf) : OracleComp Spec (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← Spec.query (.initialKdf request)
    continueResult (pending.resume reply) fromRatchet

/-- The actual full current-pin comparison and native allocation gate run before any primitive callback. -/
def begin (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8) :
    OracleComp Spec (RustM Result) :=
  continueResult (registration.begin_server_completion control current availability agreement application) fromInitial

noncomputable def execute {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8) :=
  simulateQ (RegistrationRecordPrimitives.implementation (Auxiliary := Auxiliary) source writer)
    (begin control current availability agreement application)

private theorem continueWith_support {Input : Type} (result : RustM Input)
    (next : Input → OracleComp Spec (RustM Result)) (completed : registration.ServerResponseHash)
    (supported : .ok (.Ok completed) ∈ support (continueWith result next)) :
    ∃ value, result = .ok value ∧ .ok (.Ok completed) ∈ support (next value) := by
  cases result <;> simp_all [continueWith]

private theorem continueResult_support {Input : Type} (result : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp Spec (RustM Result)) (completed : registration.ServerResponseHash)
    (supported : .ok (.Ok completed) ∈ support (continueResult result next)) :
    ∃ value, result = .ok (.Ok value) ∧ .ok (.Ok completed) ∈ support (next value) := by
  cases result with
  | ok value => cases value <;> simp_all [continueResult]
  | fail => simp_all [continueResult]
  | div => simp_all [continueResult]

/-- A successful callback chain consists only of the actual extracted continuations, ending in the actual write result. -/
inductive Path (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) : Prop where
  | mk (initialReply : core.option.Option pqxdh.concrete.InitialRatchetKdfResponse)
      (ratchetPhase : registration.ServerInitialSeal)
      (initialResume : initial.resume initialReply = .ok (.Ok ratchetPhase))
      (ratchetReply : core.option.Option ratchet.RatchetKdfResponse)
      (aead : registration.ServerRecordAead)
      (ratchetResume : ratchetPhase.resume ratchetReply = .ok (.Ok aead))
      (aeadReply : core.option.Option (Slice Std.U8 × Std.Array Std.U8 16#usize))
      (commitmentPhase : registration.ServerRecordCommitment)
      (aeadResume : aead.resume aeadReply = .ok (.Ok commitmentPhase))
      (hashReply : core.option.Option (Std.Array Std.U8 64#usize))
      (writePhase : registration.ServerRecordWrite)
      (commitmentResume : commitmentPhase.resume hashReply = .ok (.Ok writePhase))
      (writeReply : core.option.Option (Slice Std.U8))
      (writeResume : writePhase.resume writeReply = .ok (.Ok completed)) : Path initial completed

theorem fromInitial_path (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (supported : .ok (.Ok completed) ∈ support (fromInitial initial)) : Path initial completed := by
  obtain ⟨request, _, called⟩ := continueWith_support initial.request _ completed supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨initialReply, _, continued⟩ := called
  obtain ⟨ratchet, initialResume, supported⟩ := continueResult_support _ _ completed continued
  obtain ⟨request, _, called⟩ := continueWith_support ratchet.request _ completed supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨ratchetReply, _, continued⟩ := called
  obtain ⟨aead, ratchetResume, supported⟩ := continueResult_support _ _ completed continued
  obtain ⟨request, _, called⟩ := continueWith_support aead.request _ completed supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨aeadReply, _, continued⟩ := called
  obtain ⟨commitmentPhase, aeadResume, supported⟩ := continueResult_support _ _ completed continued
  obtain ⟨request, _, called⟩ := continueWith_support commitmentPhase.transcript _ completed supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨hashReply, _, continued⟩ := called
  obtain ⟨writePhase, commitmentResume, supported⟩ := continueResult_support _ _ completed continued
  obtain ⟨request, _, called⟩ := continueWith_support writePhase.request _ completed supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨writeReply, _, returned⟩ := called
  simp only [support_pure, Set.mem_singleton_iff] at returned
  exact ⟨initialReply, ratchet, initialResume, ratchetReply, aead, ratchetResume, aeadReply,
    commitmentPhase, aeadResume, hashReply, writePhase, commitmentResume, writeReply, returned.symm⟩

/-- The returned kernel is the actual advanced sequence-one seal capability, with the exact populated AD and retained registration owner. -/
theorem path_retains (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (path : Path initial completed) :
    completed.binding = initial.binding ∧ completed.candidate = initial.candidate ∧
      ∃ selected : ratchet.concrete.SendSeal record_effects.SealFrameContext,
        completed.kernel = selected.advanced ∧ selected.sequence.val = 1 ∧
        selected.context.associated_data = initial.binding.associated_data := by
  cases path with
  | mk initialReply ratchetPhase initialResume ratchetReply aead ratchetResume aeadReply commitmentPhase
      aeadResume hashReply writePhase commitmentResume writeReply writeResume =>
    cases initialReply with
    | none => simp [registration.ServerInitialKdf.resume, pqxdh.server_abort_candidate] at initialResume
    | some initialResponse =>
      obtain ⟨kernel, bound, next, _, _, _, resumed, stateSame, _, contextSame, sequence, _⟩ :=
        server_kdf_prefix_refines initial initialResponse
      have same : next = ratchetPhase := by simpa using resumed.symm.trans initialResume
      subst ratchetPhase
      cases ratchetReply with
      | none => simp [registration.ServerInitialSeal.resume, pqxdh.server_abort_candidate] at ratchetResume
      | some ratchetResponse =>
        obtain ⟨nextAead, resumed, aeadState, aeadContext, aeadSequence, _⟩ :=
          server_step_kdf_refines next ratchetResponse
        have same : nextAead = aead := by simpa using resumed.symm.trans ratchetResume
        subst aead
        cases aeadReply with
        | none =>
          simp [registration.ServerRecordAead.resume,
            BeaconcryptCore.Refinement.RecordEffects.seal_aead_missing_exact,
            pqxdh.server_abort_candidate] at aeadResume
        | some pair =>
          obtain ⟨ciphertext, tag⟩ := pair
          obtain ⟨nextCommitment, resumed, commitmentState, commitmentSeal, _⟩ :=
            server_aead_reply_refines nextAead ciphertext tag
          have same : nextCommitment = commitmentPhase := by simpa using resumed.symm.trans aeadResume
          subst commitmentPhase
          cases hashReply with
          | none =>
            simp [registration.ServerRecordCommitment.resume,
              BeaconcryptCore.Refinement.RecordEffects.seal_commitment_missing_exact,
              pqxdh.server_abort_candidate] at commitmentResume
          | some digest =>
            obtain ⟨nextWrite, resumed, writeState, writeSeal, _⟩ :=
              server_commitment_reply_refines nextCommitment digest
            have same : nextWrite = writePhase := by simpa using resumed.symm.trans commitmentResume
            subst writePhase
            obtain ⟨result, resumed, retained⟩ :=
              BeaconcryptCore.Refinement.RegistrationPublication.server_seal_retention_refines nextWrite writeReply
            have same : result = .Ok completed := by simpa using resumed.symm.trans writeResume
            rw [same] at retained
            refine ⟨?_, ?_, nextAead.pending.seal, ?_, ?_, ?_⟩
            · simpa only [BeaconcryptCore.Refinement.RegistrationPublication.serverSealRetains,
                writeState, commitmentState, aeadState, stateSame] using retained.2.1
            · simpa only [BeaconcryptCore.Refinement.RegistrationPublication.serverSealRetains,
                writeState, commitmentState, aeadState, stateSame] using retained.1
            · simpa only [writeSeal, commitmentSeal] using retained.2.2.1
            · rw [aeadSequence]
              exact sequence
            · rw [aeadContext, contextSame]
              rfl

/-- Stateful interpretation can return a response only through the actual checked native completion gate and all five source callbacks. -/
theorem execute_path {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (completed : registration.ServerResponseHash)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((execute source writer control current availability agreement application).run before)) :
    ∃ initial, registration.begin_server_completion control current availability agreement application = .ok (.Ok initial) ∧
      Path initial completed := by
  have native : .ok (.Ok completed) ∈ support (begin control current availability agreement application) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationRecordPrimitives.implementation source writer) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  obtain ⟨initial, started, continued⟩ := continueResult_support _ _ completed native
  exact ⟨initial, started, fromInitial_path initial completed continued⟩

theorem changed_pin_rejects (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (changed : ¬ BeaconcryptCore.Refinement.SessionBinding.sameServerPin agreement.binding.server_pin current) :
    begin control current availability agreement application = pure (.ok (.Err control)) := by
  rw [begin, BeaconcryptCore.Refinement.RegistrationPublication.server_owner_rejects
    control current availability agreement application changed]
  rfl

/-- Native completion never substitutes a registration binding when constructing its initial-record capability. -/
theorem initial_binding (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : registration.begin_server_completion control current availability agreement application = .ok (.Ok initial)) :
    initial.binding = agreement.binding := by
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty application = .ok result := ⟨_, rfl⟩
  obtain ⟨matched, matchRun⟩ := BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total
    agreement.binding current
  obtain ⟨prepared, prepareRun⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok control agreement.pending
    current.binding availability
  cases prepared with
  | Err error =>
      cases empty <;> cases matched <;>
        simp [registration.begin_server_completion, session.ServerAuthenticationPin.impl.binding,
          emptyRun, matchRun, prepareRun] at actual
  | Ok candidate =>
      obtain ⟨pending, pendingRun⟩ :=
        BeaconcryptCore.PanicFreedom.Structural.pqxdh_concrete_start_server_candidate_ratchet_kdf_total
          candidate agreement.root.bytes
      cases empty <;> cases matched
      all_goals simp only [registration.begin_server_completion, session.ServerAuthenticationPin.impl.binding,
        ratchet.RatchetChain.as_bytes, emptyRun, matchRun, prepareRun, pendingRun, bind_tc_ok,
        Bool.false_eq_true, ite_false, ite_true, RustM.ok.injEq, core.result.Result.Ok.injEq,
        reduceCtorEq] at actual
      cases actual
      rfl

/-- A successful concrete run returns the source sequence-one advanced kernel and original populated binding, after rechecking the complete current pin. -/
theorem execute_retains {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (completed : registration.ServerResponseHash)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((execute source writer control current availability agreement application).run before)) :
    BeaconcryptCore.Refinement.SessionBinding.sameServerPin agreement.binding.server_pin current ∧
      completed.binding = agreement.binding ∧
      ∃ selected : ratchet.concrete.SendSeal record_effects.SealFrameContext,
        completed.kernel = selected.advanced ∧ selected.sequence.val = 1 ∧
        selected.context.associated_data = agreement.binding.associated_data := by
  obtain ⟨initial, started, path⟩ :=
    execute_path source writer control current availability agreement application before after completed supported
  obtain ⟨binding, _, selected, kernel, sequence, data⟩ := path_retains initial completed path
  have sameBinding := initial_binding control current availability agreement application initial started
  refine ⟨?_, binding.trans sameBinding, selected, kernel, sequence, ?_⟩
  · by_contra changed
    unfold execute at supported
    rw [changed_pin_rejects control current availability agreement application changed] at supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at supported
  · exact data.trans (congrArg (fun value => value.associated_data) sameBinding)

end BeaconcryptCore.Computational.RegistrationServerRecordExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordExecutor.fromInitial_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordExecutor.fromInitial_path
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordExecutor.path_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordExecutor.path_retains
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordExecutor.execute_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordExecutor.execute_path
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordExecutor.changed_pin_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordExecutor.changed_pin_rejects
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordExecutor.initial_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordExecutor.initial_binding
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordExecutor.execute_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordExecutor.execute_retains
