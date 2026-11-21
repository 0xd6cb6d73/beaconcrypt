-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationRecordPrimitives
import BeaconcryptCore.Refinement.RegistrationRecords
import BeaconcryptCore.Refinement.RegistrationAd

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

/-- AD is hashed and completed before either initial-record KDF. Missing replies follow the owned candidate rejection path. -/
def fromAd (pending : registration.ServerAdHash) : OracleComp Spec (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← Spec.query (.adHash request)
    continueResult (pending.resume reply) fromInitial

/-- The actual full current-pin comparison and native allocation gate run before any primitive callback. -/
def begin (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8) :
    OracleComp Spec (RustM Result) :=
  continueResult (registration.begin_server_completion control current availability agreement application) fromAd

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

/-- Stateful interpretation can return a response only through the actual checked native completion gate and the AD hash and all five initial-record callbacks. -/
theorem execute_path {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (completed : registration.ServerResponseHash)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((execute source writer control current availability agreement application).run before)) :
    ∃ initial, BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control current availability agreement application initial ∧
      Path initial completed := by
  have native : .ok (.Ok completed) ∈ support (begin control current availability agreement application) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationRecordPrimitives.implementation source writer) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  obtain ⟨ad, selected, hashing⟩ := continueResult_support _ _ completed native
  obtain ⟨request, _, called⟩ := continueWith_support ad.request _ completed hashing
  simp only [mem_support_bind_iff] at called
  obtain ⟨reply, _, continued⟩ := called
  obtain ⟨initial, resumed, recorded⟩ := continueResult_support _ _ completed continued
  cases reply with
  | none => simp [registration.ServerAdHash.resume, pqxdh.server_abort_candidate] at resumed
  | some digest => exact ⟨initial, ⟨ad, digest, selected, resumed⟩, fromInitial_path initial completed recorded⟩

theorem changed_pin_rejects (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (changed : ¬ BeaconcryptCore.Refinement.SessionBinding.sameServerPin agreement.binding.server_pin current) :
    begin control current availability agreement application = pure (.ok (.Err control)) := by
  rw [begin, BeaconcryptCore.Refinement.RegistrationPublication.server_owner_rejects
    control current availability agreement application changed]
  rfl

/-- The initial record uses the completed binding from the actual selected AD-hash continuation. -/
theorem initial_completed_binding (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control current availability agreement application initial) :
    ∃ digest binding, agreement.binding.complete digest = .ok binding ∧ initial.binding = binding ∧
      BeaconcryptCore.Refinement.SessionBinding.registrationConsistent binding ∧
      pqxdh.server_prepare_commit control agreement.pending current.binding availability = .ok (.Ok initial.candidate) :=
  BeaconcryptCore.Refinement.RegistrationAd.server_admission_binding
    control current availability agreement application initial actual

/-- A successful concrete run returns the source sequence-one advanced kernel and original populated binding, after rechecking the complete current pin. -/
theorem execute_retains_completed_ad {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (completed : registration.ServerResponseHash)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((execute source writer control current availability agreement application).run before)) :
    BeaconcryptCore.Refinement.SessionBinding.sameServerPin agreement.binding.server_pin current ∧
      ∃ digest binding, agreement.binding.complete digest = .ok binding ∧ completed.binding = binding ∧
      BeaconcryptCore.Refinement.SessionBinding.registrationConsistent binding ∧
      ∃ selected : ratchet.concrete.SendSeal record_effects.SealFrameContext,
        completed.kernel = selected.advanced ∧ selected.sequence.val = 1 ∧
        selected.context.associated_data = binding.associated_data := by
  obtain ⟨initial, started, path⟩ :=
    execute_path source writer control current availability agreement application before after completed supported
  obtain ⟨bindingSame, _, selected, kernel, sequence, data⟩ := path_retains initial completed path
  obtain ⟨digest, binding, complete, sameBinding, consistent, _prepared⟩ :=
    initial_completed_binding control current availability agreement application initial started
  refine ⟨?_, digest, binding, complete, bindingSame.trans sameBinding, consistent,
    selected, kernel, sequence, data.trans (congrArg (fun value => value.associated_data) sameBinding)⟩
  by_contra changed
  unfold execute at supported
  rw [changed_pin_rejects control current availability agreement application changed] at supported
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at supported

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
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordExecutor.initial_completed_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordExecutor.initial_completed_binding
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordExecutor.execute_retains_completed_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordExecutor.execute_retains_completed_ad
