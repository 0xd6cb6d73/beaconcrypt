-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBoundSource
import BeaconcryptCore.Computational.RegistrationHiddenInstall

/-! Current-pin, application and allocation admission do not inspect the selected root bytes. The actual native completion gate can therefore be evaluated on public agreement fields before sampling a root PRK; only its successful first-record continuation consumes the key schedule. Failure still returns exactly the native entry control. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationBoundGate
open RegistrationPublicationKernelErasure (mapOk)
open PqxdhSecretInputKdf (RootOutput)

/-- The actual retained post-root agreement fields, excluding its private root chain. -/
structure PublicAgreement where
  pending : pqxdh.PendingServerRegistration
  binding : session.RegistrationBinding

def atRoot (agreement : PublicAgreement) (root : RootOutput) : beaconcrypt_core.agreement.ServerAgreement :=
  ⟨agreement.pending, agreement.binding, ⟨PqxdhRootTableInitialization.rootArray root⟩⟩

def gate (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8) :
    RustM (core.result.Result RegistrationBoundKeySchedule.PublicAd pqxdh.ServerState) :=
  mapOk RegistrationBoundKeySchedule.publicAd <$>
    registration.begin_server_completion control current availability
      (atRoot agreement RegistrationBoundKeySchedule.zero) application

/-- The current pre-hash gate restores only the original private root; its public encoder output is unchanged. -/
theorem gate_source (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8)
    (root : RootOutput) :
    registration.begin_server_completion control current availability (atRoot agreement root) application =
      mapOk (fun pending => RegistrationBoundKeySchedule.restoreAd pending root) <$>
        gate control current availability agreement application := by
  obtain ⟨empty, emptyRun⟩ : ∃ value, core.slice.Slice.is_empty application = .ok value := ⟨_, rfl⟩
  obtain ⟨matched, matchedRun⟩ := BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total
    agreement.binding current
  obtain ⟨prepared, preparedRun⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok control
    agreement.pending current.binding availability
  cases prepared with
  | Err error =>
    cases empty <;> cases matched <;> simp only [gate, atRoot, registration.begin_server_completion,
      emptyRun, matchedRun, session.ServerAuthenticationPin.impl.binding, preparedRun, bind_tc_ok,
      Bool.false_eq_true, ite_false, ite_true, RawCtxMaterialInterpretation.rust_map_ok, mapOk]
  | Ok candidate =>
    obtain ⟨bytes, bytesRun, _⟩ := BeaconcryptCore.Refinement.RegistrationAd.pending_transcript_exact
      agreement.binding (BeaconcryptCore.Refinement.RegistrationAd.serverView candidate)
    simp only [BeaconcryptCore.Refinement.RegistrationAd.serverView] at bytesRun
    cases empty <;> cases matched <;> simp only [gate, atRoot, registration.begin_server_completion,
      emptyRun, matchedRun, session.ServerAuthenticationPin.impl.binding, preparedRun, bind_tc_ok,
      Bool.false_eq_true, ite_false, ite_true, RawCtxMaterialInterpretation.rust_map_ok, mapOk,
      pqxdh.ServerRegistrationCandidate.impl.server_identity_public_key,
      pqxdh.ServerRegistrationCandidate.impl.ephemeral_public_key,
      pqxdh.ServerRegistrationCandidate.impl.kem_ciphertext, pqxdh.ServerRegistrationCandidate.impl.key_id,
      bytesRun, RegistrationBoundKeySchedule.publicAd, RegistrationBoundKeySchedule.restoreAd]

/-- Public admission does not inspect private root bytes; it still returns a hash phase, not final AD. -/
theorem gate_root (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8)
    (root : RootOutput) :
    mapOk RegistrationBoundKeySchedule.publicAd <$>
        registration.begin_server_completion control current availability (atRoot agreement root) application =
      gate control current availability agreement application := by
  rw [gate_source]
  cases actual : gate control current availability agreement application with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

theorem root_value (root : RootOutput) :
    RegistrationBoundSource.rootValue (PqxdhRootTableInitialization.rootArray root) = root := by
  apply List.Vector.toList_injective
  exact PqxdhRootTableInitialization.rootArray_bytes root

/-- Public metadata from AD completion is independent of the private root. The hash reply is retained unchanged. -/
theorem ad_resume_public_root (pending : RegistrationBoundKeySchedule.PublicAd) (root : RootOutput)
    (reply : core.option.Option (Std.Array U8 64#usize)) :
    mapOk RegistrationBoundKeySchedule.publicInitial <$>
        (RegistrationBoundKeySchedule.restoreAd pending root).resume reply =
      mapOk RegistrationBoundKeySchedule.publicInitial <$>
        (RegistrationBoundKeySchedule.restoreAd pending RegistrationBoundKeySchedule.zero).resume reply := by
  cases reply with
  | none => rfl
  | some digest =>
    obtain ⟨binding, bindingRun, _⟩ := BeaconcryptCore.Refinement.SessionBinding.complete_refines pending.binding digest
    have initial (candidate : pqxdh.ServerRegistrationCandidate) (bytes : Std.Array U8 32#usize) :
        pqxdh.concrete.start_server_candidate_ratchet_kdf candidate bytes =
          .ok (PqxdhInitialRatchetComplementarity.serverPending bytes) := by
      simpa only [pqxdh.concrete.start_server_candidate_ratchet_kdf,
        pqxdh.ServerRegistrationCandidate.ratchet_initialization,
        pqxdh.concrete.start_server_ratchet_kdf, PqxdhInitialRatchetComplementarity.serverPending] using
        pqxdh.concrete.start_server_ratchet_kdf_exact bytes
    simp only [RegistrationBoundKeySchedule.restoreAd, registration.ServerAdHash.resume,
      ratchet.RatchetChain.as_bytes, initial, bindingRun, bind_tc_ok,
      RawCtxMaterialInterpretation.rust_map_ok, mapOk, RegistrationBoundKeySchedule.publicInitial]

private theorem continue_public (action : RustM (core.result.Result registration.ServerInitialKdf pqxdh.ServerState))
    (output : PqxdhServerAuthKeySchedule.Output) :
    RegistrationServerRecordExecutor.continueResult action (fun initial =>
      RegistrationBoundKeySchedule.factored (RegistrationBoundKeySchedule.publicInitial initial) output) =
      RegistrationServerRecordExecutor.continueResult
        (mapOk RegistrationBoundKeySchedule.publicInitial <$> action) (fun initial =>
          RegistrationBoundKeySchedule.factored initial output) := by
  cases action with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

/-- The real AD hash is queried before the root-free material continuation. A zero root appears only in this private erased descriptor; the actual AD always contains the real hash reply. -/
def afterAd (pending : RegistrationBoundKeySchedule.PublicAd) (output : PqxdhServerAuthKeySchedule.Output) :
    OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result) :=
  let selected := RegistrationBoundKeySchedule.restoreAd pending RegistrationBoundKeySchedule.zero
  RegistrationServerRecordExecutor.continueWith selected.request fun request => do
    let reply ← RegistrationRecordPrimitives.Spec.query (.adHash request)
    RegistrationServerRecordExecutor.continueResult (selected.resume reply) fun initial =>
      RegistrationBoundKeySchedule.factored (RegistrationBoundKeySchedule.publicInitial initial) output

theorem afterAd_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : RegistrationBoundKeySchedule.PublicAd) (root : RootOutput) :
    RegistrationBoundSource.fromAd source (RegistrationBoundKeySchedule.restoreAd pending root) =
      afterAd pending (PqxdhServerAuthKeySchedule.fromRoot source root) := by
  simp only [RegistrationBoundSource.fromAd, afterAd, RegistrationBoundKeySchedule.restoreAd,
    root_value]
  apply congrArg (RegistrationServerRecordExecutor.continueWith _)
  funext request
  apply bind_congr
  intro reply
  rw [continue_public, continue_public]
  exact congrArg (fun action => RegistrationServerRecordExecutor.continueResult action fun initial =>
    RegistrationBoundKeySchedule.factored initial (PqxdhServerAuthKeySchedule.fromRoot source root))
    (ad_resume_public_root pending root reply)

/-- The public gate still exposes no usable AD before its actual hash callback. -/
def factored (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8)
    (output : PqxdhServerAuthKeySchedule.Output) :
    OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationServerRecordExecutor.continueResult
    (gate control current availability agreement application) fun pending => afterAd pending output

/-- Whole source factoring retains the actual response-dependent AD query before key-schedule use. -/
theorem source_begin (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8)
    (root : RootOutput) :
    RegistrationBoundSource.begin source control current availability (atRoot agreement root) application =
      factored control current availability agreement application (PqxdhServerAuthKeySchedule.fromRoot source root) := by
  unfold RegistrationBoundSource.begin factored
  rw [gate_source]
  cases actual : gate control current availability agreement application with
  | fail error => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err previous => rfl
    | Ok pending => exact afterAd_source source pending root

/-- Actual current-pin/allocator admission and both actual64/76 callbacks reduce to the same public gate and bound continuation, retaining complete cache and auxiliary state. -/
theorem source_execute {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8)
    (root : RootOutput) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (RegistrationServerRecordExecutor.execute source writer control current availability (atRoot agreement root) application).run state =
      (simulateQ (RegistrationRecordPrimitives.implementation source writer)
        (factored control current availability agreement application (PqxdhServerAuthKeySchedule.fromRoot source root))).run state := by
  rw [RegistrationBoundSource.execute_source, source_begin]

end BeaconcryptCore.Computational.RegistrationBoundGate

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundGate.gate_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundGate.gate_root

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundGate.root_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundGate.root_value

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundGate.source_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundGate.source_begin

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundGate.source_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundGate.source_execute
