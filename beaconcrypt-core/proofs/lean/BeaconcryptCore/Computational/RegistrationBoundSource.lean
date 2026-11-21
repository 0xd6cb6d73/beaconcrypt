-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationSeedErasure
import BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule
import BeaconcryptCore.Computational.RegistrationBoundKeySchedule

/-! The actual initial64 and ongoing76 callbacks evaluate the same selected functional HKDF source and preserve its complete shared primitive state. After the actual Server gate, those replies feed the existing root-free bound108 continuation. This is a derived source-program equation, with populated AD and all later seal, hash, write and failure effects retained. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationRecords
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationBoundSource

open PqxdhSecretInputKdf (RootOutput)
open PqxdhServerAuthKeySchedule (initializer fromRoot)
open RegistrationBoundKeySchedule (publicInitial factored supplied)

theorem initial_response (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    RawCtxSourceHkdf.initialResponse source.crypto
        ⟨PqxdhRootTableInitialization.rootArray root, INITIAL_RATCHET_INFO⟩ =
      RawCtxSelectedInitialConstructor.response64 (PqxdhSecretInputKdf.first32 (initializer source root) ++
        RawCtxSelectedInitialSecond.secondChain (initializer source root)) := by
  rw [RawCtxSelectedInitialConstructor.split_reconstruct]
  unfold RawCtxSourceHkdf.initialResponse RawCtxSelectedInitialConstructor.response64 initializer
  congr 2
  rw [PqxdhRootTableInitialization.rootArray_bytes,
    PqxdhInitialRatchetComplementarity.absBytes_ratchetInitialInfo]
  rfl

theorem ratchet_reply {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (request : SymmetricRatchetKdfRequest)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (RegistrationRecordPrimitives.implementation source writer (.ratchetKdf request)).run state =
      pure (.Some (RawCtxSourceHkdf.response source.crypto request), state) := rfl

theorem ratchet_response (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (chain : RootOutput) :
    RawCtxSourceHkdf.response source.crypto ⟨PqxdhRootTableInitialization.rootArray chain, SYM_RATCHET_INFO⟩ =
      RawCtxKdfRequestTable.fullResponse (PqxdhServerAuthKeySchedule.step source chain) := by
  have exactResponse := RawCtxKdfRequestTable.fullResponse_source source
    ⟨PqxdhRootTableInitialization.rootArray chain, SYM_RATCHET_INFO⟩
  simpa only [RawCtxKdfRequestTable.address, PqxdhRootTableInitialization.rootArray_bytes,
    PqxdhInitialRatchetComplementarity.absBytes_ratchetSymmetricInfo,
    PqxdhServerAuthKeySchedule.step, PqxdhJointKdfGame.FixedHkdfDomain.address,
    PqxdhJointKdfGame.FixedHkdfDomain.info] using exactResponse.symm

theorem next_request (initial : registration.ServerInitialKdf) (root : Std.Array Std.U8 32#usize)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending root)
    (left right : RootOutput) :
    ∃ next : registration.ServerInitialSeal,
      initial.resume (.Some (RawCtxSelectedInitialConstructor.response64 (left ++ right))) = .ok (.Ok next) ∧
      next.request = .ok ⟨PqxdhRootTableInitialization.rootArray left, SYM_RATCHET_INFO⟩ := by
  obtain ⟨kernel, _bound, next, kernelRun, _boundRun, _boundBytes, initialRun,
      _state, entry, _context, _sequence, request, input, info⟩ :=
    server_kdf_prefix_refines initial (RawCtxSelectedInitialConstructor.response64 (left ++ right))
  have initialEq := RegistrationSeedErasure.initial_kernel initial root role left right
  rw [kernelRun] at initialEq
  simp only [ConcreteRatchetKernel.from_counters, ratchet.refined.RefinedRatchet.from_counters,
    ratchet.control.RatchetState.from_counters, ratchet.control.SequenceCache.empty,
    ratchet.refined.empty_material_slots, bind_tc_ok, RustM.ok.injEq] at initialEq
  have bytes : next.pending.pending.request.input = PqxdhRootTableInitialization.rootArray left :=
    input.trans ((congrArg (fun kernel : ConcreteRatchetKernel => kernel.refined.send_chain.bytes)
      initialEq).trans rfl)
  have requestEq : next.pending.pending.request =
      (⟨PqxdhRootTableInitialization.rootArray left, SYM_RATCHET_INFO⟩ : SymmetricRatchetKdfRequest) := by
    exact congrArg₂ SymmetricRatchetKdfRequest.mk bytes info
  exact ⟨next, initialRun, request.trans (congrArg RustM.ok requestEq)⟩

theorem initial_supplied {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (initial : registration.ServerInitialKdf) (root : RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RegistrationRecordPrimitives.implementation source writer)
      (RegistrationServerRecordExecutor.fromInitial initial)).run state =
      (simulateQ (RegistrationRecordPrimitives.implementation source writer)
        (supplied initial (PqxdhSecretInputKdf.first32 (initializer source root))
          (RawCtxSelectedInitialSecond.secondChain (initializer source root)) (fromRoot source root).1)).run state := by
  have initialRequested : initial.request =
      .ok ⟨PqxdhRootTableInitialization.rootArray root, INITIAL_RATCHET_INFO⟩ := by
    simp only [registration.ServerInitialKdf.request, role,
      pqxdh.concrete.InitialRatchetKdfPending.impl.request, PqxdhInitialRatchetComplementarity.serverPending]
  obtain ⟨next, initialRun, nextRequested⟩ := next_request initial _ role
    (PqxdhSecretInputKdf.first32 (initializer source root))
    (RawCtxSelectedInitialSecond.secondChain (initializer source root))
  simp only [RegistrationServerRecordExecutor.fromInitial, initialRequested,
    RegistrationServerRecordExecutor.continueWith, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [RegistrationRecordPrimitives.initial_exact]
  simp only [pure_bind, initial_response, initialRun,
    RegistrationServerRecordExecutor.continueResult, RegistrationServerRecordExecutor.fromRatchet, nextRequested,
    RegistrationServerRecordExecutor.continueWith, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    supplied, RegistrationSeedErasure.selected, bind_tc_ok]
  rw [ratchet_reply]
  simp only [pure_bind, ratchet_response, PqxdhServerAuthKeySchedule.fromRoot,
    PqxdhServerAuthKeySchedule.fromInitializer]

theorem initial_factored {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (initial : registration.ServerInitialKdf) (root : RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RegistrationRecordPrimitives.implementation source writer)
      (RegistrationServerRecordExecutor.fromInitial initial)).run state =
      (simulateQ (RegistrationRecordPrimitives.implementation source writer)
        (factored (publicInitial initial) (fromRoot source root))).run state := by
  rw [initial_supplied source writer initial root role]
  have erased : supplied initial (PqxdhSecretInputKdf.first32 (initializer source root))
      (RawCtxSelectedInitialSecond.secondChain (initializer source root)) (fromRoot source root).1 =
      factored (publicInitial initial) (fromRoot source root) := by
    unfold supplied factored
    dsimp only [PqxdhServerAuthKeySchedule.fromRoot, PqxdhServerAuthKeySchedule.fromInitializer]
    rw [RegistrationSeedErasure.left_unused initial (PqxdhRootTableInitialization.rootArray root) role
      (PqxdhSecretInputKdf.first32 (initializer source root)) RegistrationBoundKeySchedule.zero
      (RawCtxSelectedInitialSecond.secondChain (initializer source root))]
    rw [RegistrationBoundKeySchedule.root_unused initial (PqxdhRootTableInitialization.rootArray root) role]
  rw [erased]

/-- Factoring begins at a real already completed AD phase; it does not erase the preceding hash effect. -/
theorem admitted_initial_factored {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control current availability agreement application initial)
    (root : RootOutput) (rootEq : agreement.root.bytes = PqxdhRootTableInitialization.rootArray root)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RegistrationRecordPrimitives.implementation source writer)
      (RegistrationServerRecordExecutor.fromInitial initial)).run state =
      (simulateQ (RegistrationRecordPrimitives.implementation source writer)
        (factored (publicInitial initial) (fromRoot source root))).run state := by
  apply initial_factored source writer initial root
  rw [RegistrationSeedKernel.server_pending control current availability agreement application initial actual, rootEq]

def rootValue (bytes : Std.Array Std.U8 32#usize) : RootOutput :=
  ⟨absBytes bytes, by simpa only [absBytes, List.length_map, Std.UScalar.ofNatCore_val_eq] using bytes.property⟩

theorem root_value_array (bytes : Std.Array Std.U8 32#usize) :
    PqxdhRootTableInitialization.rootArray (rootValue bytes) = bytes := by
  apply Subtype.ext
  apply (absBytes_inj_iff _ _).mp
  rw [PqxdhRootTableInitialization.rootArray_bytes]
  rfl

/-- The actual AD query is retained before public root-free key-schedule factoring. -/
def fromAd (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : registration.ServerAdHash) :
    OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationServerRecordExecutor.continueWith pending.request fun request => do
    let reply ← RegistrationRecordPrimitives.Spec.query (.adHash request)
    RegistrationServerRecordExecutor.continueResult (pending.resume reply) fun initial =>
      factored (publicInitial initial) (fromRoot source (rootValue pending.root.bytes))

/-- Every actual AD-hash outcome retains its cache effect and selects the same consumed kernel. -/
theorem ad_factored {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (pending : registration.ServerAdHash)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RegistrationRecordPrimitives.implementation source writer)
      (RegistrationServerRecordExecutor.fromAd pending)).run state =
      (simulateQ (RegistrationRecordPrimitives.implementation source writer) (fromAd source pending)).run state := by
  cases requested : pending.request with
  | fail error => simp only [RegistrationServerRecordExecutor.fromAd, fromAd, requested,
      RegistrationServerRecordExecutor.continueWith]
  | div => simp only [RegistrationServerRecordExecutor.fromAd, fromAd, requested,
      RegistrationServerRecordExecutor.continueWith]
  | ok request =>
    simp only [RegistrationServerRecordExecutor.fromAd, fromAd, requested,
      RegistrationServerRecordExecutor.continueWith, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply bind_congr
    intro result
    rcases result with ⟨reply, after⟩
    cases reply with
    | none => simp only [registration.ServerAdHash.resume, pqxdh.server_abort_candidate, bind_tc_ok,
        RegistrationServerRecordExecutor.continueResult]
    | some digest =>
      obtain ⟨initial, resumed, _⟩ :=
        BeaconcryptCore.Refinement.RegistrationAd.server_digest_completes_binding pending digest
      simp only [resumed, RegistrationServerRecordExecutor.continueResult]
      apply initial_factored source writer initial (rootValue pending.root.bytes)
      rw [root_value_array]
      exact BeaconcryptCore.Refinement.RegistrationAd.server_ad_resume_pending pending digest initial resumed

def begin (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8) :
    OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationServerRecordExecutor.continueResult
    (registration.begin_server_completion control current availability agreement application) (fromAd source)

/-- Whole source factoring preserves the actual AD request, every failure, and the reached global cache. -/
theorem execute_source {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (RegistrationServerRecordExecutor.execute source writer control current availability agreement application).run state =
      (simulateQ (RegistrationRecordPrimitives.implementation source writer)
        (begin source control current availability agreement application)).run state := by
  cases actual : registration.begin_server_completion control current availability agreement application with
  | fail error => simp only [RegistrationServerRecordExecutor.execute, RegistrationServerRecordExecutor.begin,
      begin, actual, RegistrationServerRecordExecutor.continueResult]
  | div => simp only [RegistrationServerRecordExecutor.execute, RegistrationServerRecordExecutor.begin,
      begin, actual, RegistrationServerRecordExecutor.continueResult]
  | ok result =>
    cases result with
    | Err previous => simp only [RegistrationServerRecordExecutor.execute, RegistrationServerRecordExecutor.begin,
        begin, actual, RegistrationServerRecordExecutor.continueResult]
    | Ok pending =>
      simp only [RegistrationServerRecordExecutor.execute, RegistrationServerRecordExecutor.begin,
        begin, actual, RegistrationServerRecordExecutor.continueResult]
      exact ad_factored source writer pending state

end BeaconcryptCore.Computational.RegistrationBoundSource

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSource.initial_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSource.initial_response
/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSource.ratchet_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSource.ratchet_reply

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSource.ratchet_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSource.ratchet_response

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSource.next_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSource.next_request

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSource.initial_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSource.initial_supplied

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSource.initial_factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSource.initial_factored

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSource.admitted_initial_factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSource.admitted_initial_factored

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSource.root_value_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSource.root_value_array

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSource.execute_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSource.execute_source
