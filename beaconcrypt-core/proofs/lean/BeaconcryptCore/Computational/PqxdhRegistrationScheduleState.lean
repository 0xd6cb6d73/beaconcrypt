-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationSchedule

/-! Lift actual Server admission, moved-token and publication state through the same interleaved native registration scheduler. These are operational state relations, not authentication or origin premises. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Every complete Beacon finish preserves the shared Server, consumed pairs, pending entries, attempt counter and shared Server-side observations. Both primitive caches retain the original actual callback effects. -/
theorem finish_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support (finish setup codec index raw state)) :
    result.2.shared.2 = { state.shared.2 with ctx := result.2.shared.2.ctx } := by
  cases found : state.owners[index]? with
  | none =>
      change result ∈ support ((finish setup codec index raw).run state) at supported
      rw [finish_missing setup codec index raw state found, support_pure, Set.mem_singleton_iff] at supported
      simp only [supported]
  | some owner =>
      simp only [finish_source setup codec index raw state owner found, support_map, Set.mem_image] at supported
      obtain ⟨reached, member, rfl⟩ := supported
      exact program_fields setup codec _ state.shared reached member

/-- Exactly the capabilities that operate on the dynamic Beacon registry. They may change shared cryptographic caches while preserving Server protocol fields. -/
def IsOwnerQuery : Spec.Domain → Prop
  | .inr (.create _ _) | .inr (.bundle _) | .inr (.finish _ _) => True
  | _ => False

/-- Actual creation, Phase-1 and complete initial receive preserve the complete shared Server-side state outside the CTX cache. -/
theorem owner_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (isOwner : IsOwnerQuery query) (state : State KemSK) (result : Spec.Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    result.2.shared.2 = { state.shared.2 with ctx := result.2.shared.2.ctx } := by
  rcases query with coin | request
  · exact False.elim isOwner
  · cases request with
    | bundle index =>
        cases found : state.owners[index]? with
        | none =>
            simp only [handler, bundle, StateT.run_bind, StateT.run_get, pure_bind, found,
              StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
            simp only [supported]
        | some owner =>
            simp only [handler, StateT.run, bundle_source setup codec index state owner found,
              support_map, Set.mem_image] at supported
            obtain ⟨reached, _, rfl⟩ := supported
            rfl
    | create pin keyId =>
        simp only [handler, StateT.run, create_source, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at supported
        obtain ⟨identity, _, prekey, _, keys, _, rfl⟩ := supported
        rfl
    | finish index raw => exact finish_fields setup codec index raw state result supported
    | _ => exact False.elim isOwner

/-- Interpreting an original Server/public program inside the shared native state returns an original supported reply and full Server-side state. Primitive evaluation retains its actual shared effects. -/
theorem shared_original {Result : Type} (setup : Setup baseSpec KemSK) (serverSeed : IdentitySeed)
    (work : PqxdhServerAuthExperiment.Game KemSK Result) (state : State KemSK)
    (result : Result × State KemSK)
    (supported : result ∈ support ((onShared (evaluate setup serverSeed observationScalar work)).run state)) :
    (result.1, result.2.shared.2) ∈ support (work.run state.shared.2) := by
  simp only [onShared_run, support_map, Set.mem_image] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  exact evaluate_support setup serverSeed observationScalar work state.shared reached member

/-- A Server-side operational relation lifts through the actual joint scheduler once it is stable under Beacon cache changes. The native Server/public handlers are compared directly to their original source programs, not through a reachable-state or security premise. -/
theorem server_relation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (relation : GameState KemSK → GameState KemSK → Prop)
    (cache : ∀ state value, relation state { state with ctx := value })
    (step : ∀ query state result,
      result ∈ support ((authHandler setup codec checks
        (challenge setup.joint setup.dh serverSeed observationScalar) serverSeed query).run state) →
      relation state result.2)
    (query : Spec.Domain) (state : State KemSK) (result : Spec.Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    relation state.shared.2 result.2.shared.2 := by
  cases query with
  | inl coin =>
      simp only [handler, StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      exact cache state.shared.2 state.shared.2.ctx
  | inr request =>
      cases request with
      | accept raw =>
          simp only [handler, onShared_run, support_map, Set.mem_image] at supported
          obtain ⟨reached, member, rfl⟩ := supported
          apply step (.inr (.accept raw)) state.shared.2 (reached.1, reached.2.2)
          apply evaluate_support setup serverSeed observationScalar _ state.shared reached
          simpa only [authHandler, accept_native setup codec checks serverSeed observationScalar raw] using member
      | build index payload =>
          apply step (.inr (.build index payload)) state.shared.2 (result.1, result.2.shared.2)
          apply shared_original setup serverSeed _ state result
          simpa only [handler, authHandler, build_native setup codec checks serverSeed observationScalar index payload] using supported
      | hmac key message =>
          exact step (.inr (.hmac key message)) state.shared.2 (result.1, result.2.shared.2)
            (shared_original setup serverSeed _ state result (by
              simpa only [handler, authHandler, hmac_native setup serverSeed observationScalar key message] using supported))
      | hash bytes =>
          exact step (.inr (.hash bytes)) state.shared.2 (result.1, result.2.shared.2)
            (shared_original setup serverSeed _ state result (by
              simpa only [handler, authHandler, hash_native setup serverSeed observationScalar bytes] using supported))
      | reveal keyId =>
          exact step (.inr (.reveal keyId)) state.shared.2 (result.1, result.2.shared.2)
            (shared_original setup serverSeed _ state result (by
              simpa only [handler, authHandler, evaluate_local setup serverSeed observationScalar] using supported))
      | _ =>
          rw [owner_fields setup codec checks serverSeed _ (by trivial) state result supported]
          exact cache state.shared.2 result.2.shared.2.ctx

/-- Each request in the joint schedule leaves the consumed-pair list unchanged or appends exactly one previously absent source pair. Arbitrary Beacon activity cannot alter this admission rule. -/
theorem handler_admission (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (state : State KemSK) (result : Spec.Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    PqxdhRegistrationAdmission.AdmissionStep state.shared.2.server.consumed result.2.shared.2.server.consumed := by
  exact server_relation setup codec checks serverSeed
    (fun before after => PqxdhRegistrationAdmission.AdmissionStep before.server.consumed after.server.consumed)
    (fun _ _ => Or.inl rfl)
    (PqxdhRegistrationAdmission.handler_admission setup codec checks
      (challenge setup.joint setup.dh serverSeed observationScalar) serverSeed)
    query state result supported

/-- The complete adaptive joint schedule retains every consumed pair and preserves uniqueness, including arbitrary rejected registrations, failed publication and interleaved dynamic Beacon operations. -/
theorem program_consumed {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp Spec Result)
    (state : State KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run state)) :
    state.shared.2.server.consumed.IsPrefix result.2.shared.2.server.consumed ∧
      (state.shared.2.server.consumed.Nodup → result.2.shared.2.server.consumed.Nodup) := by
  exact run_rel (handler setup codec checks serverSeed)
    (fun before after => before.shared.2.server.consumed.IsPrefix after.shared.2.server.consumed ∧
      (before.shared.2.server.consumed.Nodup → after.shared.2.server.consumed.Nodup))
    (fun _ => ⟨List.prefix_rfl, id⟩)
    (fun _ _ _ first second => ⟨first.1.trans second.1, second.2 ∘ first.2⟩)
    (fun query before after member => PqxdhRegistrationAdmission.admission_invariant _ _
      (handler_admission setup codec checks serverSeed query before after member))
    program state result supported

/-- No capability in the joint schedule restores an already allocated and consumed pending handle. Missing future handles remain outside this predicate. -/
theorem handler_spent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain) (index : Nat)
    (state : State KemSK) (result : Spec.Range query × State KemSK)
    (spent : PqxdhRegistrationPending.Spent index state.shared.2)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    PqxdhRegistrationPending.Spent index result.2.shared.2 := by
  exact server_relation setup codec checks serverSeed
    (fun before after => PqxdhRegistrationPending.Spent index before → PqxdhRegistrationPending.Spent index after)
    (fun _ _ disposed => disposed)
    (fun query before after member disposed => PqxdhRegistrationPending.handler_spent setup codec checks
      (challenge setup.joint setup.dh serverSeed observationScalar) serverSeed query index before after disposed member)
    query state result supported spent

/-- The actual complete adaptive schedule never resurrects an allocated moved token, even after arbitrary later registrations and Beacon lifecycle requests. -/
theorem program_spent {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp Spec Result) (index : Nat)
    (state : State KemSK) (result : Result × State KemSK)
    (spent : PqxdhRegistrationPending.Spent index state.shared.2)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run state)) :
    PqxdhRegistrationPending.Spent index result.2.shared.2 := by
  exact run_rel (handler setup codec checks serverSeed)
    (fun before after => PqxdhRegistrationPending.Spent index before.shared.2 →
      PqxdhRegistrationPending.Spent index after.shared.2)
    (fun _ => id) (fun _ _ _ first second => second ∘ first)
    (fun query before after member disposed => handler_spent setup codec checks serverSeed query index
      before after disposed member) program state result supported spent

/-- The actual build dispatch consumes its allocated pending handle on every result, including writer failure, while retaining every native effect. -/
theorem build_consumes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (index : Nat) (payload : Option Pqxdh.Bytes)
    (state : State KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × State KemSK)
    (allocated : index < state.shared.2.sessions)
    (supported : result ∈ support ((handler setup codec checks serverSeed (.inr (.build index payload))).run state)) :
    PqxdhRegistrationPending.Spent index result.2.shared.2 := by
  exact PqxdhRegistrationPending.build_consumes setup codec checks index payload state.shared.2
    (result.1, result.2.shared.2) allocated
    (shared_original setup serverSeed _ state result (by
      simpa only [handler, build_native setup codec checks serverSeed observationScalar index payload] using supported))

/-- An absent pending slot returns the original ordinary rejection without any callback or state change in the complete joint scheduler. -/
theorem missing_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (index : Nat) (payload : Option Pqxdh.Bytes)
    (state : State KemSK) (missing : state.shared.2.pending index = none) :
    (handler setup codec checks serverSeed (.inr (.build index payload))).run state = pure (none, state) := by
  change (onShared (nativeBuild setup codec checks index payload)).run state = _
  rw [onShared_run]
  simp only [nativeBuild, nativeGet_bind, missing, native_pure_run, map_pure]

/-- A complete build attempt cannot be repeated after any adaptive interleaving of new Beacons, registrations, raw finishes and public services. The allocated handle premise excludes guessed future slots, which the source may later create. -/
theorem no_rebuild {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (index : Nat)
    (payload replayPayload : Option Pqxdh.Bytes) (state : State KemSK)
    (first : Option PqxdhServerRegistrationPublication.Response × State KemSK)
    (allocated : index < state.shared.2.sessions)
    (firstRun : first ∈ support ((handler setup codec checks serverSeed (.inr (.build index payload))).run state))
    (program : OracleComp Spec Result) (last : Result × State KemSK)
    (continued : last ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run first.2)) :
    (handler setup codec checks serverSeed (.inr (.build index replayPayload))).run last.2 = pure (none, last.2) := by
  exact missing_build setup codec checks serverSeed index replayPayload last.2
    (program_spent setup codec checks serverSeed program index first.2 last
      (build_consumes setup codec checks serverSeed index payload state first allocated firstRun) continued).2

/-- The joint API publishes exactly the original successful response and successor ID. A failed build preserves the Server object, without asserting that its separate primitive/cache/signing observations disappear. -/
theorem build_counter (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (index : Nat) (payload : Option Pqxdh.Bytes)
    (state : State KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed (.inr (.build index payload))).run state)) :
    (result.1 = none ∧ result.2.shared.2.server = state.shared.2.server) ∨ ∃ response,
      result.1 = some response ∧
      result.2.shared.2.server.control.last_key_id.val = state.shared.2.server.control.last_key_id.val + 1 ∧
      response.keyId = result.2.shared.2.server.control.last_key_id := by
  exact PqxdhRegistrationResponse.build_oracle_counter setup codec checks index payload state.shared.2
    (result.1, result.2.shared.2)
    (shared_original setup serverSeed _ state result (by
      simpa only [handler, build_native setup codec checks serverSeed observationScalar index payload] using supported))

/-- Every actual joint API step preserves or increments the same live Server's checked public allocation counter. Dynamic Beacon and public primitive activity cannot reset it. -/
theorem handler_counter (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (state : State KemSK) (result : Spec.Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    result.2.shared.2.server.control.last_key_id.val = state.shared.2.server.control.last_key_id.val ∨
      result.2.shared.2.server.control.last_key_id.val = state.shared.2.server.control.last_key_id.val + 1 := by
  exact server_relation setup codec checks serverSeed
    (fun before after => after.server.control.last_key_id.val = before.server.control.last_key_id.val ∨
      after.server.control.last_key_id.val = before.server.control.last_key_id.val + 1)
    (fun _ _ => Or.inl rfl)
    (PqxdhRegistrationResponse.handler_counter setup codec checks
      (challenge setup.joint setup.dh serverSeed observationScalar) serverSeed)
    query state result supported

/-- The whole interleaved schedule keeps the actual numeric counter monotone; this includes all failed requests and all dynamically created owners. -/
theorem program_counter {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp Spec Result)
    (state : State KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run state)) :
    state.shared.2.server.control.last_key_id.val ≤ result.2.shared.2.server.control.last_key_id.val := by
  exact run_rel (handler setup codec checks serverSeed)
    (fun before after => before.shared.2.server.control.last_key_id.val ≤ after.shared.2.server.control.last_key_id.val)
    (fun _ => le_refl _) (fun _ _ _ first second => first.trans second)
    (fun query before after member => by
      rcases handler_counter setup codec checks serverSeed query before after member with same | next
      · rw [same]
      · rw [next]; omega)
    program state result supported

/-- Each accept request allocates the next public attempt index even when rejected. Only that new index can receive a new pending token; the dynamic Beacon registry does not alter this source operation. -/
theorem accept_pending (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : State KemSK) (result : Option Nat × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed (.inr (.accept raw))).run state)) :
    result.2.shared.2.sessions = state.shared.2.sessions + 1 ∧
      (result.2.shared.2.pending = state.shared.2.pending ∨ ∃ token,
        result.2.shared.2.pending = Function.update state.shared.2.pending state.shared.2.sessions (some token)) := by
  exact PqxdhServerAuthPendingBudget.accept_pending setup codec checks
    (challenge setup.joint setup.dh serverSeed observationScalar) raw state.shared.2
    (result.1, result.2.shared.2)
    (shared_original setup serverSeed _ state result (by
      simpa only [handler, accept_native setup codec checks serverSeed observationScalar raw] using supported))

end BeaconcryptCore.Computational.PqxdhRegistrationSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.owner_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.owner_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.shared_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.shared_original
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.server_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.server_relation
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_admission
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_consumed
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_spent
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_spent
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.build_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.build_consumes
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.missing_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.missing_build
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.no_rebuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.no_rebuild
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.build_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.build_counter
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_counter
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_counter
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.accept_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.accept_pending
