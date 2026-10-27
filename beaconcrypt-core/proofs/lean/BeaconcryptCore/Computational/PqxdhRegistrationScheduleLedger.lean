-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleState

/-! All-attempt source allocation accounting for the complete joint scheduler. Query classes retain rejected calls. The counter ledger does not treat primitive callbacks or local registry work as free. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The literal shared Server/public operation, when present. Owner and adversary-coin requests have no such operation; they still execute and retain their own replies, callback work and API counts. -/
def serverLabel : Spec.Domain → Option ServerAuthSpec.Domain
  | .inr (.accept raw) => some (.inr (.accept raw))
  | .inr (.build index payload) => some (.inr (.build index payload))
  | .inr (.hmac key message) => some (.inr (.hmac key message))
  | .inr (.hash bytes) => some (.inr (.hash bytes))
  | .inr (.reveal keyId) => some (.inr (.reveal keyId))
  | _ => none

/-- The complete dispatch preserves its actual original Server operation label and full supported Server state. This projection classifies state changes only: unlabelled Beacon and coin requests are not omitted from execution or resource budgets. -/
theorem server_labeled_relation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (relation : Option ServerAuthSpec.Domain → GameState KemSK → GameState KemSK → Prop)
    (cache : ∀ state value, relation none state { state with ctx := value })
    (step : ∀ query state result,
      result ∈ support ((authHandler setup codec checks
        (challenge setup.joint setup.dh serverSeed observationScalar) serverSeed query).run state) →
      relation (some query) state result.2)
    (query : Spec.Domain) (state : State KemSK) (result : Spec.Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    relation (serverLabel query) state.shared.2 result.2.shared.2 := by
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


/-- Every build request, including a missing or consumed handle and every failed writer outcome. -/
def IsBuild (query : Spec.Domain) : Prop :=
  (serverLabel query).elim False PqxdhRegistrationResponse.IsBuild

instance : DecidablePred IsBuild := fun query => by
  unfold IsBuild
  cases serverLabel query <;> dsimp only [Option.elim] <;> infer_instance

/-- Every accept request, including malformed, unauthenticated, replayed and otherwise rejected input. -/
def IsAccept (query : Spec.Domain) : Prop :=
  (serverLabel query).elim False IsAcceptQuery

instance : DecidablePred IsAccept := fun query => by
  unfold IsAccept
  cases serverLabel query <;> dsimp only [Option.elim] <;> infer_instance

/-- Only actual accept calls can add a consumed identity/one-time pair, and one such call adds at most one. Dynamic owner operations retain their full effects but cannot change this Server set. -/
theorem handler_consumed_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (state : State KemSK) (result : Spec.Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    result.2.shared.2.server.consumed.length ≤ state.shared.2.server.consumed.length + if IsAccept query then 1 else 0 := by
  classical
  have bound := server_labeled_relation setup codec checks serverSeed
    (fun label before after => after.server.consumed.length ≤ before.server.consumed.length +
      if label.elim False IsAcceptQuery then 1 else 0)
    (fun _ _ => by simp)
    (fun original before after member => by
      by_cases accepts : IsAcceptQuery original <;>
        simpa only [Option.elim, accepts, ite_true, ite_false] using
          PqxdhRegistrationAdmission.handler_consumed_count setup codec checks
            (challenge setup.joint setup.dh serverSeed observationScalar) serverSeed original before after member)
    query state result supported
  by_cases accepts : IsAccept query <;> simp_all only [IsAccept, ite_true, ite_false]

/-- An all-attempt accept cap bounds consumed-set growth in the complete adaptive joint execution, without dropping unrelated or rejected operations. -/
theorem program_consumed_count {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp Spec Result)
    (qAccept : Nat) (bounded : program.IsQueryBoundP IsAccept qAccept)
    (state : State KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run state)) :
    result.2.shared.2.server.consumed.length ≤ state.shared.2.server.consumed.length + qAccept := by
  exact run_count (handler setup codec checks serverSeed) IsAccept
    (fun current => current.shared.2.server.consumed.length)
    (handler_consumed_count setup codec checks serverSeed) program qAccept bounded state result supported

/-- Every attempted accept allocates at most one new public session index; other capabilities allocate none. This includes all malformed and replayed requests. -/
theorem handler_sessions (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (state : State KemSK) (result : Spec.Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    result.2.shared.2.sessions ≤ state.shared.2.sessions + if IsAccept query then 1 else 0 := by
  classical
  have bound := server_labeled_relation setup codec checks serverSeed
    (fun label before after => after.sessions ≤ before.sessions +
      if label.elim False IsAcceptQuery then 1 else 0)
    (fun _ _ => by simp)
    (fun original before after member => by
      by_cases accepts : IsAcceptQuery original <;>
        simpa only [Option.elim, accepts, ite_true, ite_false] using
          (authHandler_step (Reader := Reader) (Response := Response) codec checks serverSeed original before after member).2.2.1)
    query state result supported
  by_cases accepts : IsAccept query <;> simp_all only [IsAccept, ite_true, ite_false]

/-- Public attempt indices are bounded by all accept requests, including failures, under the complete adaptive joint schedule. -/
theorem program_sessions {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp Spec Result)
    (qAccept : Nat) (bounded : program.IsQueryBoundP IsAccept qAccept)
    (state : State KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run state)) :
    result.2.shared.2.sessions ≤ state.shared.2.sessions + qAccept := by
  exact run_count (handler setup codec checks serverSeed) IsAccept (fun current => current.shared.2.sessions)
    (handler_sessions setup codec checks serverSeed) program qAccept bounded state result supported

/-- The original source's public ID counter can increase only on a build request. The bound counts failed, missing-token and successful build attempts alike. -/
theorem handler_counter_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (state : State KemSK) (result : Spec.Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    result.2.shared.2.server.control.last_key_id.val ≤ state.shared.2.server.control.last_key_id.val +
      if IsBuild query then 1 else 0 := by
  classical
  have bound := server_labeled_relation setup codec checks serverSeed
    (fun label before after => after.server.control.last_key_id.val ≤ before.server.control.last_key_id.val +
      if label.elim False PqxdhRegistrationResponse.IsBuild then 1 else 0)
    (fun _ _ => by simp)
    (fun original before after member => by
      by_cases builds : PqxdhRegistrationResponse.IsBuild original <;>
        simpa only [Option.elim, builds, ite_true, ite_false] using
          PqxdhRegistrationResponse.program_counter_bound setup codec checks
            (challenge setup.joint setup.dh serverSeed observationScalar) serverSeed
            (ServerAuthSpec.query original) (if PqxdhRegistrationResponse.IsBuild original then 1 else 0)
            (by simp [isQueryBoundP_query_iff, builds]) before after
            (by simpa only [simulateQ_spec_query] using member))
    query state result supported
  by_cases builds : IsBuild query <;> simp_all only [IsBuild, ite_true, ite_false]

/-- Successful publication IDs increase by at most the actual all-attempt build allowance across the entire joint schedule. This is independent of the accept and owner-creation allowances. -/
theorem program_counter_bound {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp Spec Result)
    (qBuild : Nat) (bounded : program.IsQueryBoundP IsBuild qBuild)
    (state : State KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run state)) :
    result.2.shared.2.server.control.last_key_id.val ≤ state.shared.2.server.control.last_key_id.val + qBuild := by
  exact run_count (handler setup codec checks serverSeed) IsBuild
    (fun current => current.shared.2.server.control.last_key_id.val)
    (handler_counter_count setup codec checks serverSeed) program qBuild bounded state result supported

end BeaconcryptCore.Computational.PqxdhRegistrationSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.server_labeled_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.server_labeled_relation
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_consumed_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_consumed_count
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_consumed_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_consumed_count
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_sessions
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_sessions
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_counter_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_counter_count
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_counter_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_counter_bound
