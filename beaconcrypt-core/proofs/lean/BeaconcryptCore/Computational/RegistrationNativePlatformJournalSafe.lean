-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformJournalWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
/-! Every actual source hash/sign request preserves cached chronological ML receipts and a cached last hash cut. The invariant transports through the trusted lifted uniform interpreter with the exact external state, then through arbitrary adaptive Ed/writer capabilities whose literal source frame leaves ML receipts unchanged and extends the cache. Failed signatures and source publication prefixes remain counted; no whole-publication Cached premise is supplied. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe
open RegistrationNativePlatformSigningJournal (State Cut source)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
variable {n : Nat}
abbrev coins : QueryImpl unifSpec ProbComp := QueryImpl.id' unifSpec

def Last (before : State n) : Prop :=
  ∀ cut, before.2 = some cut → before.1.1.primitive.2 ((), hashBytes cut.request) = some cut.digest

def Safe (before : State n) : Prop :=
  RegistrationSigningShared.Cached (RegistrationWorldSigning.project before.1) ∧ Last before

variable (primitive : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)

private theorem world_hash (request : registration.HashRequest) (before : RegistrationWorldSigning.State n)
    (cached : RegistrationSigningShared.Cached (RegistrationWorldSigning.project before))
    (result : CtxRomAuth.CtxDigest × RegistrationWorldSigning.State n)
    (supported : result ∈ support ((RegistrationWorldSigning.outgoing primitive (.hash request)).run before)) :
    RegistrationSigningShared.Cached (RegistrationWorldSigning.project result.2) ∧
      before.1.primitive.2 ≤ result.2.1.primitive.2 ∧ result.2.1.primitive.2 ((), hashBytes request) = some result.1 := by
  have projected : (result.1, RegistrationWorldSigning.project result.2) ∈ support
      ((RegistrationSigningShared.implementation primitive (.hash request)).run (RegistrationWorldSigning.project before)) := by
    rw [← RegistrationWorldSigning.outgoing_project, support_map]
    exact ⟨result, supported, rfl⟩
  exact ⟨RegistrationSigningShared.hash_cached_state primitive request _ cached _ projected,
    RegistrationSigningShared.hash_cached primitive request _ _ projected⟩

private theorem world_sign (request : registration.MldsaSigningRequest)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (before : RegistrationWorldSigning.State n)
    (cached : RegistrationSigningShared.Cached (RegistrationWorldSigning.project before))
    (reached : before.1.primitive.2 ((), payload.transcript) = some digest)
    (result : RegistrationSigningShared.SignReply × RegistrationWorldSigning.State n)
    (supported : result ∈ support ((RegistrationWorldSigning.outgoing primitive (.sign request payload digest)).run before)) :
    RegistrationSigningShared.Cached (RegistrationWorldSigning.project result.2) ∧ result.2.1.primitive.2 = before.1.primitive.2 := by
  have projected : (result.1, RegistrationWorldSigning.project result.2) ∈ support
      ((RegistrationSigningShared.implementation primitive (.sign request payload digest)).run (RegistrationWorldSigning.project before)) := by
    rw [← RegistrationWorldSigning.outgoing_project, support_map]
    exact ⟨result, supported, rfl⟩
  refine ⟨RegistrationSigningShared.sign_cached primitive request payload digest _ cached reached _ projected, ?_⟩
  rw [RegistrationSigningShared.signing_step] at projected
  obtain ⟨reply, _possible, same⟩ := OracleComp.mem_support_map_peel _ _ projected
  exact congrArg (fun item : RegistrationSigningShared.SignReply × RegistrationSigningShared.State => item.2.2) same

theorem hash (request : registration.HashRequest) (before : State n) (safe : Safe before)
    (result : CtxRomAuth.CtxDigest × State n)
    (supported : result ∈ support ((RegistrationNativePlatformSigningJournal.hash coins primitive request).run before)) : Safe result.2 := by
  rw [RegistrationNativePlatformSigningJournal.hash_run] at supported
  simp only [coins, simulateQ_id', support_map] at supported
  obtain ⟨inner, queried, same⟩ := supported
  cases same
  obtain ⟨cached, _extends, recorded⟩ := world_hash primitive request before.1 safe.1 inner queried
  refine ⟨cached, ?_⟩
  intro cut equal
  cases equal
  exact recorded

theorem sign (request : registration.MldsaSigningRequest) (before : State n) (safe : Safe before)
    (result : RegistrationSigningShared.SignReply × State n)
    (supported : result ∈ support ((RegistrationNativePlatformSigningJournal.sign coins primitive request).run before)) : Safe result.2 := by
  rcases before with ⟨before, previous⟩
  cases previous with
  | none =>
      simp only [RegistrationNativePlatformSigningJournal.sign, StateT.run, coins, simulateQ_id', support_map] at supported
      obtain ⟨inner, sampled, same⟩ := supported
      cases same
      simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at sampled
      obtain ⟨counted, _possible, same⟩ := sampled
      cases same
      exact ⟨safe.1, by intro cut impossible; cases impossible⟩
  | some cut =>
      rw [RegistrationNativePlatformSigningJournal.sign_cut] at supported
      simp only [coins, simulateQ_id', support_map] at supported
      obtain ⟨inner, sampled, same⟩ := supported
      cases same
      obtain ⟨cached, cache⟩ := world_sign primitive request (cut.payload request.role) cut.digest before safe.1 (safe.2 cut rfl) inner sampled
      refine ⟨cached, ?_⟩
      intro selected equal
      cases equal
      simpa only [cache] using safe.2 cut rfl

theorem query (query : RegistrationSigningShared.Spec.Domain) (before : State n) (safe : Safe before)
    (result : RegistrationSigningShared.Spec.Range query × State n)
    (supported : result ∈ support ((source coins primitive query).run before)) : Safe result.2 := by
  cases query with
  | hash request => exact hash primitive request before safe result supported
  | sign request payload digest => exact sign primitive request before safe result supported

theorem interpreted {m : Type → Type} [Monad m] [LawfulMonad m]
    (implementation : QueryImpl unifSpec m) (query : RegistrationSigningShared.Spec.Domain) :
    RegistrationNativePlatformInterpret.state implementation (source (n := n) coins primitive query) =
      source implementation primitive query := by
  funext before
  change simulateQ implementation ((source coins primitive query).run before) = (source implementation primitive query).run before
  cases query with
  | hash request =>
      simp only [source]
      rw [RegistrationNativePlatformSigningJournal.hash_run, RegistrationNativePlatformSigningJournal.hash_run]
      simp only [coins, simulateQ_id', simulateQ_map]
  | sign request payload digest =>
      rcases before with ⟨before, previous⟩
      cases previous with
      | none =>
          simp only [source, RegistrationNativePlatformSigningJournal.sign, StateT.run, coins, simulateQ_id', simulateQ_map]
      | some cut =>
          simp only [source]
          rw [RegistrationNativePlatformSigningJournal.sign_cut, RegistrationNativePlatformSigningJournal.sign_cut]
          simp only [coins, simulateQ_id', simulateQ_map]

theorem lifted {Auxiliary : Type} (query : RegistrationSigningShared.Spec.Domain) (before : State n)
    (safe : Safe before) (previous : Auxiliary)
    (result : (RegistrationSigningShared.Spec.Range query × State n) × Auxiliary)
    (supported : result ∈ support (((source RegistrationNativePlatformMldsaProgram.coins primitive query).run before).run previous)) : Safe result.1.2 := by
  have law := congrFun (congrFun (interpreted (n := n) primitive
    (RegistrationNativePlatformMldsaProgram.coins (Platform := Auxiliary)) query) before) previous
  simp only [RegistrationNativePlatformInterpret.state, StateT.run, RegistrationNativePlatformMldsaProgram.lift_coins] at law
  simp only [StateT.run] at supported
  rw [← law] at supported
  simp only [StateT.lift, bind_pure_comp, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  exact RegistrationNativePlatformJournalSafe.query primitive query before safe inner reached

def Frame (before after : RegistrationWorldSigning.State n) : Prop :=
  before.2 = after.2 ∧ before.1.primitive.2 ≤ after.1.primitive.2

theorem frame (before after : RegistrationWorldSigning.State n) (cut : Option RegistrationNativePlatformSigningJournal.Cut)
    (safe : Safe (before, cut)) (preserved : Frame before after) : Safe (after, cut) := by
  refine ⟨?_, ?_⟩
  · change RegistrationSigningShared.Cached (after.2, after.1.primitive.2)
    rw [← preserved.1]
    exact RegistrationSigningShared.cached_extend before.2 _ _ preserved.2 safe.1
  · intro selected present
    exact preserved.2 (safe.2 selected present)

variable {I Auxiliary Value : Type} {extra : OracleSpec I}

noncomputable def handler (side : QueryImpl extra (StateT (RegistrationWorldSigning.State n) (StateT Auxiliary ProbComp))) :
    QueryImpl (RegistrationNativePlatformJournalErasure.Spec extra) (StateT (State n) (StateT Auxiliary ProbComp))
  | .inl query => source RegistrationNativePlatformMldsaProgram.coins primitive query
  | .inr query => RegistrationNativePlatformJournalErasure.liftWorld (side query)

theorem side (work : StateT (RegistrationWorldSigning.State n) (StateT Auxiliary ProbComp) Value)
    (preserved : ∀ before previous result, result ∈ support ((work.run before).run previous) → Frame before result.1.2)
    (before : State n) (safe : Safe before) (previous : Auxiliary)
    (result : (Value × State n) × Auxiliary)
    (supported : result ∈ support (((RegistrationNativePlatformJournalErasure.liftWorld work).run before).run previous)) : Safe result.1.2 := by
  change result ∈ support (((fun result => (result.1, (result.2, before.2))) <$> work.run before.1).run previous) at supported
  rw [StateT.run_map] at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  exact frame before.1 inner.1.2 before.2 safe (preserved before.1 previous inner reached)

theorem program (side : QueryImpl extra (StateT (RegistrationWorldSigning.State n) (StateT Auxiliary ProbComp)))
    (preserved : ∀ query before previous result, result ∈ support (((side query).run before).run previous) → Frame before result.1.2)
    (work : OracleComp (RegistrationNativePlatformJournalErasure.Spec extra) Value)
    (before : State n) (safe : Safe before) (previous : Auxiliary)
    (result : (Value × State n) × Auxiliary)
    (supported : result ∈ support (((simulateQ (handler primitive side) work).run before).run previous)) : Safe result.1.2 := by
  induction work using OracleComp.inductionOn generalizing before previous result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact safe
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      apply ih middle.1.1 middle.1.2 _ middle.2 result continued
      cases query with
      | inl query => exact lifted primitive query before safe previous middle reached
      | inr query => exact RegistrationNativePlatformJournalSafe.side (side query) (preserved query) before safe previous middle reached
end BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.sign

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.interpreted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.lifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.lifted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.side' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.side

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe.program
