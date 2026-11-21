import BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler
import BeaconcryptCore.Computational.RawCtxChainOwner

/-!
The original raw frontend is retained around the opaque-chain/shared-CTX receive compiler. Raw bytes, parser/pin/shape rejection, whole-kernel publication, immutable metadata and the outer API-attempt counter are unchanged. Source attempts and primitive verification attempts are distinct: every API call increments once, while early rejection issues no component query. Arbitrary adaptive raw schedules retain separate bounds of 51q derivations and q opening calls, including all rejected attempts. No ambient derivation is free, and no independent-key or secrecy premise is introduced.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSharedReceiveOwner
open RawCtxSharedReceiveCompiler RawCtxChainOwner

abbrev Kernel (Send Chain : Type) (count : Nat) := RefinedRatchet Send Chain (Label count)
abbrev Owner (Send Chain Metadata : Type) (count : Nat) := State (Kernel Send Chain count) Metadata

/-- Exactly the original source raw gates and publication, around the compiled receive driver. -/
noncomputable def raw {Send Chain Metadata : Type} {count : Nat}
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) :
    StateT (Owner Send Chain Metadata count) (OracleComp (Spec Chain count))
      (core.option.Option RawCtxWholeOwner.Decrypted) := fun state =>
  if bytes.isEmpty then pure (publish state (state.kernel, .None)) else
  match read bytes with
  | none => pure (publish state (state.kernel, .None))
  | some frame =>
    if RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame then do
      let result ← receive state.kernel frame.sequence ⟨bytes, frame, state.associatedData⟩
      pure (publish state result)
    else pure (publish state (state.kernel, .None))

/-- The frontend is the existing source owner definition; the unused send callback is never evaluated. -/
theorem raw_frontend {Send Chain Metadata : Type} {count : Nat}
    (send : Kernel Send Chain count → RawCtxSourceSend.SealContext →
      OracleComp (Spec Chain count) (Kernel Send Chain count × Option RawCtxSourceSend.Encrypted))
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (state : Owner Send Chain Metadata count) :
    (raw read bytes).run state =
      (RawCtxChainOwner.rawReceive ⟨receive, send⟩ read bytes).run state := rfl

/-- Every original early-rejection branch pays zero derivations and zero component openings. -/
theorem raw_bound {Send Chain Metadata : Type} {count : Nat}
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (state : Owner Send Chain Metadata count)
    (kdf : Bool) :
    ((raw read bytes).run state).IsQueryBoundP (Resource kdf) (if kdf then 51 else 1) := by
  unfold raw StateT.run
  split
  · trivial
  · cases decoded : read bytes with
    | none => trivial
    | some frame =>
      simp only
      split
      · simp only [bind_pure_comp, isQueryBoundP_map_iff]
        cases kdf with
        | true => exact receive_kdf state.kernel frame.sequence _
        | false => exact receive_raw state.kernel frame.sequence _
      · trivial

/-- Arbitrary raw input and actual optional replies use one complete private owner between calls. -/
noncomputable def ownerImpl {Send Chain Metadata : Type} {count : Nat}
    (read : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxWholeOwner.RawSpec (StateT (Owner Send Chain Metadata count) (OracleComp (Spec Chain count))) :=
  raw read

/-- Every finite adaptive raw schedule retains both source-derived primitive ledgers. -/
theorem schedule_bound {Send Chain Metadata Result : Type} {count : Nat}
    (read : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (qRaw : Nat) (bounded : client.IsTotalQueryBound qRaw) (state : Owner Send Chain Metadata count)
    (kdf : Bool) :
    ((simulateQ (ownerImpl read) client).run state).IsQueryBoundP (Resource kdf)
      ((if kdf then 51 else 1) * qRaw) := by
  induction client using OracleComp.inductionOn generalizing qRaw state with
  | pure value => simp
  | query_bind bytes next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
    have tail := fun (result : core.option.Option RawCtxWholeOwner.Decrypted × Owner Send Chain Metadata count) => ih result.1 (qRaw - 1) (bounded.2 result.1) result.2
    have total := isQueryBoundP_bind (raw_bound read bytes state kdf) (fun result _ => tail result)
    apply total.mono
    have positive := bounded.1
    cases kdf <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- Every possible raw result publishes exactly one complete kernel and its actual optional reply. -/
theorem raw_publication {Send Chain Metadata : Type} {count : Nat}
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (state : Owner Send Chain Metadata count)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × Owner Send Chain Metadata count)
    (actual : result ∈ support ((raw read bytes).run state)) :
    ∃ kernel reply, result = publish state (kernel, reply) := by
  unfold raw StateT.run at actual
  split at actual
  · obtain rfl := eq_of_mem_support_pure actual
    exact ⟨_, _, rfl⟩
  · cases decoded : read bytes with
    | none =>
      simp only [decoded] at actual
      obtain rfl := eq_of_mem_support_pure actual
      exact ⟨_, _, rfl⟩
    | some frame =>
      simp only [decoded] at actual
      split at actual
      · rw [mem_support_bind_iff] at actual
        obtain ⟨received, _, returned⟩ := actual
        obtain rfl := eq_of_mem_support_pure returned
        exact ⟨received.1, received.2, rfl⟩
      · obtain rfl := eq_of_mem_support_pure actual
        exact ⟨_, _, rfl⟩

/-- Every API attempt increments once, including parse/validation/preparation failure; immutable metadata remains exact. -/
theorem raw_attempt {Send Chain Metadata : Type} {count : Nat}
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (state : Owner Send Chain Metadata count)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × Owner Send Chain Metadata count)
    (actual : result ∈ support ((raw read bytes).run state)) :
    result.2.rawAttempts = state.rawAttempts + 1 ∧ result.2.expectedSender = state.expectedSender ∧
      result.2.associatedData = state.associatedData ∧ result.2.metadata = state.metadata := by
  obtain ⟨kernel, reply, rfl⟩ := raw_publication read bytes state result actual
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The outer source ledger counts all adaptive API calls, while primitive ledgers can be strictly smaller. -/
theorem schedule_attempts {Send Chain Metadata Result : Type} {count : Nat}
    (read : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (qRaw : Nat) (bounded : client.IsTotalQueryBound qRaw) (state : Owner Send Chain Metadata count)
    (result : Result × Owner Send Chain Metadata count)
    (actual : result ∈ support ((simulateQ (ownerImpl read) client).run state)) :
    result.2.rawAttempts ≤ state.rawAttempts + qRaw ∧ result.2.expectedSender = state.expectedSender ∧
      result.2.associatedData = state.associatedData ∧ result.2.metadata = state.metadata := by
  induction client using OracleComp.inductionOn generalizing qRaw state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at actual
    subst result
    exact ⟨Nat.le_add_right _ _, rfl, rfl, rfl⟩
  | query_bind bytes next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at actual
    obtain ⟨step, called, later⟩ := actual
    have first := raw_attempt read bytes state step called
    have rest := ih step.1 (qRaw - 1) (bounded.2 step.1) step.2 result later
    exact ⟨by omega, rest.2.1.trans first.2.1, rest.2.2.1.trans first.2.2.1,
      rest.2.2.2.trans first.2.2.2⟩

end BeaconcryptCore.Computational.RawCtxSharedReceiveOwner

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.raw_frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.raw_frontend

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.raw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.raw_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.schedule_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.schedule_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.raw_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.raw_publication

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.raw_attempt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.raw_attempt

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.schedule_attempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveOwner.schedule_attempts
