import BeaconcryptCore.Computational.PqxdhRegistrationProtocolState
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds
import BeaconcryptCore.Computational.FinitePartitionQueryBounds

/-!
The live record/public/reveal scheduler gains the actual native Beacon Phase2 operation. Its fixed private native handler runs on the same auxiliary state and CTX cache as the original services. Installation changes only the selected Beacon and advances the common API position once. Native finish attempts have their own source-query class, including inactive rejection, and are not inferred from the record raw-attempt counters. This module supplies operational interpretation and resource laws; selected KEM provenance, concrete native leaf contracts and cryptographic reduction instantiation remain separate.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2LiveFinish
open PqxdhBeaconPhase2Preparation (Bytes)

variable {M P I D K X Response A : Type} {S B : Nat}

abbrev State := PqxdhRegistrationProtocolState.State M P I D K A S B
abbrev Shared := RawCtxSharedPrimitive.SharedState A
abbrev NativeSpec := PqxdhBeaconPhase2Publication.NativeSpec I D K X Response

local notation "LiveState" => State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)

inductive Request (beaconCount : Nat) where
  | finish (index : Fin beaconCount) (raw : Bytes)

def FinishSpec (beaconCount : Nat) : OracleSpec (Request beaconCount) := fun _ => Option Bytes
abbrev Spec (serverCount beaconCount : Nat) :=
  RawCtxProtocolReveals.SourceSpec serverCount beaconCount + FinishSpec beaconCount

/-- Publish only the actual selected Beacon and primitive poststate, preserving all other owners and registration fields. -/
def install (index : Fin B) (state : LiveState)
    (updated : RawCtxBeaconLifecycle.State I D K) (primitive : Shared (A := A)) : LiveState :=
  { state with
    roles := ((state.roles.1.1, Function.update state.roles.1.2 index updated), RawCtxProtocolReveals.tick state.roles.2)
    primitive := primitive }

theorem install_fields (index : Fin B) (state : LiveState)
    (updated : RawCtxBeaconLifecycle.State I D K) (primitive : Shared (A := A)) :
    (install index state updated primitive).roles.1.2 index = updated ∧
    (install index state updated primitive).roles.1.1 = state.roles.1.1 ∧
    (install index state updated primitive).controls = state.controls ∧
    (install index state updated primitive).consumed = state.consumed ∧
    (install index state updated primitive).primitive = primitive ∧
    (install index state updated primitive).roles.2.position = state.roles.2.position + 1 ∧
    (install index state updated primitive).roles.2.observations = state.roles.2.observations ∧
    ∀ other, other ≠ index → (install index state updated primitive).roles.1.2 other = state.roles.1.2 other := by
  simp only [install, Function.update_self, RawCtxProtocolReveals.tick, true_and]
  intro other different
  exact Function.update_of_ne different _ _

/-- The original native operation receives the actual selected owner and complete shared state. -/
noncomputable def finishImpl {m : Type → Type} [Monad m]
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)) (StateT (Shared (A := A)) m))
    (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (FinishSpec B) (StateT (LiveState) m) :=
  fun request => StateT.mk fun state => match request with
  | .finish index raw => do
      let result ← (simulateQ native (PqxdhBeaconPhase2Publication.nativeOwner decode raw (state.roles.1.2 index))).run state.primitive
      pure (result.1.1, install index state result.1.2 result.2)

noncomputable def liveImpl {m : Type → Type} [Monad m]
    (old : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (LiveState) m))
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)) (StateT (Shared (A := A)) m))
    (decode : RawCtxReceive.FrameDecoder) : QueryImpl (Spec S B) (StateT LiveState m)
  | .inl query => old query
  | .inr query => finishImpl native decode query

/-- Concrete old requests use the unchanged source services and their existing reveal history. -/
noncomputable def sourceImpl
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)) (StateT (Shared (A := A)) ProbComp)) :
    QueryImpl (Spec S B) (StateT (LiveState) ProbComp) :=
  liveImpl (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode) native decode

/-- Interpreting native callbacks preserves the complete actual owner installation and shared primitive state. -/
theorem finish_interpretation {ι : Type} {base : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : QueryImpl base m)
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response))
      (StateT (Shared (A := A)) (OracleComp base))) (decode : RawCtxReceive.FrameDecoder) :
    interpret.mapStateTBase (finishImpl (M := M) (P := P) (S := S) (B := B) native decode) =
      finishImpl (interpret.mapStateTBase native) decode := by
  funext query state
  cases query with
  | finish index raw =>
    change simulateQ interpret (do
      let result ← (simulateQ native (PqxdhBeaconPhase2Publication.nativeOwner decode raw (state.roles.1.2 index))).run state.primitive
      pure (result.1.1, install index state result.1.2 result.2)) = (do
      let result ← (simulateQ (interpret.mapStateTBase native)
        (PqxdhBeaconPhase2Publication.nativeOwner decode raw (state.roles.1.2 index))).run state.primitive
      pure (result.1.1, install index state result.1.2 result.2))
    simp only [bind_pure_comp, simulateQ_map, QueryImpl.simulateQ_mapStateTBase_run]

/-- Both original and new source operations commute with the same actual interpreter. -/
theorem live_interpretation {ι : Type} {base : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : QueryImpl base m)
    (old : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (LiveState) (OracleComp base)))
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response))
      (StateT (Shared (A := A)) (OracleComp base))) (decode : RawCtxReceive.FrameDecoder) :
    interpret.mapStateTBase (liveImpl old native decode) =
      liveImpl (interpret.mapStateTBase old) (interpret.mapStateTBase native) decode := by
  funext query
  cases query with
  | inl query => rfl
  | inr query => exact congrFun (finish_interpretation interpret native decode) query

/-- The arbitrary adaptive continuation preserves its exact result and full live state, including the common cache. -/
theorem live_schedule {ι : Type} {base : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m] {Result : Type}
    (interpret : QueryImpl base m)
    (old : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (LiveState) (OracleComp base)))
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response))
      (StateT (Shared (A := A)) (OracleComp base))) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Spec S B) Result) (state : LiveState) :
    simulateQ interpret ((simulateQ (liveImpl old native decode) client).run state) =
      (simulateQ (liveImpl (interpret.mapStateTBase old) (interpret.mapStateTBase native) decode) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, live_interpretation]

/-- Existing source operations execute their original handler, including its actual tick or reveal note. -/
theorem source_old
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)) (StateT (Shared (A := A)) ProbComp))
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) :
    sourceImpl (P := P) source writer senderId route decode native (.inl query) =
      PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode query := rfl

/-- Finish uses the actual selected live owner and then installs its complete optional outcome. -/
theorem source_finish
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)) (StateT (Shared (A := A)) ProbComp))
    (index : Fin B) (raw : Bytes) (state : LiveState) :
    (sourceImpl source writer senderId route decode native (.inr (.finish index raw))).run state =
      (do
        let result ← (simulateQ native (PqxdhBeaconPhase2Publication.nativeOwner decode raw (state.roles.1.2 index))).run state.primitive
        pure (result.1.1, install index state result.1.2 result.2)) := rfl

/-- Native Phase2's internal raw opening does not increment the outer record-attempt counter, on either successful or failed completion. -/
theorem native_raw_attempts
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)) (StateT (Shared (A := A)) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state next : RawCtxBeaconLifecycle.State I D K)
    (primitive final : Shared (A := A)) (reply : Option Bytes)
    (present : ((reply, next), final) ∈ support
      ((simulateQ native (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run primitive)) :
    next.rawAttempts = state.rawAttempts := by
  cases reply with
  | none =>
      have failed := PqxdhBeaconPhase2Publication.native_failure native decode raw state next primitive final present
      cases active : state.beacon.phase <;> simp only [active] at failed
      case initSent control prekey oneTime kem => rw [failed]; rfl
      all_goals rw [failed.1]
  | some plaintext =>
      obtain ⟨staged, _, _, published⟩ :=
        PqxdhBeaconPhase2Publication.native_success native decode raw plaintext state next primitive final present
      exact (congrArg (fun result => result.2.rawAttempts) published).symm

/-- Every supported finish result retains its exact native execution witness and unchanged outer raw-attempt counter. -/
theorem finish_supported
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)) (StateT (Shared (A := A)) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (index : Fin B) (raw : Bytes) (state : LiveState)
    (result : Option Bytes × LiveState)
    (present : result ∈ support ((finishImpl native decode (.finish index raw)).run state)) :
    ∃ updated primitive,
      ((result.1, updated), primitive) ∈ support
        ((simulateQ native (PqxdhBeaconPhase2Publication.nativeOwner decode raw (state.roles.1.2 index))).run state.primitive) ∧
      result.2 = install index state updated primitive ∧
      updated.rawAttempts = (state.roles.1.2 index).rawAttempts := by
  simp only [finishImpl, StateT.run_mk, bind_pure_comp, support_map] at present
  obtain ⟨⟨⟨reply, updated⟩, primitive⟩, supported, rfl⟩ := present
  exact ⟨updated, primitive, supported, rfl,
    native_raw_attempts native decode raw _ _ _ _ reply supported⟩

/-- Each finish call retains the actual native 69-callback upper bound, including inactive attempts and work before sequence-one rejection. -/
theorem finish_query_bound {ι : Type} {base : OracleSpec ι}
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response))
      (StateT (Shared (A := A)) (OracleComp base))) (decode : RawCtxReceive.FrameDecoder)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qCall : Nat)
    (bounded : ∀ query primitive, ((native query).run primitive).IsQueryBoundP predicate qCall)
    (request : (FinishSpec B).Domain) (state : LiveState) :
    ((finishImpl native decode request).run state).IsQueryBoundP predicate (69 * qCall) := by
  cases request with
  | finish index raw =>
    simp only [finishImpl, StateT.run_mk, bind_pure_comp, isQueryBoundP_map_iff]
    exact PqxdhBeaconPhase2Bounds.native_interpreted_bound native predicate qCall bounded decode raw _ _

/-- Original operations and finish attempts have separate all-reply source caps; finish work is never derived from a record-attempt counter. -/
theorem live_query_bound {ι : Type} {base : OracleSpec ι} {Result : Type}
    (old : QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (StateT LiveState (OracleComp base)))
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response))
      (StateT (Shared (A := A)) (OracleComp base))) (decode : RawCtxReceive.FrameDecoder)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qOld qFinish qOldCost qCall : Nat)
    (oldCost : ∀ query state, ((old query).run state).IsQueryBoundP predicate qOldCost)
    (nativeCost : ∀ query primitive, ((native query).run primitive).IsQueryBoundP predicate qCall)
    (client : OracleComp (Spec S B) Result)
    (oldCount : client.IsQueryBoundP (fun query => query.isRight = false) qOld)
    (finishCount : client.IsQueryBoundP (fun query => query.isRight = true) qFinish) (state : LiveState) :
    ((simulateQ (liveImpl old native decode) client).run state).IsQueryBoundP predicate
      (qOldCost * qOld + 69 * qCall * qFinish) := by
  let cost : Bool → Nat := fun finish => if finish then 69 * qCall else qOldCost
  let budget : Bool → Nat := fun finish => if finish then qFinish else qOld
  have bounded : ∀ kind, client.IsQueryBoundP (fun query => query.isRight = kind) (budget kind) := by
    intro kind
    cases kind
    · exact oldCount
    · exact finishCount
  have step : ∀ query state, (((liveImpl old native decode) query).run state).IsQueryBoundP predicate (cost query.isRight) := by
    intro query state
    cases query with
    | inl query => exact oldCost query state
    | inr query => exact finish_query_bound native decode predicate qCall nativeCost query state
  have counted := FinitePartitionQueryBounds.weighted_bound (fun query => query.isRight) cost budget
    (liveImpl old native decode) predicate client bounded step state
  simpa only [Fintype.sum_bool, cost, budget, Bool.false_eq_true, ite_false, ite_true, Nat.add_comm] using counted

/-- Every original source operation preserves registration fields and advances the existing history exactly once. -/
theorem old_step_history
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : LiveState)
    (result : (RawCtxProtocolReveals.SourceSpec S B).Range query × LiveState)
    (present : result ∈ support
      ((PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode query).run state)) :
    result.2.controls = state.controls ∧ result.2.consumed = state.consumed ∧
    result.2.roles.2.position = state.roles.2.position + 1 ∧
    ∃ suffix, result.2.roles.2.observations = state.roles.2.observations ++ suffix ∧ suffix.length ≤ 1 := by
  cases query with
  | inl query =>
      simp only [PqxdhRegistrationProtocolState.sourceImpl, RawCtxProtocolReveals.sourceImpl,
        StateT.run, PqxdhRegistrationProtocolState.project, mem_support_bind_iff, mem_support_pure_iff] at present
      obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := present
      exact ⟨rfl, rfl, rfl, [], by simp [PqxdhRegistrationProtocolState.restore, RawCtxProtocolReveals.tick]⟩
  | inr query =>
      simp only [PqxdhRegistrationProtocolState.sourceImpl, RawCtxProtocolReveals.sourceImpl,
        StateT.run, PqxdhRegistrationProtocolState.project, pure_bind, mem_support_pure_iff] at present
      subst result
      exact ⟨rfl, rfl, rfl, [(state.roles.2.position, ⟨query, RawCtxProtocolReveals.reveal query state.roles.1⟩)], rfl, by simp⟩

/-- Every supported live operation, including an inactive finish, advances one position and preserves the actual prior reveal history. -/
theorem source_step_history
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)) (StateT (Shared (A := A)) ProbComp))
    (query : (Spec S B).Domain) (state : LiveState) (result : (Spec S B).Range query × LiveState)
    (present : result ∈ support ((sourceImpl source writer senderId route decode native query).run state)) :
    result.2.controls = state.controls ∧ result.2.consumed = state.consumed ∧
    result.2.roles.2.position = state.roles.2.position + 1 ∧
    ∃ suffix, result.2.roles.2.observations = state.roles.2.observations ++ suffix ∧ suffix.length ≤ 1 := by
  cases query with
  | inl query => exact old_step_history source writer senderId route decode query state result present
  | inr query =>
      cases query with
      | finish index raw =>
        obtain ⟨updated, primitive, _, equal, _⟩ := finish_supported native decode index raw state result present
        rw [equal]
        exact ⟨rfl, rfl, rfl, [], by simp [install, RawCtxProtocolReveals.tick]⟩

/-- The full supported adaptive schedule preserves registration fields and the actual history prefix, with every finish charged as one source operation. -/
theorem source_schedule_history {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)) (StateT (Shared (A := A)) ProbComp))
    (client : OracleComp (Spec S B) Result) (budget : Nat) (bounded : client.IsTotalQueryBound budget)
    (state : LiveState) (result : Result × LiveState)
    (present : result ∈ support ((simulateQ (sourceImpl source writer senderId route decode native) client).run state)) :
    result.2.controls = state.controls ∧ result.2.consumed = state.consumed ∧
    result.2.roles.2.position ≤ state.roles.2.position + budget ∧
    ∃ suffix, result.2.roles.2.observations = state.roles.2.observations ++ suffix ∧ suffix.length ≤ budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at present
      subst result
      exact ⟨rfl, rfl, Nat.le_add_right _ _, [], by simp⟩
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at present
      obtain ⟨reply, supported, continued⟩ := present
      obtain ⟨controlsStep, consumedStep, positionStep, firstLog, prefixEq, prefixLength⟩ :=
        source_step_history source writer senderId route decode native query state reply supported
      obtain ⟨controlsTail, consumedTail, positionTail, tailLog, tailEq, tailLength⟩ :=
        ih reply.1 (budget - 1) (bounded.2 reply.1) reply.2 result continued
      refine ⟨controlsTail.trans controlsStep, consumedTail.trans consumedStep, by omega,
        firstLog ++ tailLog, ?_, ?_⟩
      · rw [tailEq, prefixEq, List.append_assoc]
      · simp only [List.length_append]
        omega

/-- A proved family predicate transports through the full live schedule when the original steps and actual native installation preserve it. The preservation premises refer to supported original executions, not chosen successful candidates. -/
theorem live_invariant {Result : Type}
    (old : QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (StateT LiveState ProbComp))
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response))
      (StateT (Shared (A := A)) ProbComp)) (decode : RawCtxReceive.FrameDecoder)
    (invariant : LiveState → Prop)
    (oldPreserves : ∀ query state result, invariant state →
      result ∈ support ((old query).run state) → invariant result.2)
    (finishPreserves : ∀ index raw state result, invariant state →
      result ∈ support ((simulateQ native
        (PqxdhBeaconPhase2Publication.nativeOwner decode raw (state.roles.1.2 index))).run state.primitive) →
      invariant (install index state result.1.2 result.2))
    (client : OracleComp (Spec S B) Result) (state : LiveState) (before : invariant state)
    (result : Result × LiveState)
    (present : result ∈ support ((simulateQ (liveImpl old native decode) client).run state)) :
    invariant result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at present
      subst result
      exact before
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at present
      obtain ⟨reply, supported, continued⟩ := present
      have preserved : invariant reply.2 := by
        cases query with
        | inl query => exact oldPreserves query state reply before supported
        | inr query =>
          cases query with
          | finish index raw =>
            obtain ⟨updated, primitive, nativeSupported, equal, _⟩ :=
              finish_supported native decode index raw state reply supported
            rw [equal]
            exact finishPreserves index raw state ((reply.1, updated), primitive) before nativeSupported
      exact ih reply.1 reply.2 preserved result continued

end BeaconcryptCore.Computational.PqxdhPhase2LiveFinish

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.install_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.install_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.finish_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.finish_interpretation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.live_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.live_interpretation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.live_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.live_schedule

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.source_old' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.source_old

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.source_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.source_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.native_raw_attempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.native_raw_attempts

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.finish_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.finish_supported

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.finish_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.finish_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.live_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.live_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.old_step_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.old_step_history

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.source_step_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.source_step_history

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.source_schedule_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.source_schedule_history

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.live_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.live_invariant
