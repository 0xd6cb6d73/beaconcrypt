import BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared

/-!
Opaque-shared Phase2 accounting follows the actual query syntax under every typed reply. It needs no byte interpretation or callback realization: twelve collection callbacks, one temporary erasure, one private root, one typed64 initializer, one app getter and at most 53 expanded raw callbacks give the same 69-call allowance. Later sequence rejection retains all preceding receive work. Separate all-reply classifiers give at most one original decapsulation and one private root request per attempt. Per-callback codec, primitive and local reconstruction costs remain explicit; these syntax bounds do not assume primitive correctness or establish KDF freshness, live-compromise security or a global reduction. Storage, snapshots and restoration are excluded.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds
open PqxdhBeaconPhase2Shared
open PqxdhBeaconPhase2Preparation (Bytes Word32 State)
open PqxdhBeaconPhase2Bounds (simulate_total)

/-- The opaque reply changes neither the original twelve collection sites nor their optional short circuits. -/
theorem collect_bound {I D K X Response Shared : Type} (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    (collect (X := X) (Response := Response) (Shared := Shared) identity prekey oneTime kem raw).IsTotalQueryBound 12 := by
  unfold collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | rw [isTotalQueryBound_query_bind_iff]
    | constructor
    | intro reply; cases reply

/-- Temporary shared-output erasure remains one actual effect on either core admission outcome. -/
theorem afterInputs_bound {I D K X Response Shared : Type} (control : pqxdh.BeaconInitSent) (inputs : Inputs Response Shared) :
    (afterInputs (I := I) (D := D) (K := K) (X := X) control inputs).IsTotalQueryBound 1 := by
  unfold afterInputs
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

/-- The complete pre-root collection and admission cost at most thirteen callbacks without any successful-reply premise. -/
theorem prepare_bound {I D K X Response Shared : Type} (control : pqxdh.BeaconInitSent)
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    (prepare (X := X) (Response := Response) (Shared := Shared) control identity prekey oneTime kem raw).IsTotalQueryBound 13 := by
  unfold prepare
  apply isTotalQueryBound_bind (collect_bound identity prekey oneTime kem raw) (n₂ := 1)
  intro result
  cases result with
  | none => trivial
  | some inputs => exact afterInputs_bound control inputs

/-- The exact post-root program retains the initial64/app queries and at most 51 KDF plus one hash and one AEAD call. -/
theorem afterRoot_bound {Response Shared : Type} (decode : RawCtxReceive.FrameDecoder)
    (pending : Prepared Response Shared) (root : Word32) :
    (afterRoot decode pending root).IsTotalQueryBound 55 := by
  unfold afterRoot
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun response => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some raw =>
      simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      apply simulate_total rawLift _ 53 (PqxdhBeaconPhase2Bounds.native_raw_total _ _ _)
      intro query
      exact (isQueryBoundP_true_iff _ _).mp
        ((isQueryBoundP_query_iff (spec := TailSpec Response Shared) (p := fun _ => True) (.inl query) 1).mpr (by decide))

/-- A single private root callback precedes the full post-root allowance, including all optional rejection paths. -/
theorem tail_bound {Response Shared : Type} (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) :
    (tail decode pending).IsTotalQueryBound 56 := by
  unfold tail
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some root => exact afterRoot_bound decode pending root

/-- Every active or inactive native-shaped Phase2 call retains the complete 69-callback bound without materializing the opaque secret. -/
theorem owner_bound {I D K X Response Shared : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K) :
    (owner (X := X) (Response := Response) (Shared := Shared) decode raw state).IsTotalQueryBound 69 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [owner, active]
      apply isTotalQueryBound_bind (n₁ := 13) (n₂ := 56)
      · apply simulate_total preLift _ 13 (prepare_bound _ _ _ _ _ _)
        intro query
        exact (isQueryBoundP_true_iff _ _).mp
          ((isQueryBoundP_query_iff (spec := FullSpec I D K X Response Shared) (p := fun _ => True) (.inl query) 1).mpr (by decide))
      · intro reply
        cases reply with
        | none => trivial
        | some pending =>
            simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
            apply simulate_total tailLift _ 56 (tail_bound _ _)
            intro query
            exact (isQueryBoundP_true_iff _ _).mp
              ((isQueryBoundP_query_iff (spec := FullSpec I D K X Response Shared) (p := fun _ => True) (.inr query) 1).mpr (by decide))
  | _ => simp only [owner, active]; trivial

/-- Every selected underlying callback bill is charged on the actual opaque implementation, without access to a byte realization. -/
theorem interpreted_bound {I D K X Response Shared Auxiliary ι : Type} {base : OracleSpec ι}
    (handler : QueryImpl (FullSpec I D K X Response Shared) (StateT Auxiliary (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qCall : Nat)
    (step : ∀ query auxiliary, ((handler query).run auxiliary).IsQueryBoundP predicate qCall)
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) (auxiliary : Auxiliary) :
    ((simulateQ handler (owner decode raw state)).run auxiliary).IsQueryBoundP predicate (69 * qCall) :=
  PqxdhBeaconPhase2Bounds.interpreted_total_bound handler predicate qCall 69 step _ (owner_bound decode raw state) auxiliary

/-- A following private computation retains the complete actual owner and callback poststate and pays its own selected query allowance. -/
theorem continuation_bound {I D K X Response Shared Auxiliary Result ι : Type} {base : OracleSpec ι}
    (handler : QueryImpl (FullSpec I D K X Response Shared) (StateT Auxiliary (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qCall qNext : Nat)
    (step : ∀ query auxiliary, ((handler query).run auxiliary).IsQueryBoundP predicate qCall)
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) (auxiliary : Auxiliary)
    (next : Option Bytes → State I D K → Auxiliary → OracleComp base Result)
    (nextBound : ∀ reply nextState current, (next reply nextState current).IsQueryBoundP predicate qNext) :
    ((simulateQ handler (owner decode raw state)).run auxiliary >>= fun result =>
      next result.1.1 result.1.2 result.2).IsQueryBoundP predicate (69 * qCall + qNext) :=
  isQueryBoundP_bind (interpreted_bound handler predicate qCall step decode raw state auxiliary)
    (fun result _ => nextBound result.1.1 result.1.2 result.2)

def isDecapsulation {I D K X Response Shared : Type} : Query I D K X Response Shared → Bool
  | .decapsulate _ _ => true
  | _ => false

def isRoot {Response Shared : Type} : (TailSpec Response Shared).Domain → Bool
  | .inr (.root _) => true
  | _ => false

/-- Collection reaches at most one decapsulation callback, retaining its original position before all four DH calls. -/
theorem collect_decapsulation {I D K X Response Shared : Type} (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    (collect (X := X) (Response := Response) (Shared := Shared) identity prekey oneTime kem raw).IsQueryBoundP
      (fun query => isDecapsulation query = true) 1 := by
  unfold collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; simp [isDecapsulation])
    | rw [isQueryBoundP_map_iff]
    | intro reply; cases reply <;> simp only [Option.elim]
  all_goals exact (isQueryBoundP_query_iff (spec := Spec I D K X Response Shared)
    (p := fun query => isDecapsulation query = true) _ 0).mpr (by simp [isDecapsulation])

/-- Core admission and temporary erasure cannot introduce another decapsulation. -/
theorem prepare_decapsulation {I D K X Response Shared : Type} (control : pqxdh.BeaconInitSent)
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    (prepare (X := X) (Response := Response) (Shared := Shared) control identity prekey oneTime kem raw).IsQueryBoundP
      (fun query => isDecapsulation query = true) 1 := by
  unfold prepare
  apply isQueryBoundP_bind (collect_decapsulation identity prekey oneTime kem raw) (m := 0)
  intro reply _
  cases reply with
  | none => trivial
  | some inputs =>
      unfold afterInputs
      rw [isQueryBoundP_query_bind_iff]
      simp only [isDecapsulation, Bool.false_eq_true, not_false_eq_true, true_or, if_false, true_and]
      intro erased
      trivial

/-- After the private root result, initialization and the exact raw driver issue no further root requests. -/
theorem afterRoot_no_root {Response Shared : Type} (decode : RawCtxReceive.FrameDecoder)
    (pending : Prepared Response Shared) (root : Word32) :
    (afterRoot decode pending root).IsQueryBoundP (fun query => isRoot query = true) 0 := by
  unfold afterRoot
  rw [isQueryBoundP_query_bind_iff]
  simp only [isRoot, Bool.false_eq_true, not_false_eq_true, true_or, if_false, true_and]
  intro response
  rw [isQueryBoundP_query_bind_iff]
  simp only [Bool.false_eq_true, not_false_eq_true, true_or, if_false, true_and]
  intro reply
  cases reply with
  | none => trivial
  | some raw =>
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      apply RawCtxSourceOpen.simulate_bound rawLift (fun _ => False) _ _ 0 (isQueryBoundP_false _ _)
      intro query
      exact (isQueryBoundP_query_iff (spec := TailSpec Response Shared)
        (p := fun query => isRoot query = true) (.inl query) 0).mpr (by simp [isRoot])

/-- Every optional root outcome is charged once; the post-root suffix cannot add a second request. -/
theorem tail_root {Response Shared : Type} (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) :
    (tail decode pending).IsQueryBoundP (fun query => isRoot query = true) 1 := by
  unfold tail
  rw [isQueryBoundP_query_bind_iff]
  simp only [isRoot, not_true_eq_false, false_or, if_true]
  refine ⟨by decide, fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some root => exact afterRoot_no_root decode pending root

/-- All-reply preparation and tail class bounds compose through the actual owner branches and unchanged finishing projection. -/
theorem owner_selected_bound {I D K X Response Shared : Type}
    (predicate : (FullSpec I D K X Response Shared).Domain → Prop) [DecidablePred predicate]
    (qPre qTail : Nat)
    (preBound : ∀ control identity prekey oneTime kem raw,
      (prepare control identity prekey oneTime kem raw).IsQueryBoundP (fun query => predicate (.inl query)) qPre)
    (tailBound : ∀ decode pending, (tail decode pending).IsQueryBoundP (fun query => predicate (.inr query)) qTail)
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) :
    (owner decode raw state).IsQueryBoundP predicate (qPre + qTail) := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [owner, active]
      apply isQueryBoundP_bind (n := qPre) (m := qTail)
      · apply RawCtxSourceOpen.simulate_bound preLift (fun query => predicate (.inl query)) predicate _ qPre
          (preBound _ _ _ _ _ _)
        intro query
        exact (isQueryBoundP_query_iff (spec := FullSpec I D K X Response Shared) (p := predicate) (.inl query) _).mpr
          (by split_ifs <;> simp_all)
      · intro reply _
        cases reply with
        | none => trivial
        | some pending =>
            simp only [bind_pure_comp, isQueryBoundP_map_iff]
            apply RawCtxSourceOpen.simulate_bound tailLift (fun query => predicate (.inr query)) predicate _ qTail
              (tailBound _ _)
            intro query
            exact (isQueryBoundP_query_iff (spec := FullSpec I D K X Response Shared) (p := predicate) (.inr query) _).mpr
              (by split_ifs <;> simp_all)
  | _ => simp only [owner, active]; trivial

def decapsulationCall {I D K X Response Shared : Type} : (FullSpec I D K X Response Shared).Domain → Bool
  | .inl query => isDecapsulation query
  | .inr _ => false

def rootCall {I D K X Response Shared : Type} : (FullSpec I D K X Response Shared).Domain → Bool
  | .inl _ => false
  | .inr query => isRoot query

/-- The actual opaque owner reaches at most one original decapsulation site, even when later DH, root or opening work rejects. -/
theorem owner_decapsulation {I D K X Response Shared : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K) :
    (owner (X := X) (Response := Response) (Shared := Shared) decode raw state).IsQueryBoundP
      (fun query => decapsulationCall query = true) 1 := by
  apply owner_selected_bound _ 1 0
  · intro control identity prekey oneTime kem raw
    exact prepare_decapsulation control identity prekey oneTime kem raw
  · intro decode pending
    simpa only [decapsulationCall, Bool.false_eq_true] using isQueryBoundP_false (tail decode pending) 0

/-- Every active, rejected, repeated or inactive attempt has at most one private root call; no accepted-sequence premise shortens the earlier work. -/
theorem owner_root {I D K X Response Shared : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K) :
    (owner (X := X) (Response := Response) (Shared := Shared) decode raw state).IsQueryBoundP
      (fun query => rootCall query = true) 1 := by
  apply owner_selected_bound _ 0 1
  · intro control identity prekey oneTime kem raw
    simpa only [rootCall, Bool.false_eq_true] using isQueryBoundP_false (prepare control identity prekey oneTime kem raw) 0
  · intro decode pending
    exact tail_root decode pending

end BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.collect_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.afterInputs_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.afterInputs_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.prepare_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.afterRoot_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.afterRoot_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.tail_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.tail_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.owner_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.interpreted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.interpreted_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.continuation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.continuation_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.collect_decapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.collect_decapsulation

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.prepare_decapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.prepare_decapsulation

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.afterRoot_no_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.afterRoot_no_root

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.tail_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.tail_root

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.owner_selected_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.owner_selected_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.owner_decapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.owner_decapsulation

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.owner_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds.owner_root
