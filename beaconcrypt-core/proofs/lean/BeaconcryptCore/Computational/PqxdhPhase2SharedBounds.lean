import BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared

/-!
Intrinsic callback counts for the opaque-shared Phase2 program are proved from its own source-shaped syntax. The selected decapsulation and private root each occur at most once; the complete source callback count includes actual raw KDF, commitment and opening work before the final sequence-one gate. No cryptographic simulation or externally supplied protocol budget establishes these bounds.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2SharedBounds
open PqxdhBeaconPhase2Preparation (Bytes Word32 State)
open PqxdhBeaconPhase2Shared
open PqxdhBeaconPhase2Bounds (simulate_total native_raw_total)
variable {I D K X Response Shared : Type}

/-- All twelve original preparation getters and cryptographic callbacks retain every optional reply branch. -/
theorem collect_total (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    (collect (X := X) (Response := Response) (Shared := Shared) identity prekey oneTime kem raw).IsTotalQueryBound 12 := by
  unfold collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | rw [isTotalQueryBound_query_bind_iff]
    | constructor
    | intro reply; cases reply

/-- Core admission retains exactly one temporary-secret erasure callback on either outcome. -/
theorem afterInputs_total (control : pqxdh.BeaconInitSent) (inputs : Inputs Response Shared) :
    (afterInputs (I := I) (D := D) (K := K) (X := X) control inputs).IsTotalQueryBound 1 := by
  simp only [afterInputs, isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

/-- All original preparation and erasure callbacks are charged before the optional tail begins. -/
theorem prepare_total (control : pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D)
    (kem : K) (raw : Bytes) :
    (prepare (X := X) (Response := Response) (Shared := Shared) control identity prekey oneTime kem raw).IsTotalQueryBound 13 := by
  unfold prepare
  apply isTotalQueryBound_bind (collect_total identity prekey oneTime kem raw) (n₂ := 1)
  exact fun result => by cases result with
    | none => trivial
    | some inputs => exact afterInputs_total control inputs

/-- Initial64 and application access precede the same 53 native raw KDF/hash/opening callbacks. -/
theorem afterRoot_total (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) (root : Word32) :
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
    apply simulate_total rawLift _ 53 (native_raw_total _ _ _)
    exact fun query => (isQueryBoundP_true_iff _ _).mp
      ((isQueryBoundP_query_iff (spec := TailSpec Response Shared) (p := fun _ => True) (.inl query) 1).mpr (by decide))

/-- The private root query is charged before its optional result, followed by the original native tail. -/
theorem tail_total (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) :
    (tail decode pending).IsTotalQueryBound 56 := by
  simp only [tail, isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun reply => by cases reply with
    | none => trivial
    | some root => exact afterRoot_total decode pending root⟩

/-- Every attempted opaque-shared Phase2 owner has at most 69 original callbacks, including failures before the sequence-one gate. -/
theorem owner_total (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) :
    (owner (X := X) (Response := Response) (Shared := Shared) decode raw state).IsTotalQueryBound 69 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [owner, active]
    apply isTotalQueryBound_bind (n₁ := 13) (n₂ := 56)
    · apply simulate_total preLift _ 13 (prepare_total _ _ _ _ _ _)
      exact fun query => (isQueryBoundP_true_iff _ _).mp
        ((isQueryBoundP_query_iff (spec := FullSpec I D K X Response Shared) (p := fun _ => True) (.inl query) 1).mpr (by decide))
    · intro pending
      cases pending with
      | none => trivial
      | some pending =>
        simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
        exact simulate_total tailLift _ 56 (tail_total decode pending) (fun query =>
          (isQueryBoundP_true_iff _ _).mp
            ((isQueryBoundP_query_iff (spec := FullSpec I D K X Response Shared) (p := fun _ => True) (.inr query) 1).mpr (by decide)))
  | _ => simp only [owner, active]; trivial

def IsDecapsulation : (Spec I D K X Response Shared).Domain → Prop
  | .decapsulate _ _ => True
  | _ => False

instance : DecidablePred (IsDecapsulation (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)) :=
  fun query => by cases query <;> simp only [IsDecapsulation] <;> infer_instance

/-- The original collection attempts its one decapsulation at most once, before every DH callback. -/
theorem collect_decapsulation (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    (collect (X := X) (Response := Response) (Shared := Shared) identity prekey oneTime kem raw).IsQueryBoundP
      IsDecapsulation 1 := by
  unfold collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | rw [isQueryBoundP_query_bind_iff]
    | apply And.intro
    | intro reply; cases reply
  all_goals simp [IsDecapsulation, OracleSpec.query, monadLift]

/-- No later preparation stage repeats the collected decapsulation, including admission errors. -/
theorem prepare_decapsulation (control : pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D)
    (kem : K) (raw : Bytes) :
    (prepare (X := X) (Response := Response) (Shared := Shared) control identity prekey oneTime kem raw).IsQueryBoundP
      IsDecapsulation 1 := by
  unfold prepare
  apply isQueryBoundP_bind (collect_decapsulation identity prekey oneTime kem raw) (m := 0)
  exact fun result _ => by cases result <;>
    simp [afterInputs, IsDecapsulation]

private theorem simulate_excluded {ι κ Result : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    (handler : QueryImpl source (OracleComp target))
    (predicate : target.Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ query, (handler query).IsQueryBoundP predicate 0) (client : OracleComp source Result) :
    (simulateQ handler client).IsQueryBoundP predicate 0 := by
  exact RawCtxSourceOpen.simulate_bound handler (fun _ => False) predicate client 0
    (isQueryBoundP_false client 0) (fun query => by simpa only [ite_false] using excluded query)

def IsTailRoot : (TailSpec Response Shared).Domain → Prop
  | .inr (.root _) => True
  | _ => False

instance : DecidablePred (IsTailRoot (Response := Response) (Shared := Shared)) :=
  fun query => by rcases query with (query | query) <;> cases query <;> simp only [IsTailRoot] <;> infer_instance

/-- Initializer, app getter and arbitrary native raw work have no private-root callback. -/
theorem afterRoot_no_root (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) (root : Word32) :
    (afterRoot decode pending root).IsQueryBoundP IsTailRoot 0 := by
  simp only [afterRoot, isQueryBoundP_query_bind_iff, IsTailRoot, not_false_eq_true, true_or, true_and]
  intro response reply
  cases reply with
  | none => trivial
  | some raw =>
    simp only [bind_pure_comp, isQueryBoundP_map_iff]
    exact simulate_excluded rawLift IsTailRoot (fun query =>
      (isQueryBoundP_query_iff (spec := TailSpec Response Shared) (p := IsTailRoot) (.inl query) 0).mpr
        (by simp [IsTailRoot])) _

/-- The complete tail issues at most its one private root query, independent of all later raw replies. -/
theorem tail_root (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) :
    (tail decode pending).IsQueryBoundP IsTailRoot 1 := by
  simp only [tail, isQueryBoundP_query_bind_iff, IsTailRoot, not_true_eq_false, false_or]
  exact ⟨by decide, fun reply => by cases reply with
    | none => trivial
    | some root => exact afterRoot_no_root decode pending root⟩

def IsOwnerRoot : (FullSpec I D K X Response Shared).Domain → Prop
  | .inl _ => False
  | .inr query => IsTailRoot query

def IsOwnerDecapsulation : (FullSpec I D K X Response Shared).Domain → Prop
  | .inl query => IsDecapsulation query
  | .inr _ => False

instance : DecidablePred (IsOwnerRoot (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)) :=
  fun query => by cases query <;> simp only [IsOwnerRoot] <;> infer_instance

instance : DecidablePred (IsOwnerDecapsulation (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)) :=
  fun query => by cases query <;> simp only [IsOwnerDecapsulation] <;> infer_instance

/-- Every attempted finish can request at most one private root, including all optional and inactive branches. -/
theorem owner_root (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) :
    (owner (X := X) (Response := Response) (Shared := Shared) decode raw state).IsQueryBoundP IsOwnerRoot 1 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [owner, active]
    apply isQueryBoundP_bind (n := 0) (m := 1)
    · exact simulate_excluded preLift IsOwnerRoot (fun query =>
        (isQueryBoundP_query_iff (spec := FullSpec I D K X Response Shared) (p := IsOwnerRoot) (.inl query) 0).mpr
          (by simp [IsOwnerRoot])) _
    · intro pending _
      cases pending with
      | none => trivial
      | some pending =>
        simp only [bind_pure_comp, isQueryBoundP_map_iff]
        apply RawCtxSourceOpen.simulate_bound tailLift IsTailRoot IsOwnerRoot _ 1 (tail_root decode pending)
        exact fun query => (isQueryBoundP_query_iff (spec := FullSpec I D K X Response Shared)
          (p := IsOwnerRoot) (.inr query) _).mpr (by
            intro selected
            simpa only [ite_eq_left (show IsTailRoot query from selected)] using Nat.zero_lt_one)
  | _ => simp only [owner, active]; trivial

/-- Every attempted finish can invoke its retained KEM decapsulation at most once, with no repeat in the tail. -/
theorem owner_decapsulation (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) :
    (owner (X := X) (Response := Response) (Shared := Shared) decode raw state).IsQueryBoundP IsOwnerDecapsulation 1 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [owner, active]
    apply isQueryBoundP_bind (n := 1) (m := 0)
    · apply RawCtxSourceOpen.simulate_bound preLift IsDecapsulation IsOwnerDecapsulation _ 1
        (prepare_decapsulation control state.beacon.identity prekey oneTime kem raw)
      exact fun query => (isQueryBoundP_query_iff (spec := FullSpec I D K X Response Shared)
        (p := IsOwnerDecapsulation) (.inl query) _).mpr (by
          intro selected
          simpa only [ite_eq_left (show IsDecapsulation query from selected)] using Nat.zero_lt_one)
    · intro pending _
      cases pending with
      | none => trivial
      | some pending =>
        simp only [bind_pure_comp, isQueryBoundP_map_iff]
        exact simulate_excluded tailLift IsOwnerDecapsulation (fun query =>
          (isQueryBoundP_query_iff (spec := FullSpec I D K X Response Shared)
            (p := IsOwnerDecapsulation) (.inr query) 0).mpr (by simp [IsOwnerDecapsulation])) _
  | _ => simp only [owner, active]; trivial

end BeaconcryptCore.Computational.PqxdhPhase2SharedBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.collect_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.collect_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.afterInputs_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.afterInputs_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.prepare_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.prepare_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.afterRoot_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.afterRoot_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.tail_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.tail_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.owner_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.owner_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.collect_decapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.collect_decapsulation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.prepare_decapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.prepare_decapsulation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.afterRoot_no_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.afterRoot_no_root

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.tail_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.tail_root

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.owner_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.owner_root

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.owner_decapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedBounds.owner_decapsulation
