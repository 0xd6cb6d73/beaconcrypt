import BeaconcryptCore.Computational.PqxdhInitialFusedOwner
import BeaconcryptCore.Computational.PqxdhPhase2SharedBounds

/-!
The response-only Beacon owner has its own all-reply source budgets. Its fused root/initializer callback is counted once, preparation still attempts at most one decapsulation, and the complete source program has at most68 callbacks. These bounds are derived from the executable fused program for every supplied64-byte response, without transporting costs through a cryptographic or evaluated-distribution equality.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialFusedBudgets
open PqxdhInitialFusedOwner
open PqxdhBeaconPhase2Bounds (simulate_total native_raw_total)
variable {I D K X Response Shared : Type}

def IsTailService : (PqxdhInitialFusedBeacon.Spec Response Shared).Domain → Prop
  | .inr _ => True
  | _ => False
instance : DecidablePred (IsTailService (Response := Response) (Shared := Shared)) :=
  fun query => by cases query <;> simp only [IsTailService] <;> infer_instance

def IsService : (Spec I D K X Response Shared).Domain → Prop
  | .inr query => IsTailService query
  | _ => False
def IsDecapsulation : (Spec I D K X Response Shared).Domain → Prop
  | .inl query => PqxdhPhase2SharedBounds.IsDecapsulation query
  | _ => False
instance : DecidablePred (IsService (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)) :=
  fun query => by cases query <;> simp only [IsService] <;> infer_instance
instance : DecidablePred (IsDecapsulation (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)) :=
  fun query => by cases query <;> simp only [IsDecapsulation] <;> infer_instance

private theorem excluded {ι κ Result : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    (handler : QueryImpl source (OracleComp target)) (predicate : target.Domain → Prop) [DecidablePred predicate]
    (steps : ∀ query, (handler query).IsQueryBoundP predicate 0) (client : OracleComp source Result) :
    (simulateQ handler client).IsQueryBoundP predicate 0 := by
  exact RawCtxSourceOpen.simulate_bound handler (fun _ => False) predicate client 0
    (isQueryBoundP_false client 0) (fun query => by simpa only [ite_false] using steps query)

/-- The root-erased application getter and complete original raw receive use at most54 callbacks for every initializer response. -/
theorem after_total (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    (PqxdhInitialFusedBeacon.afterInitial decode pending response).IsTotalQueryBound 54 := by
  unfold PqxdhInitialFusedBeacon.afterInitial
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some raw =>
      simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      apply simulate_total PqxdhInitialFusedBeacon.rawLift _ 53 (native_raw_total _ _ _)
      exact fun query => (isQueryBoundP_true_iff _ _).mp
        ((isQueryBoundP_query_iff (spec := PqxdhInitialFusedBeacon.Spec Response Shared)
          (p := fun _ => True) (.inl (.inl query)) 1).mpr (by decide))

/-- The actual private fused request precedes the full application/raw tail and is charged once. -/
theorem tail_total (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) :
    (PqxdhInitialFusedBeacon.tail decode pending).IsTotalQueryBound 55 := by
  simp only [PqxdhInitialFusedBeacon.tail, isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun reply => by cases reply with
    | none => trivial
    | some response => exact after_total decode pending response⟩

/-- Every active or inactive attempted fused owner has at most68 actual callbacks, including all failures. -/
theorem owner_total (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K) :
    (owner (X := X) (Response := Response) (Shared := Shared) decode raw state).IsTotalQueryBound 68 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [owner, active]
      apply isTotalQueryBound_bind (n₁ := 13) (n₂ := 55)
      · apply simulate_total preLift _ 13 (PqxdhPhase2SharedBounds.prepare_total _ _ _ _ _ _)
        exact fun query => (isQueryBoundP_true_iff _ _).mp
          ((isQueryBoundP_query_iff (spec := Spec I D K X Response Shared) (p := fun _ => True) (.inl query) 1).mpr (by decide))
      · intro pending
        cases pending with
        | none => trivial
        | some pending =>
            simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
            exact simulate_total tailLift _ 55 (tail_total decode pending) (fun query =>
              (isQueryBoundP_true_iff _ _).mp
                ((isQueryBoundP_query_iff (spec := Spec I D K X Response Shared)
                  (p := fun _ => True) (.inr query) 1).mpr (by decide)))
  | _ => simp only [owner, active]; trivial

/-- No callback after the supplied initializer response can request the private initializer again. -/
theorem after_no_service (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    (PqxdhInitialFusedBeacon.afterInitial decode pending response).IsQueryBoundP IsTailService 0 := by
  simp only [PqxdhInitialFusedBeacon.afterInitial, isQueryBoundP_query_bind_iff,
    IsTailService, not_false_eq_true, true_or, true_and]
  intro reply
  cases reply with
  | none => trivial
  | some raw =>
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      exact excluded PqxdhInitialFusedBeacon.rawLift IsTailService (fun query =>
        (isQueryBoundP_query_iff (spec := PqxdhInitialFusedBeacon.Spec Response Shared)
          (p := IsTailService) (.inl (.inl query)) 0).mpr (by simp [IsTailService])) _

/-- Every optional fused tail makes at most its one private initializer request. -/
theorem tail_service (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) :
    (PqxdhInitialFusedBeacon.tail decode pending).IsQueryBoundP IsTailService 1 := by
  simp only [PqxdhInitialFusedBeacon.tail, isQueryBoundP_query_bind_iff, IsTailService,
    not_true_eq_false, false_or]
  exact ⟨by decide, fun reply => by cases reply with
    | none => trivial
    | some response => exact after_no_service decode pending response⟩

/-- The complete actual owner attempts at most one response-only initializer service, independently of all arbitrary replies. -/
theorem owner_service (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K) :
    (owner (X := X) (Response := Response) (Shared := Shared) decode raw state).IsQueryBoundP IsService 1 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [owner, active]
      apply isQueryBoundP_bind (n := 0) (m := 1)
      · exact excluded preLift IsService (fun query =>
          (isQueryBoundP_query_iff (spec := Spec I D K X Response Shared) (p := IsService) (.inl query) 0).mpr
            (by simp [IsService])) _
      · intro pending _
        cases pending with
        | none => trivial
        | some pending =>
            simp only [bind_pure_comp, isQueryBoundP_map_iff]
            apply RawCtxSourceOpen.simulate_bound tailLift IsTailService IsService _ 1 (tail_service decode pending)
            exact fun query => (isQueryBoundP_query_iff (spec := Spec I D K X Response Shared)
              (p := IsService) (.inr query) _).mpr (by
                intro selected
                simpa only [IsService, ite_eq_left (show IsTailService query from selected)] using Nat.zero_lt_one)
  | _ => simp only [owner, active]; trivial

/-- The actual collection's single decapsulation bound survives the fused tail; no response-only or raw callback can add a decapsulation. -/
theorem owner_decapsulation (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K) :
    (owner (X := X) (Response := Response) (Shared := Shared) decode raw state).IsQueryBoundP IsDecapsulation 1 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [owner, active]
      apply isQueryBoundP_bind (n := 1) (m := 0)
      · apply RawCtxSourceOpen.simulate_bound preLift PqxdhPhase2SharedBounds.IsDecapsulation IsDecapsulation _ 1
          (PqxdhPhase2SharedBounds.prepare_decapsulation _ _ _ _ _ _)
        exact fun query => (isQueryBoundP_query_iff (spec := Spec I D K X Response Shared)
          (p := IsDecapsulation) (.inl query) _).mpr (by
            intro selected
            simpa only [IsDecapsulation, ite_eq_left (show PqxdhPhase2SharedBounds.IsDecapsulation query from selected)] using Nat.zero_lt_one)
      · intro pending _
        cases pending with
        | none => trivial
        | some pending =>
            simp only [bind_pure_comp, isQueryBoundP_map_iff]
            exact excluded tailLift IsDecapsulation (fun query =>
              (isQueryBoundP_query_iff (spec := Spec I D K X Response Shared)
                (p := IsDecapsulation) (.inr query) 0).mpr (by simp [IsDecapsulation])) _
  | _ => simp only [owner, active]; trivial

end BeaconcryptCore.Computational.PqxdhInitialFusedBudgets

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.after_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.after_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.tail_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.tail_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.owner_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.owner_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.after_no_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.after_no_service
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.tail_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.tail_service
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.owner_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.owner_service
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.owner_decapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBudgets.owner_decapsulation
