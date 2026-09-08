import BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication

/-!
Phase2 resource bounds refer to the actual private callback program and its full stateful interpretation. The logical adapter has at most 68 callbacks; expanding its selected opening into the existing source commitment hash and optional AEAD gives at most 69. These caps retain all work before the final sequence-one gate, including admitted later sequences that are decrypted and then rejected.

Each typed callback still carries its own primitive, codec and local computation cost. The selective interpreted bounds require an explicit per-callback allowance and preserve every actual optional reply and complete state. They transport costs only through exact program equations and structural query bounds. This module asserts no cryptographic advantage bound or native library implementation contract.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds
open PqxdhBeaconPhase2Preparation (Bytes Word32 State Prepared)
open PqxdhBeaconPhase2Publication

/-- Complementary all-reply query classes give one shared total allowance, rather than separately selected traces. -/
theorem total_of_partition {ι Result : Type} {spec : OracleSpec ι}
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (client : OracleComp spec Result)
    (first second : Nat) (left : client.IsQueryBoundP predicate first)
    (right : client.IsQueryBoundP (fun query => ¬ predicate query) second) :
    client.IsTotalQueryBound (first + second) := by
  induction client using OracleComp.inductionOn generalizing first second with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at left right
      rw [isTotalQueryBound_query_bind_iff]
      by_cases selected : predicate query
      · simp only [selected, not_true_eq_false, false_or, if_true, not_false_eq_true,
          true_or, if_false, true_and] at left right
        refine ⟨by omega, fun reply => ?_⟩
        exact (ih reply (first - 1) second (left.2 reply) (right reply)).mono (by omega)
      · simp only [selected, not_false_eq_true, true_or, if_false, true_and,
          not_true_eq_false, false_or, if_true] at left right
        refine ⟨by omega, fun reply => ?_⟩
        exact (ih reply first (second - 1) (left reply) (right.2 reply)).mono (by omega)

/-- A structural one-query compiler preserves total callback counts for arbitrary typed replies. -/
theorem simulate_total {ι κ Result : Type} {spec : OracleSpec ι} {target : OracleSpec κ}
    (handler : QueryImpl spec (OracleComp target)) (client : OracleComp spec Result) (budget : Nat)
    (bounded : client.IsTotalQueryBound budget) (step : ∀ query, (handler query).IsTotalQueryBound 1) :
    (simulateQ handler client).IsTotalQueryBound budget := by
  apply (isQueryBoundP_true_iff _ _).mp
  apply RawCtxSourceOpen.simulate_bound handler (fun _ => True) (fun _ => True) client budget
    ((isQueryBoundP_true_iff _ _).mpr bounded)
  intro query
  exact (step query).isQueryBoundP

/-- The union of two all-reply classes is charged by their combined allowances, including overlapping membership. -/
theorem query_union {ι Result : Type} {spec : OracleSpec ι}
    (p q : spec.Domain → Prop) [DecidablePred p] [DecidablePred q]
    (client : OracleComp spec Result) (first second : Nat)
    (left : client.IsQueryBoundP p first) (right : client.IsQueryBoundP q second) :
    client.IsQueryBoundP (fun query => p query ∨ q query) (first + second) := by
  induction client using OracleComp.inductionOn generalizing first second with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at left right ⊢
      by_cases hp : p query <;> by_cases hq : q query
      · simp only [hp, hq, true_or, if_true, not_true_eq_false, false_or] at left right ⊢
        exact ⟨by omega, fun reply => (ih reply (first - 1) (second - 1) (left.2 reply) (right.2 reply)).mono (by omega)⟩
      · simp only [hp, hq, true_or, if_true, if_false, true_and, not_true_eq_false, not_false_eq_true, false_or] at left right ⊢
        exact ⟨by omega, fun reply => (ih reply (first - 1) second (left.2 reply) (right reply)).mono (by omega)⟩
      · simp only [hp, hq, true_or, if_true, if_false, true_and, not_true_eq_false, not_false_eq_true, false_or] at left right ⊢
        exact ⟨by omega, fun reply => (ih reply first (second - 1) (left reply) (right.2 reply)).mono (by omega)⟩
      · simp only [hp, hq, false_or, if_false, not_false_eq_true, true_or, true_and] at left right ⊢
        exact fun reply => ih reply first second (left reply) (right reply)

/-- The actual admitted source receiver retains its 51 KDF cap and at most one opening, including all rejected initial sequences. -/
theorem receive_total (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel target context).IsTotalQueryBound 52 := by
  apply total_of_partition (fun query => query.isLeft = true) _ 51 1 (RawCtxKdfBudget.receive_bound _ _ _)
  apply (isQueryBoundP_congr_pred (p' := fun query => query.isRight = true) (fun query => by cases query <;> simp)).mpr
  exact RawCtxOwnerOracle.program_open_bound _

/-- Parsing, field guards and result wrapping do not add to the actual raw receiver's 52 callbacks. -/
theorem raw_total {Metadata : Type} (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    ((RawCtxWholeOwner.rawReceive decode raw).run state).IsTotalQueryBound 52 := by
  unfold RawCtxWholeOwner.rawReceive StateT.run
  split
  · trivial
  · split
    · trivial
    · dsimp only
      split
      · simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
        apply simulate_total RawCtxWholeOwner.adapter _ 52 (receive_total _ _ _)
        intro query
        cases query with
        | inl request =>
            simp only [RawCtxWholeOwner.adapter]
            exact (isQueryBoundP_true_iff _ _).mp
              ((isQueryBoundP_query_iff (spec := RawCtxWholeOwner.PrimitiveSpec) (p := fun _ => True) (.inl request) 1).mpr (by decide))
        | inr pending =>
            simp only [RawCtxWholeOwner.adapter]
            cases RawCtxWholeOwner.arguments pending with
            | none => trivial
            | some input =>
                rw [isTotalQueryBound_query_bind_iff]
                exact ⟨by decide, fun _ => by trivial⟩
      · trivial

/-- Source opening expansion retains one hash and one optional AEAD call in addition to the same 51 KDF allowance. -/
theorem native_raw_total {Metadata : Type} (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    (simulateQ RawCtxSourceOpen.nativeAdapter ((RawCtxWholeOwner.rawReceive decode raw).run state)).IsTotalQueryBound 53 := by
  have bounds := RawCtxSourceOpen.raw_primitive_bounds decode raw state
  have combined := query_union _ _ _ 51 2 (RawCtxKdfBudget.raw_bound decode raw state)
    (query_union _ _ _ 1 1 bounds.1 bounds.2)
  apply (isQueryBoundP_true_iff _ _).mp
  apply (isQueryBoundP_congr_pred (p' := fun query => query.isLeft = true ∨
    (RawCtxSourceOpen.openingPredicate Sum.isLeft query = true ∨
      RawCtxSourceOpen.openingPredicate Sum.isRight query = true)) ?_).mpr combined
  intro query
  cases query with
  | inl request => simp [RawCtxSourceOpen.openingPredicate]
  | inr request => cases request <;> simp [RawCtxSourceOpen.openingPredicate]

/-- The actual initial64 callback, later app getter and admitted raw work cost at most 54 logical callbacks. -/
theorem afterRoot_bound {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : Prepared Response) (root : Word32) :
    (afterRoot decode prepared root).IsTotalQueryBound 54 := by
  unfold afterRoot initialRun
  simp only [bind_assoc, pure_bind]
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun response => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some raw =>
      simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      apply simulate_total rawLift _ 52 (raw_total _ _ _)
      intro query
      exact (isQueryBoundP_true_iff _ _).mp
        ((isQueryBoundP_query_iff (spec := TailSpec Response) (p := fun _ => True) (.inl query) 1).mpr (by decide))

/-- Every attempted root derivation is charged before its optional outcome, for at most 55 tail callbacks. -/
theorem tail_bound {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : Prepared Response) : (tail decode prepared).IsTotalQueryBound 55 := by
  unfold tail
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some root => exact afterRoot_bound decode prepared root

/-- The complete active native policy has 68 logical callbacks; all failed initial sequence attempts retain their actual work. -/
theorem owner_bound {I D K X Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K) :
    (owner (X := X) (Response := Response) decode raw state).IsTotalQueryBound 68 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [owner, active]
      apply isTotalQueryBound_bind (n₁ := 13) (n₂ := 55)
      · apply simulate_total preLift _ 13 (PqxdhBeaconPhase2Preparation.prepare_bound _ _ _ _ _ _)
        intro query
        exact (isQueryBoundP_true_iff _ _).mp
          ((isQueryBoundP_query_iff (spec := FullSpec I D K X Response) (p := fun _ => True) (.inl query) 1).mpr (by decide))
      · intro prepared
        cases prepared with
        | none => trivial
        | some prepared =>
            simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
            apply simulate_total tailLift _ 55 (tail_bound _ _)
            intro query
            exact (isQueryBoundP_true_iff _ _).mp
              ((isQueryBoundP_query_iff (spec := FullSpec I D K X Response) (p := fun _ => True) (.inr query) 1).mpr (by decide))
  | _ => simp only [owner, active]; trivial

/-- The nested private raw dispatch is exactly the existing source opening expansion in the same native tail oracle. -/
theorem native_raw_lift {Response Result : Type} (client : OracleComp RawCtxWholeOwner.PrimitiveSpec Result) :
    simulateQ (nativeTailAdapter (Response := Response)) (simulateQ rawLift client) =
      simulateQ nativeRawLift (simulateQ RawCtxSourceOpen.nativeAdapter client) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, rawLift]
  exact simulateQ_spec_query nativeTailAdapter (.inl query)

/-- The concrete hash/AEAD expansion adds only one to the original post-root allowance. -/
theorem native_afterRoot_bound {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : Prepared Response) (root : Word32) :
    (simulateQ nativeTailAdapter (afterRoot decode prepared root)).IsTotalQueryBound 55 := by
  unfold afterRoot initialRun
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, nativeTailAdapter]
  change (show OracleComp (NativeTailSpec Response) (Option Staged) from do
    let response ← (NativeTailSpec Response).query (.inr (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request))
    let reply ← (NativeTailSpec Response).query (.inr (.application prepared.response))
    simulateQ nativeTailAdapter (match reply with
      | none => pure none
      | some raw => do
        let result ← simulateQ rawLift ((RawCtxWholeOwner.rawReceive decode raw).run
          (localOwner (clearedCandidate prepared.candidate) (normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root) response)))
        pure (afterOpening (clearedCandidate prepared.candidate) result.2.owner.kernel result.1))).IsTotalQueryBound 55
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun response => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun reply => ?_⟩
  cases reply with
  | none => simp only [simulateQ_pure]; trivial
  | some raw =>
      simp only [bind_pure_comp, simulateQ_map, native_raw_lift,
        IsTotalQueryBound, isQueryBound_map_iff]
      apply simulate_total nativeRawLift _ 53 (native_raw_total _ _ _)
      intro query
      exact (isQueryBoundP_true_iff _ _).mp
        ((isQueryBoundP_query_iff (spec := NativeTailSpec Response) (p := fun _ => True) (.inl query) 1).mpr (by decide))

/-- Native tail processing charges root, initial64, app access, and all 51 KDF/hash/AEAD work before any rejection. -/
theorem native_tail_bound {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : Prepared Response) :
    (simulateQ nativeTailAdapter (tail decode prepared)).IsTotalQueryBound 56 := by
  unfold tail
  simp only [simulateQ_bind, simulateQ_spec_query, nativeTailAdapter]
  change (show OracleComp (NativeTailSpec Response) (Option Staged) from do
    let reply ← (NativeTailSpec Response).query (.inr (.root prepared.candidate.root_key_input))
    simulateQ nativeTailAdapter (match reply with
      | none => pure none
      | some root => afterRoot decode prepared root)).IsTotalQueryBound 56
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun reply => ?_⟩
  cases reply with
  | none => simp only [simulateQ_pure]; trivial
  | some root => exact native_afterRoot_bound decode prepared root

/-- Full-owner routing retains the identical native tail program and every callback reply. -/
theorem native_tail_lift {I D K X Response Result : Type} (client : OracleComp (TailSpec Response) Result) :
    simulateQ (nativeAdapter (I := I) (D := D) (K := K) (X := X)) (simulateQ tailLift client) =
      simulateQ nativeTailLift (simulateQ nativeTailAdapter client) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, tailLift]
  exact simulateQ_spec_query nativeAdapter (.inr query)

/-- The complete expanded native Phase2 program retains its full 69-callback allowance under every optional reply. -/
theorem native_owner_bound {I D K X Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K) :
    (nativeOwner (X := X) (Response := Response) decode raw state).IsTotalQueryBound 69 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [nativeOwner, owner, active, simulateQ_bind]
      apply isTotalQueryBound_bind (n₁ := 13) (n₂ := 56)
      · rw [← QueryImpl.simulateQ_compose]
        apply simulate_total _ _ 13 (PqxdhBeaconPhase2Preparation.prepare_bound _ _ _ _ _ _)
        intro query
        simp only [QueryImpl.apply_compose, preLift]
        change (simulateQ nativeAdapter (liftM ((FullSpec I D K X Response).query (.inl query)))).IsTotalQueryBound 1
        rw [show simulateQ nativeAdapter (liftM ((FullSpec I D K X Response).query (.inl query))) =
          liftM ((NativeSpec I D K X Response).query (.inl query)) from simulateQ_spec_query nativeAdapter (.inl query)]
        exact (isQueryBoundP_true_iff _ _).mp
          ((isQueryBoundP_query_iff (spec := NativeSpec I D K X Response) (p := fun _ => True) (.inl query) 1).mpr (by decide))
      · intro prepared
        cases prepared with
        | none => simp only [simulateQ_pure]; trivial
        | some prepared =>
            simp only [bind_pure_comp, simulateQ_map, native_tail_lift, IsTotalQueryBound, isQueryBound_map_iff]
            apply simulate_total nativeTailLift _ 56 (native_tail_bound _ _)
            intro query
            exact (isQueryBoundP_true_iff _ _).mp
              ((isQueryBoundP_query_iff (spec := NativeSpec I D K X Response) (p := fun _ => True) (.inr query) 1).mpr (by decide))
  | _ => simp only [nativeOwner, owner, active, simulateQ_pure]; trivial

/-- Typed callback allowances bound the same complete stateful execution under any selected underlying query predicate. -/
theorem interpreted_total_bound {ι κ Result A : Type} {spec : OracleSpec ι} {base : OracleSpec κ}
    (handler : QueryImpl spec (StateT A (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qCall budget : Nat)
    (step : ∀ query auxiliary, ((handler query).run auxiliary).IsQueryBoundP predicate qCall)
    (client : OracleComp spec Result) (bounded : client.IsTotalQueryBound budget) (auxiliary : A) :
    ((simulateQ handler client).run auxiliary).IsQueryBoundP predicate (budget * qCall) := by
  have bound := FinitePartitionQueryBounds.weighted_bound (fun (_ : spec.Domain) => ())
    (fun _ => qCall) (fun _ => budget) handler predicate client
    (fun kind => by cases kind; simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false,
      false_or, if_true] using bounded) step auxiliary
  simpa only [Finset.univ_unique, Finset.sum_singleton, Nat.mul_comm] using bound

/-- The expanded native adapter charges every primitive/codec callback's selected work, including work before terminal abort. -/
theorem native_interpreted_bound {I D K X Response A ι : Type} {base : OracleSpec ι}
    (handler : QueryImpl (NativeSpec I D K X Response) (StateT A (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qCall : Nat)
    (step : ∀ query auxiliary, ((handler query).run auxiliary).IsQueryBoundP predicate qCall)
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) (auxiliary : A) :
    ((simulateQ handler (nativeOwner decode raw state)).run auxiliary).IsQueryBoundP predicate (69 * qCall) :=
  interpreted_total_bound handler predicate qCall 69 step _ (native_owner_bound decode raw state) auxiliary

/-- A private continuation starts from the actual optional result, complete updated owner and primitive poststate, and pays its own selected allowance. -/
theorem native_continuation_bound {I D K X Response A Result ι : Type} {base : OracleSpec ι}
    (handler : QueryImpl (NativeSpec I D K X Response) (StateT A (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qCall qNext : Nat)
    (step : ∀ query auxiliary, ((handler query).run auxiliary).IsQueryBoundP predicate qCall)
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) (auxiliary : A)
    (next : Option Bytes → State I D K → A → OracleComp base Result)
    (nextBound : ∀ reply nextState current, (next reply nextState current).IsQueryBoundP predicate qNext) :
    ((simulateQ handler (nativeOwner decode raw state)).run auxiliary >>= fun result =>
      next result.1.1 result.1.2 result.2).IsQueryBoundP predicate (69 * qCall + qNext) :=
  isQueryBoundP_bind (native_interpreted_bound handler predicate qCall step decode raw state auxiliary)
    (fun result _ => nextBound result.1.1 result.1.2 result.2)

end BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.total_of_partition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.total_of_partition

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.simulate_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.simulate_total

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.query_union' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.query_union

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.receive_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.receive_total

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.raw_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.raw_total

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_raw_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_raw_total

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.afterRoot_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.afterRoot_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.tail_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.tail_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.owner_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_raw_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_raw_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_afterRoot_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_afterRoot_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_tail_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_tail_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_tail_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_tail_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_owner_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.interpreted_total_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.interpreted_total_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_interpreted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_interpreted_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_continuation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds.native_continuation_bound
