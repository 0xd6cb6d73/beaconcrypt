import BeaconcryptCore.Computational.PqxdhDynamicKemRouter

/-!
The capped dynamic router's concrete source is related to the original private pool operation by operation. The source-derived creation allowance prevents reservation exhaustion. The freshness stop remains explicit and must be consumed by the final target event; no original client decision is presumed false after compromise. Native owner erasure restricts which private pool reads the production adapter may request.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemSource
open PqxdhDynamicKemRouter PqxdhKemIndCca
open PqxdhLiveKemBirth (Query PoolSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

/-- Rebuilding source state after one reserved creation gives the exact original appended private pair and public-index reply. -/
theorem created_pool (pairs : List (MlKem768PublicKey × KemSK)) (state : State KemSK)
    (pair : MlKem768PublicKey × KemSK) (present : pairs[state.created]? = some pair) :
    ((state.created, pair.1), sourcePool pairs (record .create (state.created, pair.1) { state with created := state.created + 1 })) =
      PqxdhLiveKemBirth.created (sourcePool pairs state) pair := by
  have inRange : state.created < pairs.length := (List.getElem?_eq_some_iff.mp present).1
  have atIndex : pairs[state.created] = pair := (List.getElem?_eq_some_iff.mp present).2
  simp only [sourcePool, record, PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt inRange), List.take_succ_eq_append_getElem inRange, atIndex]

set_option backward.isDefEq.respectTransparency false in
/-- A source decapsulation has the original actual private pool reply and complete appended history, including missing handles and invalid-ciphertext fallback. -/
theorem decapsulation_source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (state : State KemSK)
    (index : Nat) (ciphertext : MlKem768Ciphertext) :
    (fun result => (result.1, sourcePool pairs result.2)) <$>
      (((source baseImpl kem selected pairs (.decapsulate index ciphertext)).run).run state) =
        (fun result => (some result.1, result.2)) <$>
          (PqxdhLiveKemBirth.poolImpl baseImpl kem (.decapsulate index ciphertext)).run (sourcePool pairs state) := by
  cases found : (pairs.take state.created)[index]? <;>
    simp only [source, OptionT.run_mk, StateT.run, PqxdhLiveKemBirth.poolImpl, sourcePool,
      found, map_bind, map_pure, record, PqxdhLiveKemBirth.record]

set_option backward.isDefEq.respectTransparency false in
/-- Every permitted nonselected reveal returns precisely the original optional private key and unchanged pool, with the actual disclosure recorded. -/
theorem other_reveal_source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (state : State KemSK)
    (index : Nat) (other : index ≠ selected) :
    (fun result => (result.1, sourcePool pairs result.2)) <$>
      (((source baseImpl kem selected pairs (.reveal index)).run).run state) =
        (fun result => (some result.1, result.2)) <$>
          (PqxdhLiveKemBirth.poolImpl baseImpl kem (.reveal index)).run (sourcePool pairs state) := by
  cases found : (pairs.take state.created)[index]? <;>
    simp only [source, OptionT.run_mk, StateT.run, PqxdhLiveKemBirth.poolImpl, sourcePool,
      found, map_pure, record, PqxdhLiveKemBirth.record, Option.map_none, Option.map_some, ite_eq_right other]

def IsCreation : Query → Prop
  | .create => True
  | _ => False

instance : DecidablePred IsCreation := fun query => by
  cases query <;> simp only [IsCreation] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- At an affordable callback the original source reservation never exhausts; no callback except creation advances the created-prefix length. -/
theorem step_capacity (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (query : Query) (state : State KemSK)
    (clear : state.exhausted = false)
    (room : state.created + (if IsCreation query then 1 else 0) ≤ pairs.length)
    (result : Option ((PoolSpec KemSK).Range query) × State KemSK)
    (supported : result ∈ support (((source baseImpl kem selected pairs query).run).run state)) :
    result.2.exhausted = false ∧ result.2.created ≤ state.created + (if IsCreation query then 1 else 0) := by
  cases query with
  | create =>
      have before : state.created < pairs.length := by
        simpa only [IsCreation, ite_true] using Nat.lt_of_succ_le room
      have found : pairs[state.created]? = some pairs[state.created] := List.getElem?_eq_some_iff.mpr ⟨before, rfl⟩
      simp only [source, OptionT.run_mk, StateT.run, found, mem_support_pure_iff] at supported
      subst result
      simp only [record, IsCreation, ite_true, le_refl, and_true, clear]
  | decapsulate index ciphertext =>
      simp only [source, OptionT.run_mk, StateT.run, bind_pure_comp] at supported
      split at supported <;> simp only [support_map, Set.mem_image] at supported
      all_goals obtain ⟨reply, _, rfl⟩ := supported
      all_goals simpa only [record, IsCreation, ite_false, Nat.add_zero, le_refl, and_true] using clear
  | reveal index =>
      simp only [source, OptionT.run_mk, StateT.run] at supported
      split at supported
      · simp only [mem_support_pure_iff] at supported
        subst result
        simpa only [record, IsCreation, ite_false, Nat.add_zero, le_refl, and_true] using clear
      · split at supported <;> simp only [mem_support_pure_iff] at supported
        all_goals subst result
        all_goals simpa only [record, IsCreation, ite_false, Nat.add_zero, le_refl, and_true] using clear

set_option backward.isDefEq.respectTransparency false in
/-- A source creation cap suffices for the whole adaptive stopped execution. Reservation exhaustion is impossible, including after failed decapsulation or an uncreated-index reveal. -/
theorem schedule_capacity (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result) (qCreate : Nat)
    (bounded : client.IsQueryBoundP IsCreation qCreate) (state : State KemSK)
    (clear : state.exhausted = false) (room : state.created + qCreate ≤ pairs.length)
    (result : Option Result × State KemSK)
    (supported : result ∈ support (((simulateQ (source baseImpl kem selected pairs) client).run).run state)) :
    result.2.exhausted = false ∧ result.2.created ≤ state.created + qCreate := by
  induction client using OracleComp.inductionOn generalizing qCreate state result with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨clear, Nat.le_add_right _ _⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨head, actual, rest⟩ := supported
      have affordable : state.created + (if IsCreation query then 1 else 0) ≤ pairs.length := by
        split_ifs with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      have headBound := step_capacity baseImpl kem selected pairs query state clear affordable head actual
      rcases head with ⟨none | answer, after⟩
      · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at rest
        subst result
        refine ⟨headBound.1, headBound.2.trans ?_⟩
        split_ifs with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      · dsimp only at headBound
        have tailRoom : after.created + (if IsCreation query then qCreate - 1 else qCreate) ≤ pairs.length := by
          split_ifs at headBound ⊢ with creates
          · have positive := bounded.1.resolve_left (not_not.mpr creates)
            omega
          · omega
        have tail := ih answer _ (bounded.2 answer) after headBound.1 tailRoom result rest
        refine ⟨tail.1, tail.2.trans ?_⟩
        split_ifs at headBound ⊢ with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega

/-- Source fresh construction begins with no private history and needs exactly the announced finite reservation allowance. -/
theorem empty_capacity (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result)
    (bounded : client.IsQueryBoundP IsCreation pairs.length)
    (result : Option Result × State KemSK)
    (supported : result ∈ support (((simulateQ (source baseImpl kem selected pairs) client).run).run empty)) :
    result.2.exhausted = false ∧ result.2.created ≤ pairs.length := by
  simpa only [empty, Nat.zero_add] using
    schedule_capacity baseImpl kem selected pairs client pairs.length bounded empty rfl (by simp [empty]) result supported

/-- Adaptive choice among actually created KEM owners costs the explicit finite sum over the source creation allowance. The final event and complete source result remain unchanged in each summand. -/
theorem selection_sum (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result)
    (bounded : client.IsQueryBoundP IsCreation pairs.length)
    (event : Nat → Option Result × State KemSK → Prop) :
    Pr{let result ← ((simulateQ (source baseImpl kem selected pairs) client).run).run empty}[
      ∃ index, index < result.2.created ∧ event index result] ≤
      ∑ index ∈ Finset.range pairs.length,
        Pr{let result ← ((simulateQ (source baseImpl kem selected pairs) client).run).run empty}[
          index < result.2.created ∧ event index result] := by
  refine le_trans ?_ (prEvent_exists_finset_le _ _ _)
  apply prEvent_mono_of_support
  intro result supported selectedEvent
  obtain ⟨index, present, accepts⟩ := selectedEvent
  exact ⟨index, Finset.mem_range.mpr (present.trans_le
    (empty_capacity baseImpl kem selected pairs client bounded result supported).2), present, accepts⟩

end BeaconcryptCore.Computational.PqxdhDynamicKemSource

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemSource.created_pool' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemSource.created_pool
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemSource.decapsulation_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemSource.decapsulation_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemSource.other_reveal_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemSource.other_reveal_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemSource.step_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemSource.step_capacity
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemSource.schedule_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemSource.schedule_capacity
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemSource.empty_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemSource.empty_capacity
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemSource.selection_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemSource.selection_sum
