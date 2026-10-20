import BeaconcryptCore.Computational.PqxdhLiveKemBirth

/-!
Bounded private KEM reservation is compared with the actual on-demand indexed service through the complete evaluated continuation. Future pairs stay private and uncreated, every source observation is retained, and every sampled pair uses the actual KEM generator. This permits a later selected-creation reduction to move generation only through a checked full-distribution equation. It does not discharge selected-secret freshness or expose an erased key through a production reveal API.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveKemReservation
open PqxdhLiveKemBirth PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

abbrev Pair (KemSK : Type) := MlKem768PublicKey × KemSK

def samplePairs (sampler : ProbComp (Pair KemSK)) : Nat → ProbComp (List (Pair KemSK))
  | 0 => pure []
  | count + 1 => do
      let pair ← sampler
      let rest ← samplePairs sampler count
      pure (pair :: rest)

/-- Future reserved pairs never occur in source state until the actual indexed creation request. Exhaustion falls back to the original sampler, a branch the bounded comparison will avoid. -/
def reserved (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (pairs : List (Pair KemSK)) :
    QueryImpl (Spec KemSK) (StateT (State KemSK) ProbComp) := fun query state =>
  match query with
  | .inr (.inr .create) =>
      match pairs[state.2.keys.length]? with
      | some pair => pure ((created state.2 pair).1, (state.1, (created state.2 pair).2))
      | none => (impl baseImpl primitives kem (.inr (.inr .create))).run state
  | query => (impl baseImpl primitives kem query).run state

def IsCreate : (Spec KemSK).Domain → Prop
  | .inr (.inr .create) => True
  | _ => False

instance : DecidablePred (IsCreate (KemSK := KemSK)) := fun query => by
  rcases query with query | (query | query)
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable False)
  · cases query <;> simp only [IsCreate] <;> infer_instance

/-- The ordinary actual pair sampler is lossless, so privately unused future draws integrate out of the entire continued distribution. -/
theorem unused {Result : Type} (sampler : ProbComp (Pair KemSK)) (count : Nat) (work : ProbComp Result) :
    𝒮[samplePairs sampler count >>= fun _ => work] = 𝒮[work] := by
  apply evalSPMF_ext
  intro result
  simp only [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

/-- Actual creation appends the generated pair and creation reply while retaining the entire joint service. -/
theorem source_create (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (state : State KemSK) :
    (impl baseImpl primitives kem (.inr (.inr .create))).run state =
      (fun pair => ((created state.2 pair).1, (state.1, (created state.2 pair).2))) <$>
        simulateQ (kemAmbientImpl baseImpl) kem.keygen := by
  simp only [impl, poolImpl, StateT.run]
  change (fun result : (Nat × MlKem768PublicKey) × Pool KemSK =>
    (result.1, (state.1, result.2))) <$> (created state.2 <$>
      simulateQ (kemAmbientImpl baseImpl) kem.keygen) = _
  rw [LawfulMonad.map_map]

/-- A nonempty private reservation supplies the next actual slot and publishes precisely the original create reply. -/
theorem reserved_create (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (state : State KemSK)
    (pair : Pair KemSK) (future : List (Pair KemSK)) :
    (reserved baseImpl primitives kem (state.2.keys ++ pair :: future) (.inr (.inr .create))).run state =
      pure ((created state.2 pair).1, (state.1, (created state.2 pair).2)) := by
  simp [reserved, StateT.run]
  rfl

/-- Every other source operation is independent of the private future reservation, including real decapsulation, joint generation and actual service reveals. -/
theorem noncreate_equal (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (pairs : List (Pair KemSK))
    (query : (Spec KemSK).Domain) (notCreate : ¬ IsCreate query) (state : State KemSK) :
    (impl baseImpl primitives kem query).run state = (reserved baseImpl primitives kem pairs query).run state := by
  rcases query with query | (query | query) <;> try rfl
  cases query <;> simp_all [IsCreate, reserved, StateT.run]

/-- Noncreation operations preserve the actual private KEM prefix, even while their full histories, joint state or optional replies change. -/
theorem noncreate_keys (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (query : (Spec KemSK).Domain) (notCreate : ¬ IsCreate query) (state : State KemSK)
    (result : (Spec KemSK).Range query × State KemSK)
    (actual : result ∈ support ((impl baseImpl primitives kem query).run state)) :
    result.2.2.keys = state.2.keys := by
  rcases query with joint | (coin | query)
  case inr.inr =>
    cases query
    case decapsulate index ciphertext =>
      simp only [impl, poolImpl, StateT.run, support_map, Set.mem_image] at actual
      obtain ⟨reply, actual, rfl⟩ := actual
      split at actual <;> simp only [mem_support_bind_iff, mem_support_pure_iff] at actual
      all_goals obtain ⟨answer, _, rfl⟩ := actual
      all_goals rfl
    case create => exact False.elim (notCreate trivial)
    case reveal index =>
      simp only [impl, poolImpl, StateT.run, map_pure, mem_support_pure_iff] at actual
      exact congrArg (fun value => value.2.2.keys) actual
  all_goals simp only [impl, StateT.run, support_map, Set.mem_image] at actual
  all_goals obtain ⟨answer, _, rfl⟩ := actual
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
/-- Actual on-demand KEM creation and bounded private reservation have equal complete evaluated executions, including every private created pair, all joint state and both full observation histories. -/
theorem complete (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) {Result : Type}
    (client : OracleComp (Spec KemSK) Result) (count : Nat)
    (bounded : client.IsQueryBoundP (IsCreate (KemSK := KemSK)) count) (state : State KemSK) :
    𝒮[(simulateQ (impl baseImpl primitives kem) client).run state] =
      𝒮[samplePairs (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count >>= fun future =>
        (simulateQ (reserved baseImpl primitives kem (state.2.keys ++ future)) client).run state] := by
  induction client using OracleComp.inductionOn generalizing count state
  case query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    change 𝒮[(impl baseImpl primitives kem query).run state >>= fun result =>
      (simulateQ (impl baseImpl primitives kem) (next result.1)).run result.2] =
      𝒮[samplePairs (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count >>= fun future =>
        (reserved baseImpl primitives kem (state.2.keys ++ future) query).run state >>= fun result =>
          (simulateQ (reserved baseImpl primitives kem (state.2.keys ++ future)) (next result.1)).run result.2]
    by_cases creates : IsCreate (KemSK := KemSK) query
    case pos =>
      have queryEq : query = .inr (.inr .create) := by
        rcases query with joint | (coin | (_ | ⟨index, ciphertext⟩ | index)) <;> simp_all [IsCreate]
      subst query
      obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (bounded.1.resolve_left (not_not.mpr creates)))
      rw [source_create, samplePairs]
      simp only [bind_assoc, bind_map_left, pure_bind]
      apply evalSPMF_bind_congr
      intro pair _
      simp only [reserved_create, pure_bind]
      simpa only [created, record, List.append_assoc, List.singleton_append] using
        ih (created state.2 pair).1 count (by simpa [IsCreate] using bounded.2 (created state.2 pair).1)
          (state.1, (created state.2 pair).2)
    case neg =>
      have stepEq (future : List (Pair KemSK)) :=
        noncreate_equal baseImpl primitives kem (state.2.keys ++ future) query creates state
      simp_rw [← stepEq]
      rw [PqxdhSecretInputKdf.evalSPMF_sample_comm_vcvioLegacy (samplePairs (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count)
        ((impl baseImpl primitives kem query).run state)]
      apply evalSPMF_bind_congr
      intro result actual
      simpa only [noncreate_keys baseImpl primitives kem query creates state result actual] using
        ih result.1 count (by simpa [creates] using bounded.2 result.1) result.2
  case pure value =>
    simpa only [simulateQ_pure, StateT.run_pure] using
      (unused (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count (pure (value, state))).symm

/-- The private reservation pays the complete actual generator allowance for every reserved slot, including unused slots. -/
theorem reservation_uniform (sampler : ProbComp (Pair KemSK)) (qKeygen count : Nat)
    (bounded : sampler.IsTotalQueryBound qKeygen) :
    (samplePairs sampler count).IsTotalQueryBound (qKeygen * count) := by
  induction count with
  | zero => simp [samplePairs, IsTotalQueryBound]
  | succ count ih =>
      rw [samplePairs, Nat.mul_succ, Nat.add_comm (qKeygen * count) qKeygen]
      apply isTotalQueryBound_bind bounded
      intro pair
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using ih

end BeaconcryptCore.Computational.PqxdhLiveKemReservation

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemReservation.unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemReservation.unused

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemReservation.source_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemReservation.source_create

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemReservation.reserved_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemReservation.reserved_create

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemReservation.noncreate_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemReservation.noncreate_equal

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemReservation.noncreate_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemReservation.noncreate_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemReservation.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemReservation.complete

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemReservation.reservation_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemReservation.reservation_uniform
