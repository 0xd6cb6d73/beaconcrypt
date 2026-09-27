import BeaconcryptCore.Computational.PqxdhDynamicKemRouter

/-!
Dynamic creation/reveal routing has no hidden primitive calls. The original actual KEM reservation is separately charged; every adaptive logical decapsulation attempt, including missing handles and stopped suffixes, contributes to the source bound. Local other-key decapsulation pays its full uniform/base allowance. No running-time claim is made for list lookup or retained transcripts.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemBounds
open PqxdhDynamicKemRouter PqxdhKemIndCca PqxdhPrivateKemSource
open PqxdhLiveKemBirth (Query PoolSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

def IsDecapsulation : Query → Prop
  | .decapsulate _ _ => True
  | _ => False

instance : DecidablePred IsDecapsulation := fun query => by
  cases query <;> simp only [IsDecapsulation] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Each callback pays its actual internal decapsulation allowance; creation consumes a previously charged reservation and reveals only local existing values. -/
theorem step_bound
    (decapsulation : Reservation KemSK → Nat → MlKem768Ciphertext →
      OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret))
    (selected : Nat) (reservation : Reservation KemSK)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (cost : Nat) (bounded : ∀ keys index ciphertext, (decapsulation keys index ciphertext).IsQueryBoundP predicate cost)
    (query : Query) (state : State KemSK) :
    (((router decapsulation selected reservation query).run).run state).IsQueryBoundP predicate
      (if IsDecapsulation query then cost else 0) := by
  cases query with
  | create =>
      simp only [router, OptionT.run_mk, StateT.run, IsDecapsulation, ite_false]
      split <;> trivial
  | reveal index =>
      simp only [router, OptionT.run_mk, StateT.run, IsDecapsulation, ite_false]
      split
      · trivial
      · split <;> trivial
  | decapsulate index ciphertext =>
      simpa only [router, OptionT.run_mk, StateT.run, IsDecapsulation, ite_true,
        bind_pure_comp, isQueryBoundP_map_iff] using bounded (lookup reservation state) index ciphertext

/-- The complete stopped adaptive schedule pays its source decapsulation-attempt cap times the per-call cost, without dropping rejection or abort paths. -/
theorem schedule_bound
    (decapsulation : Reservation KemSK → Nat → MlKem768Ciphertext →
      OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret))
    (selected : Nat) (reservation : Reservation KemSK)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (cost : Nat) (perCall : ∀ keys index ciphertext, (decapsulation keys index ciphertext).IsQueryBoundP predicate cost)
    (client : OracleComp (PoolSpec KemSK) Result) (qD : Nat)
    (bounded : client.IsQueryBoundP IsDecapsulation qD) (state : State KemSK) :
    (((simulateQ (router decapsulation selected reservation) client).run).run state).IsQueryBoundP predicate (cost * qD) := by
  induction client using OracleComp.inductionOn generalizing qD state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
      by_cases counted : IsDecapsulation query
      · have positive : 0 < qD := bounded.1.resolve_left (not_not.mpr counted)
        obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
        rw [Nat.mul_succ, Nat.add_comm (cost * remaining) cost]
        apply isQueryBoundP_bind
          (by simpa only [ite_eq_left counted] using step_bound decapsulation selected reservation predicate cost perCall query state)
        rintro ⟨none | answer, after⟩ _
        · trivial
        · exact ih answer remaining (by simpa [counted] using bounded.2 answer) after
      · rw [← Nat.zero_add (cost * qD)]
        apply isQueryBoundP_bind
          (by simpa only [ite_eq_right counted] using step_bound decapsulation selected reservation predicate cost perCall query state)
        rintro ⟨none | answer, after⟩ _
        · trivial
        · exact ih answer qD (by simpa [counted] using bounded.2 answer) after

/-- Dynamic prechallenge routing uses at most one selected-key oracle request per actual decapsulation attempt. -/
theorem pre_decaps (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK) (client : OracleComp (PoolSpec KemSK) Result)
    (qD : Nat) (bounded : client.IsQueryBoundP IsDecapsulation qD) (state : State KemSK) :
    (((simulateQ (pre kem selected reservation) client).run).run state).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qD := by
  simpa only [pre, Nat.one_mul] using schedule_bound
    (fun keys index ciphertext => PqxdhLiveKemRouting.pre kem selected keys (default, index) ciphertext)
    selected reservation IsMlKemLogicalDecapsulationQuery 1
    (fun keys index ciphertext => PqxdhLiveKemRouting.pre_decaps kem selected keys (default, index) ciphertext)
    client qD bounded state

/-- Uniform and base costs of every actual other-key primitive call are retained independently of the selected logical decapsulation cap. -/
theorem pre_ambient (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK) (client : OracleComp (PoolSpec KemSK) Result)
    (qD : Nat) (bounded : client.IsQueryBoundP IsDecapsulation qD) (state : State KemSK)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ ciphertext, ¬ predicate (.inr ciphertext)) (cost : Nat)
    (localBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => predicate (.inl query)) cost) :
    (((simulateQ (pre kem selected reservation) client).run).run state).IsQueryBoundP predicate (cost * qD) :=
  schedule_bound _ selected reservation predicate cost
    (fun keys index ciphertext => PqxdhLiveKemRouting.pre_ambient_bound kem selected keys (default, index)
      ciphertext predicate excluded cost (fun secret => localBound secret ciphertext)) client qD bounded state

/-- Postchallenge local work keeps its ordinary costs. The exact selected challenge is handled internally and is never submitted to the CCA oracle. -/
theorem post_step_bound (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (keys : Reservation KemSK) (index : Nat) (ciphertext : MlKem768Ciphertext)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qLocal qSelected : Nat)
    (localBound : ∀ secret, (kem.decaps secret ciphertext).IsQueryBoundP (fun query => predicate (.inl query)) qLocal)
    (selectedBound : (if ciphertext = challenge then 0 else if predicate (.inr ciphertext) then 1 else 0) ≤ qSelected) :
    (postDecapsulation kem selected challenge candidate keys index ciphertext).IsQueryBoundP predicate (qLocal + qSelected) := by
  unfold postDecapsulation
  split <;> try trivial
  split
  · split
    · trivial
    · apply (isQueryBoundP_query_iff (spec := MlKemCCAOracleSpec baseSpec)
        (p := predicate) (.inr ciphertext) _).2
      intro counted
      simp_all
      omega
  · split
    · trivial
    · exact (PqxdhPrivateRootQueryBounds.ccaAmbient_bound _ predicate qLocal (localBound _)).mono (Nat.le_add_right _ _)

/-- The entire adaptive postchallenge source has the same logical decapsulation cap as its original attempt schedule. -/
theorem post_decaps (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (client : OracleComp (PoolSpec KemSK) Result)
    (qD : Nat) (bounded : client.IsQueryBoundP IsDecapsulation qD) (state : State KemSK) :
    (((simulateQ (post kem selected reservation challenge candidate) client).run).run state).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qD := by
  have step (keys : Reservation KemSK) (index : Nat) (ciphertext : MlKem768Ciphertext) :=
    post_step_bound kem selected challenge candidate keys index ciphertext IsMlKemLogicalDecapsulationQuery 0 1
      (fun secret => by simpa [IsQueryBoundP, IsMlKemLogicalDecapsulationQuery] using isQueryBoundP_false (kem.decaps secret ciphertext) 0)
      (by split_ifs <;> simp_all [IsMlKemLogicalDecapsulationQuery])
  simpa only [post, Nat.one_mul] using schedule_bound
    (postDecapsulation kem selected challenge candidate) selected reservation IsMlKemLogicalDecapsulationQuery 1
    step client qD bounded state

/-- The same postchallenge source schedule retains the actual uniform/base cost of each local other-key decapsulation. -/
theorem post_ambient (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (client : OracleComp (PoolSpec KemSK) Result) (qD : Nat)
    (bounded : client.IsQueryBoundP IsDecapsulation qD) (state : State KemSK)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ ciphertext, ¬ predicate (.inr ciphertext)) (cost : Nat)
    (localBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => predicate (.inl query)) cost) :
    (((simulateQ (post kem selected reservation challenge candidate) client).run).run state).IsQueryBoundP predicate (cost * qD) := by
  apply schedule_bound _ selected reservation predicate cost _ client qD bounded state
  intro keys index ciphertext
  simpa only [Nat.add_zero] using post_step_bound kem selected challenge candidate keys index ciphertext predicate cost 0
    (fun secret => localBound secret ciphertext) (by split_ifs <;> simp_all)

def IsChallenge (challenge : MlKem768Ciphertext) : (MlKemCCAOracleSpec baseSpec).Domain → Prop
  | .inl _ => False
  | .inr ciphertext => ciphertext = challenge

instance (challenge : MlKem768Ciphertext) : DecidablePred (IsChallenge (baseSpec := baseSpec) challenge) := fun query => by
  cases query <;> simp only [IsChallenge] <;> infer_instance

/-- The selected challenge ciphertext is never queried to the ordinary CCA oracle, even during adaptive later creation and compromise attempts. -/
theorem challenge_blocked (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (client : OracleComp (PoolSpec KemSK) Result) (qD : Nat)
    (bounded : client.IsQueryBoundP IsDecapsulation qD) (state : State KemSK) :
    (((simulateQ (post kem selected reservation challenge candidate) client).run).run state).IsQueryBoundP
      (IsChallenge (baseSpec := baseSpec) challenge) 0 := by
  classical
  have step (keys : Reservation KemSK) (index : Nat) (ciphertext : MlKem768Ciphertext) :=
    post_step_bound kem selected challenge candidate keys index ciphertext (IsChallenge (baseSpec := baseSpec) challenge) 0 0
      (fun secret => by simpa [IsQueryBoundP, IsChallenge] using isQueryBoundP_false (kem.decaps secret ciphertext) 0)
      (by split_ifs <;> simp_all [IsChallenge])
  simpa only [post, Nat.zero_mul] using schedule_bound
    (postDecapsulation kem selected challenge candidate) selected reservation (IsChallenge (baseSpec := baseSpec) challenge) 0
    step client qD bounded state

end BeaconcryptCore.Computational.PqxdhDynamicKemBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemBounds.step_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemBounds.step_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemBounds.schedule_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemBounds.schedule_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemBounds.pre_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemBounds.pre_decaps
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemBounds.pre_ambient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemBounds.pre_ambient
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemBounds.post_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemBounds.post_step_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemBounds.post_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemBounds.post_decaps
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemBounds.post_ambient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemBounds.post_ambient
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemBounds.challenge_blocked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemBounds.challenge_blocked
