import BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter

/-!
Every actual joint-identity, local-coin and KEM source query is charged in the executable CCA router. Selected logical decapsulation and local primitive/base costs retain the source decapsulation cap; uniform work also counts native identity generation and all explicit source coins.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds
open PqxdhKemIndCca PqxdhPrivateKemSource
open PqxdhDynamicKemJointRouter
open PqxdhDynamicKemJointSource (State)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

def IsDecapsulation : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop
  | .inr (.inr request) => PqxdhDynamicKemBounds.IsDecapsulation request
  | _ => False

instance : DecidablePred (IsDecapsulation (KemSK := KemSK)) := fun query => by
  rcases query with joint | (coin | query)
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable (PqxdhDynamicKemBounds.IsDecapsulation query))

set_option backward.isDefEq.respectTransparency false in
/-- Nonuniform CCA classes receive no hidden joint-identity or local-coin requests. Every counted primitive query comes from the exact indexed decapsulation callback. -/
theorem excluded_step (primitives : PqxdhJointIdentity.Primitives)
    (pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
      (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl coin))) (cost : Nat)
    (bounded : ∀ request state, (((pool request).run).run state).IsQueryBoundP predicate
      (if PqxdhDynamicKemBounds.IsDecapsulation request then cost else 0))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK) :
    (((combine ccaCoins primitives pool query).run).run state).IsQueryBoundP predicate
      (if IsDecapsulation (KemSK := KemSK) query then cost else 0) := by
  rcases query with joint | (coin | query)
  · simpa only [combine, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff, IsDecapsulation, ite_false] using
      PqxdhPrivateRootQueryBounds.ccaCoins_excluded ((PqxdhDynamicIdentityPool.lazyImpl primitives joint).run state.1) predicate excluded
  · simpa only [combine, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff, IsDecapsulation, ite_false] using
      PqxdhPrivateRootQueryBounds.ccaCoins_excluded (unifSpec.query coin : ProbComp _) predicate excluded
  · simpa only [combine, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff, IsDecapsulation] using bounded query state.2

/-- The entire combined adaptive source preserves its exact decapsulation-attempt cap for every nonuniform CCA resource class, through all joint replies and stopping branches. -/
theorem excluded_schedule (primitives : PqxdhJointIdentity.Primitives)
    (pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
      (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl coin))) (cost : Nat)
    (perCall : ∀ request state, (((pool request).run).run state).IsQueryBoundP predicate
      (if PqxdhDynamicKemBounds.IsDecapsulation request then cost else 0))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qD : Nat)
    (bounded : client.IsQueryBoundP (IsDecapsulation (KemSK := KemSK)) qD) (state : State KemSK) :
    (((simulateQ (combine ccaCoins primitives pool) client).run).run state).IsQueryBoundP predicate (cost * qD) := by
  induction client using OracleComp.inductionOn generalizing qD state with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    by_cases counted : IsDecapsulation (KemSK := KemSK) query
    · have positive : 0 < qD := bounded.1.resolve_left (not_not.mpr counted)
      obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      rw [Nat.mul_succ, Nat.add_comm (cost * remaining) cost]
      apply isQueryBoundP_bind
        (by simpa only [ite_eq_left counted] using excluded_step primitives pool predicate excluded cost perCall query state)
      rintro ⟨none | answer, after⟩ _
      · trivial
      · exact ih answer remaining (by simpa [counted] using bounded.2 answer) after
    · rw [← Nat.zero_add (cost * qD)]
      apply isQueryBoundP_bind
        (by simpa only [ite_eq_right counted] using excluded_step primitives pool predicate excluded cost perCall query state)
      rintro ⟨none | answer, after⟩ _
      · trivial
      · exact ih answer qD (by simpa [counted] using bounded.2 answer) after

/-- The complete actual combined prechallenge program makes at most one selected CCA decapsulation request per source KEM decapsulation attempt. Identity and local-coin traffic add no such request. -/
theorem pre_decaps (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qD : Nat)
    (bounded : client.IsQueryBoundP (IsDecapsulation (KemSK := KemSK)) qD) (state : State KemSK) :
    (((simulateQ (pre primitives kem selected reservation) client).run).run state).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qD := by
  simpa only [pre, Nat.one_mul] using excluded_schedule primitives
    (PqxdhDynamicKemRouter.pre kem selected reservation) IsMlKemLogicalDecapsulationQuery
    (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) 1
    (fun query poolState => PqxdhDynamicKemBounds.step_bound
      (fun keys index ciphertext => PqxdhLiveKemRouting.pre kem selected keys (default, index) ciphertext)
      selected reservation IsMlKemLogicalDecapsulationQuery 1
      (fun keys index ciphertext => PqxdhLiveKemRouting.pre_decaps kem selected keys (default, index) ciphertext)
      query poolState) client qD bounded state

/-- The complete combined postchallenge program retains the source logical-decapsulation cap while never forwarding its selected challenge ciphertext. -/
theorem post_decaps (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qD : Nat)
    (bounded : client.IsQueryBoundP (IsDecapsulation (KemSK := KemSK)) qD) (state : State KemSK) :
    (((simulateQ (post primitives kem selected reservation challenge candidate) client).run).run state).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qD := by
  have step (keys : PqxdhDynamicKemRouter.Reservation KemSK) (index : Nat) (ciphertext : MlKem768Ciphertext) :=
    PqxdhDynamicKemBounds.post_step_bound kem selected challenge candidate keys index ciphertext IsMlKemLogicalDecapsulationQuery 0 1
      (fun secret => by simpa [IsQueryBoundP, IsMlKemLogicalDecapsulationQuery] using isQueryBoundP_false (kem.decaps secret ciphertext) 0)
      (by split_ifs <;> simp_all [IsMlKemLogicalDecapsulationQuery])
  simpa only [post, Nat.one_mul] using excluded_schedule primitives
    (PqxdhDynamicKemRouter.post kem selected reservation challenge candidate) IsMlKemLogicalDecapsulationQuery
    (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) 1
    (fun query poolState => PqxdhDynamicKemBounds.step_bound
      (PqxdhDynamicKemRouter.postDecapsulation kem selected challenge candidate)
      selected reservation IsMlKemLogicalDecapsulationQuery 1 step query poolState) client qD bounded state

/-- Every nonuniform, nonselected base resource keeps the exact local decapsulation cost multiplied by the actual source attempt cap. Joint source coins remain a separately counted class. -/
theorem pre_base (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qD : Nat)
    (bounded : client.IsQueryBoundP (IsDecapsulation (KemSK := KemSK)) qD) (state : State KemSK)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (noCoins : ∀ coin, ¬ predicate (.inl (.inl coin))) (noSelected : ∀ ciphertext, ¬ predicate (.inr ciphertext))
    (cost : Nat) (localBound : ∀ secret ciphertext,
      (kem.decaps secret ciphertext).IsQueryBoundP (fun query => predicate (.inl query)) cost) :
    (((simulateQ (pre primitives kem selected reservation) client).run).run state).IsQueryBoundP predicate (cost * qD) :=
  excluded_schedule primitives (PqxdhDynamicKemRouter.pre kem selected reservation) predicate noCoins cost
    (fun query poolState => PqxdhDynamicKemBounds.step_bound
      (fun keys index ciphertext => PqxdhLiveKemRouting.pre kem selected keys (default, index) ciphertext)
      selected reservation predicate cost
      (fun keys index ciphertext => PqxdhLiveKemRouting.pre_ambient_bound kem selected keys (default, index)
        ciphertext predicate noSelected cost (fun secret => localBound secret ciphertext)) query poolState)
    client qD bounded state

/-- Postchallenge local base queries obey the same complete source attempt cap; blocked challenge handling adds no base query and does not erase other-key work. -/
theorem post_base (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qD : Nat)
    (bounded : client.IsQueryBoundP (IsDecapsulation (KemSK := KemSK)) qD) (state : State KemSK)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (noCoins : ∀ coin, ¬ predicate (.inl (.inl coin))) (noSelected : ∀ ciphertext, ¬ predicate (.inr ciphertext))
    (cost : Nat) (localBound : ∀ secret ciphertext,
      (kem.decaps secret ciphertext).IsQueryBoundP (fun query => predicate (.inl query)) cost) :
    (((simulateQ (post primitives kem selected reservation challenge candidate) client).run).run state).IsQueryBoundP predicate (cost * qD) := by
  have step (keys : PqxdhDynamicKemRouter.Reservation KemSK) (index : Nat) (ciphertext : MlKem768Ciphertext) :
      (PqxdhDynamicKemRouter.postDecapsulation kem selected challenge candidate keys index ciphertext).IsQueryBoundP predicate cost := by
    simpa only [Nat.add_zero] using PqxdhDynamicKemBounds.post_step_bound kem selected challenge candidate keys index ciphertext
      predicate cost 0 (fun secret => localBound secret ciphertext) (by simp [noSelected])
  exact excluded_schedule primitives (PqxdhDynamicKemRouter.post kem selected reservation challenge candidate)
    predicate noCoins cost
    (fun query poolState => PqxdhDynamicKemBounds.step_bound
      (PqxdhDynamicKemRouter.postDecapsulation kem selected challenge candidate)
      selected reservation predicate cost step query poolState) client qD bounded state

/-- Actual joint-identity creation, whose source draws a fresh 32-byte seed. -/
def IsIdentityCreate : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop
  | .inl query => PqxdhDynamicIdentityPool.IsCreate query
  | _ => False

instance : DecidablePred (IsIdentityCreate (KemSK := KemSK)) := fun query => by
  cases query <;> simp only [IsIdentityCreate] <;> infer_instance

/-- Explicit uniform requests in either the joint-identity or local source interface. -/
def IsUniform : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop
  | .inl query => PqxdhDynamicIdentityPool.IsUniform query
  | .inr (.inl _) => True
  | .inr (.inr _) => False

instance : DecidablePred (IsUniform (KemSK := KemSK)) := fun query => by
  rcases query with query | (coin | query) <;> simp only [IsUniform] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Each source request pays its exact identity-creation and explicit-coin class, plus the full local KEM allowance on every decapsulation attempt. -/
theorem uniform_step (primitives : PqxdhJointIdentity.Primitives)
    (pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
      (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)))))
    (cost : Nat)
    (bounded : ∀ request state, (((pool request).run).run state).IsQueryBoundP IsMlKemUniformQuery
      (if PqxdhDynamicKemBounds.IsDecapsulation request then cost else 0))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK) :
    (((combine ccaCoins primitives pool query).run).run state).IsQueryBoundP IsMlKemUniformQuery
      ((if IsIdentityCreate (KemSK := KemSK) query then 32 else 0) +
       (if IsUniform (KemSK := KemSK) query then 1 else 0) +
       (if IsDecapsulation (KemSK := KemSK) query then cost else 0)) := by
  rcases query with joint | (coin | query)
  · simpa only [combine, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff,
      IsIdentityCreate, IsUniform, IsDecapsulation, ite_false, Nat.add_zero] using
      PqxdhPrivateRootQueryBounds.ccaCoins_uniform ((PqxdhDynamicIdentityPool.lazyImpl primitives joint).run state.1) _
        (PqxdhDynamicIdentityPool.lazyImpl_uniform_step primitives joint state.1)
  · simp only [combine, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff,
      IsIdentityCreate, IsUniform, IsDecapsulation, ite_false, ite_true, Nat.add_zero, Nat.zero_add]
    apply PqxdhPrivateRootQueryBounds.ccaCoins_uniform
    exact (isQueryBoundP_true_iff _ _).mp
      ((isQueryBoundP_query_iff (spec := unifSpec) (p := fun _ => True) coin 1).mpr (by simp))
  · simpa only [combine, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff,
      IsIdentityCreate, IsUniform, IsDecapsulation, ite_false, Nat.zero_add] using bounded query state.2

/-- The complete adaptive source charges every identity seed draw, explicit coin and permitted local KEM callback, including continuations after optional replies. -/
theorem uniform_schedule (primitives : PqxdhJointIdentity.Primitives)
    (pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
      (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)))))
    (cost : Nat)
    (perCall : ∀ request state, (((pool request).run).run state).IsQueryBoundP IsMlKemUniformQuery
      (if PqxdhDynamicKemBounds.IsDecapsulation request then cost else 0))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qCreate qUniform qD : Nat)
    (creates : client.IsQueryBoundP (IsIdentityCreate (KemSK := KemSK)) qCreate)
    (coins : client.IsQueryBoundP (IsUniform (KemSK := KemSK)) qUniform)
    (decaps : client.IsQueryBoundP (IsDecapsulation (KemSK := KemSK)) qD) (state : State KemSK) :
    (((simulateQ (combine ccaCoins primitives pool) client).run).run state).IsQueryBoundP IsMlKemUniformQuery
      (32 * qCreate + qUniform + cost * qD) := by
  induction client using OracleComp.inductionOn generalizing qCreate qUniform qD state with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at creates coins decaps
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    apply (isQueryBoundP_bind (uniform_step primitives pool cost perCall query state)
      (m := 32 * (if IsIdentityCreate (KemSK := KemSK) query then qCreate - 1 else qCreate) +
        (if IsUniform (KemSK := KemSK) query then qUniform - 1 else qUniform) +
        cost * (if IsDecapsulation (KemSK := KemSK) query then qD - 1 else qD))
      (fun result _ => by
        rcases result with ⟨none | answer, after⟩
        · trivial
        · exact ih answer _ _ _ (creates.2 answer) (coins.2 answer) (decaps.2 answer) after)).mono
    have decapAccount :
        (if IsDecapsulation (KemSK := KemSK) query then cost else 0) +
        cost * (if IsDecapsulation (KemSK := KemSK) query then qD - 1 else qD) = cost * qD := by
      by_cases counted : IsDecapsulation (KemSK := KemSK) query
      · have positive : 0 < qD := decaps.1.resolve_left (not_not.mpr counted)
        obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
        simp [counted, Nat.mul_succ, Nat.add_comm]
      · simp [counted]
    have hc := creates.1
    have hu := coins.1
    split_ifs at * <;> simp_all only [not_true_eq_false, false_or] <;> omega

/-- Prechallenge CCA simulation pays every original joint/local coin and every other-key decapsulation's ordinary coin allowance. The separately sampled KEM reservation is not included in this suffix bill. -/
theorem pre_uniform (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qCreate qUniform qD : Nat)
    (creates : client.IsQueryBoundP (IsIdentityCreate (KemSK := KemSK)) qCreate)
    (coins : client.IsQueryBoundP (IsUniform (KemSK := KemSK)) qUniform)
    (decaps : client.IsQueryBoundP (IsDecapsulation (KemSK := KemSK)) qD) (state : State KemSK)
    (cost : Nat) (localBound : ∀ secret ciphertext,
      (kem.decaps secret ciphertext).IsQueryBoundP (fun query => IsMlKemUniformQuery (.inl query)) cost) :
    (((simulateQ (pre primitives kem selected reservation) client).run).run state).IsQueryBoundP
      IsMlKemUniformQuery (32 * qCreate + qUniform + cost * qD) :=
  uniform_schedule primitives (PqxdhDynamicKemRouter.pre kem selected reservation) cost
    (fun query poolState => PqxdhDynamicKemBounds.step_bound
      (fun keys index ciphertext => PqxdhLiveKemRouting.pre kem selected keys (default, index) ciphertext)
      selected reservation IsMlKemUniformQuery cost
      (fun keys index ciphertext => PqxdhLiveKemRouting.pre_ambient_bound kem selected keys (default, index)
        ciphertext IsMlKemUniformQuery (fun _ => by simp [IsMlKemUniformQuery]) cost
        (fun secret => localBound secret ciphertext)) query poolState)
    client qCreate qUniform qD creates coins decaps state

/-- Postchallenge simulation has the same full joint/local coin bill. Returning the challenge candidate adds no draw, and every other-key callback retains its primitive allowance. -/
theorem post_uniform (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qCreate qUniform qD : Nat)
    (creates : client.IsQueryBoundP (IsIdentityCreate (KemSK := KemSK)) qCreate)
    (coins : client.IsQueryBoundP (IsUniform (KemSK := KemSK)) qUniform)
    (decaps : client.IsQueryBoundP (IsDecapsulation (KemSK := KemSK)) qD) (state : State KemSK)
    (cost : Nat) (localBound : ∀ secret ciphertext,
      (kem.decaps secret ciphertext).IsQueryBoundP (fun query => IsMlKemUniformQuery (.inl query)) cost) :
    (((simulateQ (post primitives kem selected reservation challenge candidate) client).run).run state).IsQueryBoundP
      IsMlKemUniformQuery (32 * qCreate + qUniform + cost * qD) := by
  have step (keys : PqxdhDynamicKemRouter.Reservation KemSK) (index : Nat) (ciphertext : MlKem768Ciphertext) :
      (PqxdhDynamicKemRouter.postDecapsulation kem selected challenge candidate keys index ciphertext).IsQueryBoundP IsMlKemUniformQuery cost := by
    simpa only [Nat.add_zero] using PqxdhDynamicKemBounds.post_step_bound kem selected challenge candidate keys index ciphertext
      IsMlKemUniformQuery cost 0 (fun secret => localBound secret ciphertext) (by simp [IsMlKemUniformQuery])
  exact uniform_schedule primitives (PqxdhDynamicKemRouter.post kem selected reservation challenge candidate) cost
    (fun query poolState => PqxdhDynamicKemBounds.step_bound
      (PqxdhDynamicKemRouter.postDecapsulation kem selected challenge candidate)
      selected reservation IsMlKemUniformQuery cost step query poolState)
    client qCreate qUniform qD creates coins decaps state

end BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.excluded_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.excluded_step
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.excluded_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.excluded_schedule
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.pre_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.pre_decaps
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.post_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.post_decaps
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.pre_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.pre_base
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.post_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.post_base
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.uniform_step
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.uniform_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.uniform_schedule
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.pre_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.pre_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.post_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds.post_uniform
