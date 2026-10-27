import BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily

/-!
The actual family reduction retains key generation, private preparation, unused ordinary encapsulation, all local public services, and every private root attempt. It makes at most one initial family call plus one per private attempt. The real challenger adds 32 byte-valued draws; the random challenger has no key and adds at most 64 draws per family call, reusing its full cache on hits. All bounds range over arbitrary possible continuations and charge explicit base/decapsulation sampling costs. Local HMAC, fixed-HKDF, signing/DH, byte and state work remains computation; no evaluated equality is used to infer sampling counts.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds
open PqxdhCorrelatedExtractFamily PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhHiddenRoot
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

def IsCoin : FamilySpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

def IsFamily : FamilySpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsCoin
  | .inl _ => inferInstanceAs (Decidable True)
  | .inr _ => inferInstanceAs (Decidable False)
instance : DecidablePred IsFamily
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

theorem coins_uniform {Result : Type} (client : ProbComp Result) (q : Nat)
    (bounded : client.IsTotalQueryBound q) :
    (coins client).IsQueryBoundP IsCoin q := by
  exact IsQueryBoundP.liftComp_subSpec (p := fun _ => True) (fun _ => Iff.rfl) bounded.isQueryBoundP

theorem coins_family {Result : Type} (client : ProbComp Result) :
    (coins client).IsQueryBoundP IsFamily 0 := by
  exact IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl) (isQueryBoundP_false client 0)

set_option backward.isDefEq.respectTransparency false in
theorem root_bounds (hmac : HmacSha512) (known : KnownPqxdhRootCoordinates) :
    (root hmac known).IsQueryBoundP IsCoin 0 ∧
    (root hmac known).IsQueryBoundP IsFamily 1 := by
  change OracleComp.IsQueryBoundP
      (((FamilySpec.query (.inr (coordinates known)) : OracleComp FamilySpec HmacBlock) >>= fun prk =>
        pure (expandRoot hmac prk))) IsCoin 0 ∧
    OracleComp.IsQueryBoundP
      (((FamilySpec.query (.inr (coordinates known)) : OracleComp FamilySpec HmacBlock) >>= fun prk =>
        pure (expandRoot hmac prk))) IsFamily 1
  simp only [isQueryBoundP_query_bind_iff, IsCoin, IsFamily, isQueryBoundP_pure]
  simp

theorem post_uniform_step
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (request : (LocalPostSpec baseSpec).Domain) :
    (post source hmac baseImpl kem secret challenge request).IsQueryBoundP IsCoin
      ((if PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery request then 1 else 0) +
       (if PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery request then qBase else 0) +
       (if RoutedClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery request then qDecap else 0)) := by
  rcases request with ((coin | query) | ciphertext) | privateRequest
  · simp only [
      ite_eq_left (show PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery
        (.inl (.inl (.inl coin))) from True.intro),
      ite_eq_right (show ¬ PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery
        (.inl (.inl (.inl coin))) from id),
      ite_eq_right (show ¬ RoutedClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery
        (.inl (.inl (.inl coin))) from id), Nat.add_zero]
    apply coins_uniform
    change (simulateQ (kemAmbientImpl baseImpl)
      ((unifSpec + baseSpec).query (.inl coin))).IsTotalQueryBound 1
    rw [simulateQ_spec_query]
    exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  · simp only [
      ite_eq_right (show ¬ PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery
        (.inl (.inl (.inr query))) from id),
      ite_eq_left (show PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery
        (.inl (.inl (.inr query))) from True.intro),
      ite_eq_right (show ¬ RoutedClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery
        (.inl (.inl (.inr query))) from id), Nat.zero_add, Nat.add_zero]
    apply coins_uniform
    change (simulateQ (kemAmbientImpl baseImpl)
      ((unifSpec + baseSpec).query (.inr query))).IsTotalQueryBound qBase
    rw [simulateQ_spec_query]
    exact baseBound query
  · simp only [
      ite_eq_right (show ¬ PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery
        (.inl (.inr ciphertext)) from id),
      ite_eq_right (show ¬ PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery
        (.inl (.inr ciphertext)) from id),
      ite_eq_left (show RoutedClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery
        (.inl (.inr ciphertext)) from True.intro), Nat.zero_add]
    apply coins_uniform
    change (simulateQ (kemAmbientImpl baseImpl)
      (if ciphertext = challenge then pure none else kem.decaps secret ciphertext)).IsTotalQueryBound qDecap
    split
    · simp only [simulateQ_pure]
      trivial
    · exact decapBound ciphertext
  · simp only [
      ite_eq_right (show ¬ PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery
        (.inr privateRequest) from id),
      ite_eq_right (show ¬ PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery
        (.inr privateRequest) from id),
      ite_eq_left (show RoutedClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery
        (.inr privateRequest) from True.intro), Nat.zero_add]
    simp only [post]
    split
    · exact ((isQueryBoundP_map_iff _ some 0).mpr (root_bounds hmac privateRequest.coordinates).1).mono (Nat.zero_le _)
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        coins_uniform _ qDecap (decapBound privateRequest.ciphertext)

theorem post_uniform_run {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (client : OracleComp (LocalPostSpec baseSpec) Result)
    (qUniform qBaseCalls qDecapCalls : Nat)
    (uniforms : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery) qUniform)
    (bases : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery) qBaseCalls)
    (decaps : client.IsQueryBoundP (RoutedClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) qDecapCalls) :
    (simulateQ (post source hmac baseImpl kem secret challenge) client).IsQueryBoundP IsCoin
      (qUniform + qBase * qBaseCalls + qDecap * qDecapCalls) := by
  induction client using OracleComp.inductionOn generalizing qUniform qBaseCalls qDecapCalls with
  | pure value => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at uniforms bases decaps
      simp only [simulateQ_bind, simulateQ_spec_query]
      apply (isQueryBoundP_bind
        (post_uniform_step source hmac baseImpl kem secret challenge qBase qDecap baseBound decapBound request)
        (fun answer _ => ih answer _ _ _ (uniforms.2 answer) (bases.2 answer) (decaps.2 answer))).mono
      have hu := uniforms.1
      have hb := bases.1
      have hd := decaps.1
      have baseStep : ∀ n, 0 < n → qBase * (n - 1) + qBase = qBase * n := by
        intro n hn
        rw [← Nat.mul_succ]
        congr 1
        omega
      have decapStep : ∀ n, 0 < n → qDecap * (n - 1) + qDecap = qDecap * n := by
        intro n hn
        rw [← Nat.mul_succ]
        congr 1
        omega
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or]
      all_goals try have := baseStep qBaseCalls (by omega)
      all_goals try have := decapStep qDecapCalls (by omega)
      all_goals omega

/-- Actual processing counts both public and private decapsulation work, preserving every failed private result. -/
theorem post_uniform_bound {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (client : OracleComp (LocalPostSpec baseSpec) Result) (u b d r : Nat)
    (bounded : PostBounds client u b d r) :
    (simulateQ (post source hmac baseImpl kem secret challenge) client).IsQueryBoundP IsCoin
      (u + qBase * b + qDecap * (d + r)) := by
  apply post_uniform_run source hmac baseImpl kem secret challenge qBase qDecap baseBound decapBound
    client u b (d + r) bounded.uniforms bounded.bases
  apply IsQueryBoundP.of_imp _ (PqxdhProjectionCollisions.isQueryBoundP_or bounded.decaps bounded.privateRoots)
  intro request selected
  cases request with
  | inl request => exact Or.inl selected
  | inr request => exact Or.inr trivial


/-- Only matching private requests make a family query; every private attempt is charged in the cap. -/
theorem post_family_step
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (request : (LocalPostSpec baseSpec).Domain) :
    (post source hmac baseImpl kem secret challenge request).IsQueryBoundP IsFamily
      (if IsPrivateRoot (baseSpec := baseSpec) request then 1 else 0) := by
  cases request with
  | inl request => exact coins_family _
  | inr request =>
      simp only [post, IsPrivateRoot]
      split
      · exact (isQueryBoundP_map_iff _ some 1).mpr (root_bounds hmac request.coordinates).2
      · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using (coins_family
          (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret request.ciphertext))).mono (by omega)

theorem post_family_bound {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (LocalPostSpec baseSpec) Result) (q : Nat)
    (bounded : client.IsQueryBoundP (IsPrivateRoot (baseSpec := baseSpec)) q) :
    (simulateQ (post source hmac baseImpl kem secret challenge) client).IsQueryBoundP IsFamily q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure result => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_query_bind]
      have combined := isQueryBoundP_bind (post_family_step source hmac baseImpl kem secret challenge request)
        (fun answer _ => ih answer _ (bounded.2 answer))
      apply combined.mono
      by_cases selected : IsPrivateRoot (baseSpec := baseSpec) request
      · have positive := bounded.1.resolve_left (not_not.mpr selected)
        simp only [selected, ite_true]
        omega
      · simp only [selected, ite_false, Nat.zero_add, le_refl]

/-- The reduction still performs actual key generation, the full private preparation, and ordinary encapsulation. -/
theorem prepare_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (bounded : SamplerBounds baseImpl kem protocol qKeygen qEncap qBase qDecap
      uPre bPre dPre uPost bPost dPost privatePost) :
    (prepare baseImpl kem protocol).IsTotalQueryBound
      (qKeygen + ((uPre + qBase * bPre + qDecap * dPre) + qEncap)) := by
  unfold prepare
  apply isTotalQueryBound_bind bounded.keygen
  rintro ⟨publicKey, secretKey⟩
  apply isTotalQueryBound_bind
    (PqxdhPrivateRootGameBudgets.evalKem_uniform_bound baseImpl kem secretKey qBase qDecap bounded.base
      (bounded.decaps secretKey) _ _ _ _
      (bounded.prepare publicKey).1 (bounded.prepare publicKey).2.1 (bounded.prepare publicKey).2.2)
  intro state
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using bounded.encaps publicKey

/-- An optional initial root adds one family request and no local uniform request. -/
theorem resume_bounds
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (prepared : Prepared protocol KemSK) (qBase qDecap u b d r : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps prepared.secretKey ciphertext)).IsTotalQueryBound qDecap)
    (bounded : ∀ initial, PostBounds
      (protocol.resume prepared.publicKey prepared.ciphertext prepared.state initial) u b d r) :
    (resume source hmac baseImpl kem protocol prepared).IsQueryBoundP IsCoin
      (u + qBase * b + qDecap * (d + r)) ∧
    (resume source hmac baseImpl kem protocol prepared).IsQueryBoundP IsFamily (1 + r) := by
  unfold resume
  cases initial : protocol.initialCoordinates prepared.publicKey prepared.ciphertext prepared.state with
  | none =>
      simp only [pure_bind]
      exact ⟨post_uniform_bound source hmac baseImpl kem _ _ _ _ baseBound decapBound _ _ _ _ _ (bounded none),
        (post_family_bound source hmac baseImpl kem _ _ _ _ (bounded none).privateRoots).mono (by omega)⟩
  | some known =>
      constructor
      · have rootBound := (isQueryBoundP_map_iff _ some 0).mpr (root_bounds hmac known).1
        simpa only [Nat.zero_add] using isQueryBoundP_bind rootBound (fun answer _ =>
          post_uniform_bound source hmac baseImpl kem _ _ _ _ baseBound decapBound _ _ _ _ _ (bounded answer))
      · have rootBound := (isQueryBoundP_map_iff _ some 1).mpr (root_bounds hmac known).2
        exact isQueryBoundP_bind rootBound (fun answer _ =>
          post_family_bound source hmac baseImpl kem _ _ _ _ (bounded answer).privateRoots)

/-- Logical family calls and all locally interpreted coin calls are bounded on the actual reduction program. -/
theorem reduction_bounds
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (bounded : SamplerBounds baseImpl kem protocol qKeygen qEncap qBase qDecap
      uPre bPre dPre uPost bPost dPost privatePost) :
    (PqxdhCorrelatedExtractFamily.reduction source hmac baseImpl kem protocol).IsQueryBoundP IsCoin
      (qKeygen + ((uPre + qBase * bPre + qDecap * dPre) + qEncap) +
        (uPost + qBase * bPost + qDecap * (dPost + privatePost))) ∧
    (PqxdhCorrelatedExtractFamily.reduction source hmac baseImpl kem protocol).IsQueryBoundP IsFamily
      (1 + privatePost) := by
  unfold PqxdhCorrelatedExtractFamily.reduction
  constructor
  · apply isQueryBoundP_bind (coins_uniform _ _ (prepare_uniform_bound baseImpl kem protocol
      _ _ _ _ _ _ _ _ _ _ _ bounded))
    intro prepared _
    exact (resume_bounds source hmac baseImpl kem protocol prepared _ _ _ _ _ _ bounded.base
      (bounded.decaps prepared.secretKey) (bounded.resume _ _ _)).1
  · simpa only [Nat.zero_add] using isQueryBoundP_bind (coins_family (prepare baseImpl kem protocol))
      (fun prepared _ => (resume_bounds source hmac baseImpl kem protocol prepared _ _ _ _ _ _ bounded.base
        (bounded.decaps prepared.secretKey) (bounded.resume _ _ _)).2)

/-- Real family evaluation performs local HMAC work without additional sampling. -/
theorem real_step (hmac : HmacSha512) (secret : MlKemSharedSecret) (request : FamilySpec.Domain) :
    (realImpl hmac secret request).IsTotalQueryBound (if IsCoin request then 1 else 0) := by
  cases request with
  | inl request => exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | inr request => trivial

theorem real_run_uniform {Result : Type} (hmac : HmacSha512) (secret : MlKemSharedSecret)
    (client : OracleComp FamilySpec Result) (q : Nat) (bounded : client.IsQueryBoundP IsCoin q) :
    (simulateQ (realImpl hmac secret) client).IsTotalQueryBound q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure result => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_query_bind]
      apply (isTotalQueryBound_bind (real_step hmac secret request)
        (fun answer => ih answer _ (bounded.2 answer))).mono
      by_cases selected : IsCoin request
      · have positive := bounded.1.resolve_left (not_not.mpr selected)
        simp only [selected, ite_true]
        omega
      · simp only [selected, ite_false, Nat.zero_add, le_refl]

/-- The real family challenger pays its single hidden 32-byte key sample in addition to the client's coins. -/
theorem realGame_uniform_bound (hmac : HmacSha512) (client : OracleComp FamilySpec Bool)
    (q : Nat) (bounded : client.IsQueryBoundP IsCoin q) :
    (realGame hmac client).IsTotalQueryBound (32 + q) := by
  exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
    (fun secret => real_run_uniform hmac secret client q bounded)

set_option backward.isDefEq.respectTransparency false in
/-- A random-family miss samples 64 bytes and a cache hit samples none; explicit client coins are forwarded once. -/
theorem random_step (request : FamilySpec.Domain) (cache : ExtractOracle.QueryCache) :
    ((randomImpl request).run cache).IsTotalQueryBound
      ((if IsCoin request then 1 else 0) + (if IsFamily request then 64 else 0)) := by
  cases request with
  | inl request =>
      change OracleComp.IsTotalQueryBound
        (((unifSpec.query request : ProbComp (unifSpec.Range request)) >>= fun answer =>
          pure (answer, cache))) 1
      exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | inr request =>
      change ((randomImpl (.inr request)).run cache).IsTotalQueryBound 64
      cases hit : cache request with
      | none =>
          rw [random_miss request cache hit]
          simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
            CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64
      | some prk =>
          rw [random_hit request cache prk hit]
          trivial

/-- The complete random-family state is retained throughout every possible continuation. -/
theorem random_run_uniform {Result : Type} (client : OracleComp FamilySpec Result)
    (qCoins qFamily : Nat) (coinBound : client.IsQueryBoundP IsCoin qCoins)
    (familyBound : client.IsQueryBoundP IsFamily qFamily) (cache : ExtractOracle.QueryCache) :
    ((simulateQ randomImpl client).run cache).IsTotalQueryBound (qCoins + 64 * qFamily) := by
  induction client using OracleComp.inductionOn generalizing qCoins qFamily cache with
  | pure result => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at coinBound familyBound
      rw [simulateQ_query_bind, StateT.run_bind]
      apply (isTotalQueryBound_bind (random_step request cache)
        (fun answer => ih answer.1 _ _ (coinBound.2 answer.1) (familyBound.2 answer.1) answer.2)).mono
      have hc := coinBound.1
      have hf := familyBound.1
      have familyStep : ∀ n, 0 < n → 64 * (n - 1) + 64 = 64 * n := by
        intro n hn
        omega
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or]
      all_goals try have := familyStep qFamily (by omega)
      all_goals omega

/-- The random challenger has no sampled family key; only new table entries add randomness. -/
theorem randomGame_uniform_bound (client : OracleComp FamilySpec Bool) (qCoins qFamily : Nat)
    (coinBound : client.IsQueryBoundP IsCoin qCoins) (familyBound : client.IsQueryBoundP IsFamily qFamily) :
    (randomGame client).IsTotalQueryBound (qCoins + 64 * qFamily) := by
  simpa only [randomGame, StateT.run'_eq, IsTotalQueryBound, isQueryBound_map_iff] using
    random_run_uniform client qCoins qFamily coinBound familyBound ∅

/-- Both complete family challengers retain all preparation and post work, with their own actual sampling costs. -/
theorem reduction_uniform_ledger
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (bounded : SamplerBounds baseImpl kem protocol qKeygen qEncap qBase qDecap
      uPre bPre dPre uPost bPost dPost privatePost) :
    let client := PqxdhCorrelatedExtractFamily.reduction source hmac baseImpl kem protocol
    let Q := qKeygen + ((uPre + qBase * bPre + qDecap * dPre) + qEncap) +
      (uPost + qBase * bPost + qDecap * (dPost + privatePost))
    (realGame hmac client).IsTotalQueryBound (32 + Q) ∧
    (randomGame client).IsTotalQueryBound (Q + 64 * (1 + privatePost)) := by
  dsimp only
  have caps := reduction_bounds source hmac baseImpl kem protocol
    _ _ _ _ _ _ _ _ _ _ _ bounded
  exact ⟨realGame_uniform_bound hmac _ _ caps.1, randomGame_uniform_bound _ _ _ caps.1 caps.2⟩

end BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.coins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.coins_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.coins_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.coins_family

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.root_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.root_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.post_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.post_uniform_step

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.post_uniform_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.post_uniform_run

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.post_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.post_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.post_family_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.post_family_step

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.post_family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.post_family_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.prepare_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.prepare_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.resume_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.resume_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.reduction_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.real_step' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.real_step

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.real_run_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.real_run_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.realGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.realGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.random_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.random_step

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.random_run_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.random_run_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.randomGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.randomGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.reduction_uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds.reduction_uniform_ledger
