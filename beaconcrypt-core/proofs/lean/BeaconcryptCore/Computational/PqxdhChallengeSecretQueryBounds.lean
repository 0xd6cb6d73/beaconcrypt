import BeaconcryptCore.Computational.PqxdhChallengeSecretRouting
import BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets
import BeaconcryptCore.Computational.PqxdhProjectionCollisions

/-!
Every public CCA class and every private root attempt is bounded through all possible continuations. The reduction preserves public uniform/base caps and charges at most one ordinary decapsulation per private attempt. Actual source and challenger programs have independently checked interpreted sampling ledgers, retaining real key generation, encapsulation and decapsulation effects. The source has no unused challenger sample; fixed/native wrappers add 32 byte-valued draws and the fair game adds one bit draw. These caps do not make local functional DH, root/HKDF, memory or native interface work free, and they do not instantiate the global source schedule.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds
open PqxdhChallengeSecretRouting PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhHiddenRoot PqxdhJointKdfGame PqxdhSecretInputKdf

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- A private derivation can forward only its original ciphertext as a logical decapsulation query. -/
def RoutedClass (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) :
    (LocalPostSpec baseSpec).Domain → Prop
  | .inl request => predicate request
  | .inr request => predicate (.inr request.ciphertext)

instance (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    DecidablePred (RoutedClass predicate)
  | .inl request => inferInstanceAs (Decidable (predicate request))
  | .inr request => inferInstanceAs (Decidable (predicate (.inr request.ciphertext)))

/-- Every request consumes at most one selected ordinary query; matching private requests consume zero. -/
theorem route_step
    (source : FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (request : (LocalPostSpec baseSpec).Domain) :
    (route source challenge supplied request).IsQueryBoundP predicate
      (if RoutedClass predicate request then 1 else 0) := by
  classical
  cases request with
  | inl request =>
      simp only [route, RoutedClass]
      split <;> simp_all
  | inr request =>
      by_cases same : request.ciphertext = challenge
      · simp only [route, same, if_true, pure_bind]
        trivial
      · simp only [route, same, if_false, RoutedClass]
        change (((MlKemCCAOracleSpec baseSpec).query (.inr request.ciphertext) :
          OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret)) >>=
          fun (recovered : Option MlKemSharedSecret) =>
            pure (recovered.map (productionHiddenRoot source request.coordinates))).IsQueryBoundP
              predicate (if predicate (.inr request.ciphertext) then 1 else 0)
        simp only [isQueryBoundP_query_bind_iff, isQueryBoundP_pure]
        split <;> simp_all

/-- The bound covers every original continuation, including rejected and repeated requests. -/
theorem route_class_bound {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (client : OracleComp (LocalPostSpec baseSpec) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (RoutedClass predicate) bound) :
    (simulateQ (route source challenge supplied) client).IsQueryBoundP predicate bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure result => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_query_bind]
      have combined := isQueryBoundP_bind (route_step source challenge supplied predicate request)
        (fun answer _ => ih answer _ (bounded.2 answer))
      apply combined.mono
      by_cases selected : RoutedClass predicate request
      · have positive := bounded.1.resolve_left (not_not.mpr selected)
        simp only [selected, if_true]
        omega
      · simp only [selected, if_false, Nat.zero_add, le_refl]

/-- A class of original public CCA requests; private requests do not belong to it. -/
def PublicClass (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) :
    (LocalPostSpec baseSpec).Domain → Prop
  | .inl request => predicate request
  | .inr _ => False

/-- Every private root attempt is counted, regardless of ciphertext equality or optional reply. -/
def IsPrivateRoot : (LocalPostSpec baseSpec).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    DecidablePred (PublicClass predicate)
  | .inl request => inferInstanceAs (Decidable (predicate request))
  | .inr _ => inferInstanceAs (Decidable False)

instance : DecidablePred (@IsPrivateRoot ι baseSpec)
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

/-- Uniform and base classes inherit their original caps because private root processing adds neither kind of ordinary request. -/
theorem route_public_bound {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (notDecapsulation : ∀ ciphertext, ¬ predicate (.inr ciphertext))
    (client : OracleComp (LocalPostSpec baseSpec) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (PublicClass predicate) bound) :
    (simulateQ (route source challenge supplied) client).IsQueryBoundP predicate bound := by
  apply route_class_bound source challenge supplied predicate client bound
  apply IsQueryBoundP.of_imp (p' := PublicClass predicate) _ bounded
  intro request selected
  cases request with
  | inl request => exact selected
  | inr request => exact (notDecapsulation request.ciphertext selected).elim

/-- Both original public decapsulation requests and private attempts are charged before any challenge branch is taken. -/
theorem route_decapsulation_bound {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (client : OracleComp (LocalPostSpec baseSpec) Result) (publicBound privateBound : Nat)
    (publics : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) publicBound)
    (privates : client.IsQueryBoundP (IsPrivateRoot (baseSpec := baseSpec)) privateBound) :
    (simulateQ (route source challenge supplied) client).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery (publicBound + privateBound) := by
  apply route_class_bound source challenge supplied IsMlKemLogicalDecapsulationQuery client _
  have combined := PqxdhProjectionCollisions.isQueryBoundP_or publics privates
  apply IsQueryBoundP.of_imp _ combined
  intro request selected
  cases request with
  | inl request => exact Or.inl selected
  | inr request => exact Or.inr trivial

/-- Independent caps on all public classes and every private root attempt. -/
structure PostBounds {Result : Type} (client : OracleComp (LocalPostSpec baseSpec) Result)
    (uniform base decapsulation privateRoot : Nat) : Prop where
  uniforms : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery) uniform
  bases : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery) base
  decaps : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) decapsulation
  privateRoots : client.IsQueryBoundP (IsPrivateRoot (baseSpec := baseSpec)) privateRoot

/-- The ordinary distinguisher has the original public budgets plus at most one decapsulation per private attempt. -/
theorem reduction_bounds
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (prepare : ∀ publicKey,
      (protocol.prepare publicKey).IsQueryBoundP IsMlKemUniformQuery uPre ∧
      (protocol.prepare publicKey).IsQueryBoundP IsMlKemBaseQuery bPre ∧
      (protocol.prepare publicKey).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dPre)
    (resume : ∀ publicKey ciphertext state initial,
      PostBounds (protocol.resume publicKey ciphertext state initial) uPost bPost dPost privatePost) :
    (reduction source kem protocol).MakesAtMostQueries uPre bPre dPre uPost bPost (dPost + privatePost) := by
  constructor
  · exact prepare
  · intro transcript supplied
    have bounded := resume transcript.publicKey transcript.ciphertext transcript.context
      ((protocol.initialCoordinates transcript.publicKey transcript.ciphertext transcript.context).map
        (fun coordinates => productionHiddenRoot source coordinates supplied))
    exact ⟨route_public_bound source _ _ _ (fun _ => by simp [IsMlKemUniformQuery]) _ _ bounded.uniforms,
      route_public_bound source _ _ _ (fun _ => by simp [IsMlKemBaseQuery]) _ _ bounded.bases,
      route_decapsulation_bound source _ _ _ _ _ bounded.decaps bounded.privateRoots⟩

/-- Complete fixed real and random challengers pay key generation, actual encapsulation, all interpreted primitive effects and the branch-independent 32-byte sample. -/
theorem fixed_world_uniform_bound
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (prepare : ∀ publicKey,
      (protocol.prepare publicKey).IsQueryBoundP IsMlKemUniformQuery uPre ∧
      (protocol.prepare publicKey).IsQueryBoundP IsMlKemBaseQuery bPre ∧
      (protocol.prepare publicKey).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dPre)
    (resume : ∀ publicKey ciphertext state initial,
      PostBounds (protocol.resume publicKey ciphertext state initial) uPost bPost dPost privatePost)
    (bit : Bool) :
    (simulateQ (kemAmbientImpl baseImpl)
      (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl)) (reduction source kem protocol) bit)).IsTotalQueryBound
      (qKeygen + ((uPre + qBase * bPre + qDecap * dPre) +
        (qEncap + (32 + (uPost + qBase * bPost + qDecap * (dPost + privatePost)))))) := by
  exact PqxdhPrivateRootGameBudgets.oneKeyBranch_uniform_bound baseImpl kem (reduction source kem protocol)
    _ _ _ _ _ _ _ _ _ _ keygenBound encapBound baseBound decapBound
    (reduction_bounds source kem protocol _ _ _ _ _ _ _ prepare resume) bit

/-- Actual source processing charges every private decapsulation, including at the challenge ciphertext. -/
theorem actual_step_uniform
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (request : (LocalPostSpec baseSpec).Domain) :
    (simulateQ (kemAmbientImpl baseImpl) (actualImpl source kem secret challenge request)).IsTotalQueryBound
      ((if PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery request then 1 else 0) +
       (if PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery request then qBase else 0) +
       (if RoutedClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery request then qDecap else 0)) := by
  rcases request with ((coin | query) | ciphertext) | privateRequest
  all_goals simp only [actualImpl, PublicClass, RoutedClass, IsMlKemUniformQuery, IsMlKemBaseQuery,
    IsMlKemLogicalDecapsulationQuery, if_true, if_false, Nat.zero_add, Nat.add_zero]
  · change (simulateQ (kemAmbientImpl baseImpl)
      ((unifSpec + baseSpec).query (.inl coin))).IsTotalQueryBound 1
    rw [simulateQ_spec_query]
    exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  · change (simulateQ (kemAmbientImpl baseImpl)
      ((unifSpec + baseSpec).query (.inr query))).IsTotalQueryBound qBase
    rw [simulateQ_spec_query]
    exact baseBound query
  · change (simulateQ (kemAmbientImpl baseImpl)
      (if ciphertext = challenge then pure none else kem.decaps secret ciphertext)).IsTotalQueryBound qDecap
    split
    · simp only [simulateQ_pure]
      trivial
    · exact decapBound ciphertext
  · simpa only [simulateQ_bind, simulateQ_pure, bind_pure_comp, simulateQ_map, IsTotalQueryBound,
      isQueryBound_map_iff] using decapBound privateRequest.ciphertext

/-- The actual adaptive source interpreter has its own sampling ledger; no cost is transported through evaluated distribution equality. -/
theorem actual_run_uniform {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
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
    (simulateQ (kemAmbientImpl baseImpl) (simulateQ (actualImpl source kem secret challenge) client)).IsTotalQueryBound
      (qUniform + qBase * qBaseCalls + qDecap * qDecapCalls) := by
  induction client using OracleComp.inductionOn generalizing qUniform qBaseCalls qDecapCalls with
  | pure value => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at uniforms bases decaps
      simp only [simulateQ_bind, simulateQ_spec_query]
      apply (isTotalQueryBound_bind
        (actual_step_uniform source baseImpl kem secret challenge qBase qDecap baseBound decapBound request)
        (fun answer => ih answer _ _ _ (uniforms.2 answer) (bases.2 answer) (decaps.2 answer))).mono
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
theorem actual_post_uniform {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (client : OracleComp (LocalPostSpec baseSpec) Result) (u b d r : Nat)
    (bounded : PostBounds client u b d r) :
    (simulateQ (kemAmbientImpl baseImpl) (simulateQ (actualImpl source kem secret challenge) client)).IsTotalQueryBound
      (u + qBase * b + qDecap * (d + r)) := by
  apply actual_run_uniform source baseImpl kem secret challenge qBase qDecap baseBound decapBound
    client u b (d + r) bounded.uniforms bounded.bases
  apply IsQueryBoundP.of_imp _ (PqxdhProjectionCollisions.isQueryBoundP_or bounded.decaps bounded.privateRoots)
  intro request selected
  cases request with
  | inl request => exact Or.inl selected
  | inr request => exact Or.inr trivial

/-- All sampling assumptions refer to the actual programs and all possible continuations. -/
structure SamplerBounds (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat) : Prop where
  keygen : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen
  encaps : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap
  base : ∀ query, (baseImpl query).IsTotalQueryBound qBase
  decaps : ∀ secret ciphertext,
    (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap
  prepare : ∀ publicKey,
    (protocol.prepare publicKey).IsQueryBoundP IsMlKemUniformQuery uPre ∧
    (protocol.prepare publicKey).IsQueryBoundP IsMlKemBaseQuery bPre ∧
    (protocol.prepare publicKey).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dPre
  resume : ∀ publicKey ciphertext state initial,
    PostBounds (protocol.resume publicKey ciphertext state initial) uPost bPost dPost privatePost

/-- The actual source program is bounded directly and does not pay the challenger-only unused sample. -/
theorem source_uniform_bound
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (bounded : SamplerBounds baseImpl kem protocol qKeygen qEncap qBase qDecap
      uPre bPre dPre uPost bPost dPost privatePost) :
    (simulateQ (kemAmbientImpl baseImpl) (sourceMain source kem protocol)).IsTotalQueryBound
      (qKeygen + ((uPre + qBase * bPre + qDecap * dPre) +
        (qEncap + (uPost + qBase * bPost + qDecap * (dPost + privatePost))))) := by
  simp only [sourceMain, simulateQ_bind]
  apply isTotalQueryBound_bind bounded.keygen
  rintro ⟨publicKey, secretKey⟩
  apply isTotalQueryBound_bind
    (PqxdhPrivateRootGameBudgets.evalKem_uniform_bound baseImpl kem secretKey qBase qDecap bounded.base
      (bounded.decaps secretKey) _ _ _ _
      (bounded.prepare publicKey).1 (bounded.prepare publicKey).2.1 (bounded.prepare publicKey).2.2)
  intro state
  apply isTotalQueryBound_bind (bounded.encaps publicKey)
  rintro ⟨ciphertext, secret⟩
  exact actual_post_uniform source baseImpl kem secretKey ciphertext qBase qDecap bounded.base
    (bounded.decaps secretKey) _ _ _ _ _ (bounded.resume _ _ _ _)

/-- The actual-decapsulation challenger wrapper includes its unused 32-byte sample, with costs proved on that program. -/
theorem native_uniform_bound
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (bounded : SamplerBounds baseImpl kem protocol qKeygen qEncap qBase qDecap
      uPre bPre dPre uPost bPost dPost privatePost) :
    (simulateQ (kemAmbientImpl baseImpl)
      (nativeMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)).IsTotalQueryBound
      (qKeygen + ((uPre + qBase * bPre + qDecap * dPre) +
        (qEncap + (32 + (uPost + qBase * bPost + qDecap * (dPost + privatePost)))))) := by
  simp only [nativeMain, simulateQ_bind, runtimeOfImpl_liftProbComp, simulateQ_kemAmbient_liftProbComp]
  apply isTotalQueryBound_bind bounded.keygen
  rintro ⟨publicKey, secretKey⟩
  apply isTotalQueryBound_bind
    (PqxdhPrivateRootGameBudgets.evalKem_uniform_bound baseImpl kem secretKey qBase qDecap bounded.base
      (bounded.decaps secretKey) _ _ _ _
      (bounded.prepare publicKey).1 (bounded.prepare publicKey).2.1 (bounded.prepare publicKey).2.2)
  intro state
  apply isTotalQueryBound_bind (bounded.encaps publicKey)
  rintro ⟨ciphertext, secret⟩
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro unused
  exact actual_post_uniform source baseImpl kem secretKey ciphertext qBase qDecap bounded.base
    (bounded.decaps secretKey) _ _ _ _ _ (bounded.resume _ _ _ _)

/-- The ordinary fair challenger additionally pays its hidden-bit draw in its original position. -/
theorem fair_uniform_bound
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (bounded : SamplerBounds baseImpl kem protocol qKeygen qEncap qBase qDecap
      uPre bPre dPre uPost bPost dPost privatePost) :
    (PqxdhPrivateRootGameBudgets.oneKeyFairProgram baseImpl kem (reduction source kem protocol)).IsTotalQueryBound
      (qKeygen + ((uPre + qBase * bPre + qDecap * dPre) +
        (1 + (qEncap + (32 + (uPost + qBase * bPost + qDecap * (dPost + privatePost))))))) := by
  exact PqxdhPrivateRootGameBudgets.oneKeyFairProgram_uniform_bound baseImpl kem (reduction source kem protocol)
    _ _ _ _ _ _ _ _ _ _ bounded.keygen bounded.encaps bounded.base bounded.decaps
    (reduction_bounds source kem protocol _ _ _ _ _ _ _ bounded.prepare bounded.resume)

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.route_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.route_step

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.route_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.route_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.route_public_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.route_public_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.route_decapsulation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.route_decapsulation_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.reduction_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.fixed_world_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.fixed_world_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.actual_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.actual_step_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.actual_run_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.actual_run_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.actual_post_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.actual_post_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.source_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.source_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.native_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.native_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.fair_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds.fair_uniform_bound

end BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds
