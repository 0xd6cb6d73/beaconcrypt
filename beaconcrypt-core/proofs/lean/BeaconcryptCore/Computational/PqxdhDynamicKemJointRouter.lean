import BeaconcryptCore.Computational.PqxdhDynamicKemJointSource
import BeaconcryptCore.Computational.PqxdhDynamicKemBounds

/-!
The actual combined joint-identity, local-coin and dynamically created KEM interface is interpreted by the selected CCA router. Every source identity operation keeps its native correlated seed and log state. The executable wrapper requires no selected-secret argument; arbitrary input histories and equal other-index secret bytes are not excluded by these operational statements. Source comparison supplies the selected secret to the mathematical CCA interpreter and source reconstruction.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter
open PqxdhKemIndCca PqxdhPrivateKemSource
open PqxdhDynamicKemRouter (Reservation redact)
open PqxdhDynamicKemJointSource (State)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

/-- One concrete joint service wrapper preserves every actual identity operation and random query; the private KEM callback alone changes across the CCA comparison. -/
def combine {m : Type → Type*} [Monad m]
    (coins : {X : Type} → ProbComp X → m X) (primitives : PqxdhJointIdentity.Primitives)
    (pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
      (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) m))) :
    QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OptionT (StateT (State KemSK) m)) := fun query =>
  OptionT.mk fun state => match query with
  | .inl query => (fun result => (some result.1, (result.2, state.2))) <$>
      coins ((PqxdhDynamicIdentityPool.lazyImpl primitives query).run state.1)
  | .inr (.inl query) => (fun result => (some result, state)) <$> coins (unifSpec.query query)
  | .inr (.inr query) => (fun result => (result.1, (state.1, result.2))) <$> ((pool query).run).run state.2

def pre (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK) :=
  combine ccaCoins primitives (PqxdhDynamicKemRouter.pre kem selected reservation)

noncomputable def post (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :=
  combine ccaCoins primitives (PqxdhDynamicKemRouter.post kem selected reservation challenge candidate)

def stopped (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) :=
  combine (fun work => work) primitives (PqxdhDynamicKemRouter.source baseImpl kem selected pairs)

set_option backward.isDefEq.respectTransparency false in
/-- The executable prechallenge wrapper requires no selected-secret argument and equals the exact stopped source after interpreting ordinary selected-key decapsulation. Complete joint state and all private histories remain in the result; this statement does not exclude arbitrary prior histories or equal other-index secret bytes. -/
theorem pre_step (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK) (present : pairs[selected]? = some (target, secret))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK) :
    evalKem baseImpl kem secret (((pre primitives kem selected (redact selected pairs) query).run).run state) =
      (((stopped baseImpl primitives kem selected pairs query).run).run state) := by
  rcases query with joint | (coin | query)
  · simp only [pre, stopped, combine, OptionT.run_mk, StateT.run, evalKem, simulateQ_map]
    exact congrArg (fun work => (fun result => (some result.1, (result.2, state.2))) <$> work)
      (evalKem_coins baseImpl kem secret ((PqxdhDynamicIdentityPool.lazyImpl primitives joint).run state.1))
  · simp only [pre, stopped, combine, OptionT.run_mk, StateT.run, evalKem, simulateQ_map]
    rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl kem secret)
        (ccaCoins (unifSpec.query coin : ProbComp _))) = (unifSpec.query coin : ProbComp _) from evalKem_coins baseImpl kem secret _]
  · simp only [pre, stopped, combine, OptionT.run_mk, StateT.run, evalKem, simulateQ_map]
    exact congrArg (fun work => (fun result => (result.1, (state.1, result.2))) <$> work)
      (PqxdhDynamicKemRouter.step_source baseImpl kem selected pairs target secret present query state.2)

set_option backward.isDefEq.respectTransparency false in
/-- The full adaptive prechallenge schedule preserves every joint or KEM reply, both complete histories and source state, including ordinary missing-handle rejection and the explicit selected reveal stop. -/
theorem pre_program (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK) (present : pairs[selected]? = some (target, secret))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK) :
    evalKem baseImpl kem secret (((simulateQ (pre primitives kem selected (redact selected pairs)) client).run).run state) =
      (((simulateQ (stopped baseImpl primitives kem selected pairs) client).run).run state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    change evalKem baseImpl kem secret
      ((((pre primitives kem selected (redact selected pairs) query).run).run state) >>= fun result =>
        (result.1.elim (pure none) (fun value =>
          (simulateQ (pre primitives kem selected (redact selected pairs)) (next value)).run)).run result.2) = _
    unfold evalKem
    simp only [simulateQ_bind]
    rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl kem secret)
        (((pre primitives kem selected (redact selected pairs) query).run).run state)) =
          (((stopped baseImpl primitives kem selected pairs query).run).run state)
      from pre_step baseImpl primitives kem selected pairs target secret present query state]
    apply bind_congr
    rintro ⟨none | reply, after⟩
    · rfl
    · exact ih reply after

set_option backward.isDefEq.respectTransparency false in
/-- The blocked postchallenge interpreter retains every ordinary uniform query used by joint identity work or explicit source randomness. -/
theorem post_coins (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (client : ProbComp Result) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge (ccaCoins client) = client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [ccaCoins, simulateQ_bind, simulateQ_spec_query, PqxdhDynamicKemPost.evaluate]
    have coin : simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (kem.IND_CCA_postChallengeImpl secret challenge (.inl (.inl query))) =
          (unifSpec.query query : ProbComp _) := by
      unfold KEMScheme.IND_CCA_postChallengeImpl QueryImpl.add
      simp only [QueryImpl.liftTarget_self, QueryImpl.id'_apply, simulateQ_spec_query] <;> rfl
    rw [coin]
    change ((unifSpec.query query : ProbComp _) >>= fun reply =>
      PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge (ccaCoins (next reply))) = _
    simp only [ih]

set_option backward.isDefEq.respectTransparency false in
/-- The complete postchallenge joint callback preserves the actual real-candidate source reply while the ordinary CCA interpreter blocks its challenge ciphertext. No selected secret is passed to the executable wrapper. -/
theorem post_step (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK) (present : pairs[selected]? = some (target, secret))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some candidate))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
      (((post primitives kem selected (redact selected pairs) challenge candidate query).run).run state) =
        (((stopped baseImpl primitives kem selected pairs query).run).run state) := by
  rcases query with joint | (coin | query)
  · simp only [post, stopped, combine, OptionT.run_mk, StateT.run, PqxdhDynamicKemPost.evaluate, simulateQ_map]
    exact congrArg (fun work => (fun result => (some result.1, (result.2, state.2))) <$> work)
      (post_coins baseImpl kem secret challenge ((PqxdhDynamicIdentityPool.lazyImpl primitives joint).run state.1))
  · simp only [post, stopped, combine, OptionT.run_mk, StateT.run, PqxdhDynamicKemPost.evaluate, simulateQ_map]
    exact congrArg (fun work => (fun result => (some result, state)) <$> work)
      (post_coins baseImpl kem secret challenge (unifSpec.query coin : ProbComp _))
  · simp only [post, stopped, combine, OptionT.run_mk, StateT.run, PqxdhDynamicKemPost.evaluate, simulateQ_map]
    exact congrArg (fun work => (fun result => (result.1, (state.1, result.2))) <$> work)
      ((PqxdhDynamicKemPost.step_pre baseImpl kem secret selected challenge candidate agreement
        (redact selected pairs) query state.2).trans
        (PqxdhDynamicKemRouter.step_source baseImpl kem selected pairs target secret present query state.2))

set_option backward.isDefEq.respectTransparency false in
/-- Every adaptive postchallenge continuation retains the same complete stopped source result and joint/private state. Exact challenge-ciphertext requests return the supplied candidate to the source client and never query the blocked CCA ciphertext; candidate nonexposure at the public protocol boundary is a separate obligation. -/
theorem post_program (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK) (present : pairs[selected]? = some (target, secret))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some candidate))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
      (((simulateQ (post primitives kem selected (redact selected pairs) challenge candidate) client).run).run state) =
        (((simulateQ (stopped baseImpl primitives kem selected pairs) client).run).run state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    change PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
      ((((post primitives kem selected (redact selected pairs) challenge candidate query).run).run state) >>= fun result =>
        (result.1.elim (pure none) (fun value =>
          (simulateQ (post primitives kem selected (redact selected pairs) challenge candidate) (next value)).run)).run result.2) = _
    unfold PqxdhDynamicKemPost.evaluate
    simp only [simulateQ_bind]
    rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (simulateQ (kem.IND_CCA_postChallengeImpl secret challenge)
        (((post primitives kem selected (redact selected pairs) challenge candidate query).run).run state)) =
          (((stopped baseImpl primitives kem selected pairs query).run).run state)
      from post_step baseImpl primitives kem selected pairs target secret present challenge candidate agreement query state]
    apply bind_congr
    rintro ⟨none | reply, after⟩
    · rfl
    · exact ih reply after

/-- The actual generated key and encapsulation support, ordinary recipient correctness and existing functional decapsulation contract discharge the real-candidate premise for the entire joint postchallenge program. -/
theorem supported_post (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK) (present : pairs[selected]? = some (target, secret))
    (generated : (target, secret) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (encapsulated : (challenge, candidate) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps target)))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
      (((simulateQ (post primitives kem selected (redact selected pairs) challenge candidate) client).run).run state) =
        (((simulateQ (stopped baseImpl primitives kem selected pairs) client).run).run state) :=
  post_program baseImpl primitives kem selected pairs target secret present challenge candidate
    (PqxdhChallengeSecretRouting.honest_decapsulation_program baseImpl kem functional correct generated encapsulated) client state

end BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.pre_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.pre_step
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.pre_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.pre_program
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.post_coins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.post_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.post_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.post_step
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.post_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.post_program
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.supported_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter.supported_post
