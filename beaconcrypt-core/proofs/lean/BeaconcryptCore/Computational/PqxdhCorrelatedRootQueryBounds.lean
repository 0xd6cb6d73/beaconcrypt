import BeaconcryptCore.Computational.PqxdhCorrelatedRootSource
import BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds

/-!
These structural bounds count original source creation and coin requests, public CCA classes and every private root attempt through arbitrary continuations. Source and complete challenger sampling are proved on their actual programs, retaining optional native failure, completed-branch work and unused encapsulation/secret draws. The explicit random-world program equals the ordinary false-branch program before interpretation. Deterministic signing, DH, root/HKDF, parsing, byte and state work remains real computation. Native global operation counts and correlated multi-input Extract analysis remain separate.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhJointPhase1AcceptanceComposition
open PqxdhPrivateKemSource PqxdhPrivateKemQueryBounds PqxdhPrivatePhase1Prefix
open PqxdhPrivateRootSource (Parameters Prepared targetEligible borrowedPrefix continuedSource Mode blockChallenge)
open PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhDynamicIdentityRouting PqxdhPrivateRootQueryBounds
open PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
open PqxdhCorrelatedRootSource
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

abbrev Uniform := PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery
set_option backward.isDefEq.respectTransparency false in
/-- Local uniform embedding retains each real coin query. -/
theorem localCoins_uniform {Result : Type} (client : ProbComp Result) (q : Nat)
    (bound : client.IsTotalQueryBound q) :
    (localCoins (baseSpec := baseSpec) client).IsQueryBoundP (Uniform (baseSpec := baseSpec)) q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure value => simp [localCoins]
  | query_bind coin next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bound
      simp only [localCoins, simulateQ_bind, simulateQ_spec_query]
      change OracleComp.IsQueryBoundP (((LocalPostSpec baseSpec).query (.inl (.inl (.inl coin))) :
        OracleComp (LocalPostSpec baseSpec) ((LocalPostSpec baseSpec).Range (.inl (.inl (.inl coin))))) >>=
        fun answer => localCoins (next answer)) (Uniform (baseSpec := baseSpec)) q
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr bound.1, ?_⟩
      intro answer
      simpa only [Uniform, PublicClass, IsMlKemUniformQuery, ite_true] using ih answer _ (bound.2 answer)

set_option backward.isDefEq.respectTransparency false in
/-- Source interpreter coins issue no other local resource class. -/
theorem localCoins_excluded {Result : Type} (client : ProbComp Result)
    (predicate : (LocalPostSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl (.inl coin)))) :
    (localCoins (baseSpec := baseSpec) client).IsQueryBoundP predicate 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => simp [localCoins]
  | query_bind coin next ih =>
      simp only [localCoins, simulateQ_bind, simulateQ_spec_query]
      change OracleComp.IsQueryBoundP (((LocalPostSpec baseSpec).query (.inl (.inl (.inl coin))) :
        OracleComp (LocalPostSpec baseSpec) ((LocalPostSpec baseSpec).Range (.inl (.inl (.inl coin))))) >>=
        fun answer => localCoins (next answer)) predicate 0
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (excluded coin), ?_⟩
      intro answer
      simpa only [excluded coin, ite_false, localCoins] using ih answer


def SourceClass (predicate : SourceSpec.Domain → Prop) : (CorrelatedSpec baseSpec).Domain → Prop
  | .inl (.inl query) => predicate query
  | _ => False
instance (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (SourceClass (baseSpec := baseSpec) predicate) := fun query => by
  rcases query with (query | query) | query <;> dsimp [SourceClass] <;> infer_instance

/-- Exactly forwarded ordinary/private calls; public HKDF and source identity operations keep separate local ledgers. -/
def LocalClass (predicate : (LocalPostSpec baseSpec).Domain → Prop) : (CorrelatedSpec baseSpec).Domain → Prop
  | .inl (.inr (.inl query)) => predicate (.inl query)
  | .inr query => predicate (.inr query)
  | _ => False
instance (predicate : (LocalPostSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    DecidablePred (LocalClass (baseSpec := baseSpec) predicate) := fun query => by
  rcases query with (query | (query | query)) | query <;> dsimp [LocalClass] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Source creation costs32; both original coin channels keep their exact single-query cost. -/
theorem localSource_uniform_step
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (query : (CorrelatedSpec baseSpec).Domain)
    (state : BareState count) :
    ((localSourceImpl source attachedVerify primitives count query).run state).IsQueryBoundP
      (Uniform (baseSpec := baseSpec))
      ((if SourceClass (baseSpec := baseSpec) Creating query then 32 else 0) +
       (if SourceClass (baseSpec := baseSpec) SourceUniform query then 1 else 0) +
       (if LocalClass (baseSpec := baseSpec) Uniform query then 1 else 0)) := by
  rcases query with (request | (request | request)) | request
  · simpa only [localSourceImpl, StateT.run, SourceClass, LocalClass, ite_false, Nat.add_zero] using
      localCoins_uniform ((bareImpl attachedVerify primitives count request).run state) _
        (bare_uniform_step attachedVerify primitives count request state)
  · simp only [localSourceImpl, StateT.run, SourceClass, LocalClass, ite_false, Nat.zero_add,
      bind_pure_comp, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec)
      (p := Uniform) (.inl request) _).2 (by split_ifs <;> simp_all)
  · trivial
  · simp only [localSourceImpl, StateT.run, SourceClass, LocalClass, Uniform, PublicClass, ite_false,
      Nat.zero_add, bind_pure_comp, isQueryBoundP_map_iff]
    simp [PublicClass]
/-- Full adaptive post-root interpretation charges all original source creation/coin requests and every direct initializer uniform request. -/
theorem localSource_uniform_bound {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp (CorrelatedSpec baseSpec) Result)
    (qCreate qSourceCoins qCcaCoins : Nat)
    (creates : client.IsQueryBoundP (SourceClass (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : client.IsQueryBoundP (SourceClass (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (ccaCoinBound : client.IsQueryBoundP (LocalClass (baseSpec := baseSpec) (Uniform (baseSpec := baseSpec))) qCcaCoins)
    (state : BareState count) :
    ((simulateQ (localSourceImpl source attachedVerify primitives count) client).run state).IsQueryBoundP
      (Uniform (baseSpec := baseSpec)) (32 * qCreate + qSourceCoins + qCcaCoins) := by
  induction client using OracleComp.inductionOn generalizing qCreate qSourceCoins qCcaCoins state with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at creates sourceCoins ccaCoinBound
      rw [simulateQ_query_bind, StateT.run_bind]
      apply (isQueryBoundP_bind (localSource_uniform_step source attachedVerify primitives count query state)
        (fun result _ => ih result.1 _ _ _ (creates.2 result.1) (sourceCoins.2 result.1)
          (ccaCoinBound.2 result.1) result.2)).mono
      have hc := creates.1
      have hs := sourceCoins.1
      have hk := ccaCoinBound.1
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or] <;> omega


set_option backward.isDefEq.respectTransparency false in
/-- Every nonuniform forwarded class preserves original requests, including optional private roots. -/
theorem localSource_class_step
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (predicate : (LocalPostSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl (.inl coin))))
    (query : (CorrelatedSpec baseSpec).Domain) (state : BareState count) :
    ((localSourceImpl source attachedVerify primitives count query).run state).IsQueryBoundP predicate
      (if LocalClass (baseSpec := baseSpec) predicate query then 1 else 0) := by
  rcases query with (request | (request | request)) | request
  · simpa only [localSourceImpl, StateT.run, LocalClass, ite_false] using
      localCoins_excluded ((bareImpl attachedVerify primitives count request).run state) predicate excluded
  · simp only [localSourceImpl, StateT.run, LocalClass, bind_pure_comp, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec)
      (p := predicate) (.inl request) _).2 (by split_ifs <;> simp_all)
  · trivial
  · simp only [localSourceImpl, StateT.run, LocalClass, bind_pure_comp, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec)
      (p := predicate) (.inr request) _).2 (by split_ifs <;> simp_all)

theorem localSource_class_bound {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp (CorrelatedSpec baseSpec) Result)
    (predicate : (LocalPostSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl (.inl coin)))) (q : Nat)
    (bounded : client.IsQueryBoundP (LocalClass (baseSpec := baseSpec) predicate) q) (state : BareState count) :
    ((simulateQ (localSourceImpl source attachedVerify primitives count) client).run state).IsQueryBoundP predicate q :=
  bounded.simulateQ_run_StateT_of_step
    (localSource_class_step source attachedVerify primitives count predicate excluded) state

set_option backward.isDefEq.respectTransparency false in
/-- The real source handler counts every private request before challenge-dependent public suppression. -/
theorem sourcePost_step
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (request : (LocalPostSpec baseSpec).Domain) :
    (sourcePost source challenge request).IsQueryBoundP predicate
      (if RoutedClass predicate request then 1 else 0) := by
  cases request with
  | inl request =>
      cases challenge with
      | none =>
          simp only [sourcePost, RoutedClass]
          exact (isQueryBoundP_query_iff (spec := MlKemCCAOracleSpec baseSpec) (p := predicate) request _).2 (by split_ifs <;> simp_all)
      | some challenge =>
          simpa only [sourcePost, RoutedClass, simulateQ_spec_query] using
            blockChallenge_bound challenge (((MlKemCCAOracleSpec baseSpec).query request) :
              OracleComp (MlKemCCAOracleSpec baseSpec) _) predicate
              (if predicate request then 1 else 0)
              ((isQueryBoundP_query_iff (spec := MlKemCCAOracleSpec baseSpec) (p := predicate) request _).2 (by split_ifs <;> simp_all))
  | inr request =>
      change OracleComp.IsQueryBoundP (((MlKemCCAOracleSpec baseSpec).query (.inr request.ciphertext) :
        OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret)) >>=
        fun (recovered : Option MlKemSharedSecret) => pure
          (recovered.map (PqxdhHiddenRoot.productionHiddenRoot source request.coordinates)))
        predicate (if predicate (.inr request.ciphertext) then 1 else 0)
      simp only [isQueryBoundP_query_bind_iff, isQueryBoundP_pure]
      split <;> simp_all

theorem sourcePost_bound {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (client : OracleComp (LocalPostSpec baseSpec) Result) (q : Nat)
    (bounded : client.IsQueryBoundP (RoutedClass predicate) q) :
    (simulateQ (sourcePost source challenge) client).IsQueryBoundP predicate q :=
  isQueryBoundP_simulateQ_of_step_noUniform bounded
    (fun request hit => by simpa only [hit, ite_true] using sourcePost_step source challenge predicate request)
    (fun request miss => by simpa only [miss, ite_false] using sourcePost_step source challenge predicate request)

/-- Independent caps retain the original source and direct channels and every private root attempt. -/
structure ObserverBounds {Result : Type} (client : OracleComp (CorrelatedSpec baseSpec) Result)
    (creates sourceCoins uniforms bases decaps roots : Nat) : Prop where
  createBound : client.IsQueryBoundP (SourceClass (baseSpec := baseSpec) Creating) creates
  sourceCoinBound : client.IsQueryBoundP (SourceClass (baseSpec := baseSpec) SourceUniform) sourceCoins
  uniformBound : client.IsQueryBoundP (LocalClass (baseSpec := baseSpec) Uniform) uniforms
  baseBound : client.IsQueryBoundP (LocalClass (baseSpec := baseSpec)
    (PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery)) bases
  decapBound : client.IsQueryBoundP (LocalClass (baseSpec := baseSpec)
    (PublicClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery)) decaps
  rootBound : client.IsQueryBoundP (LocalClass (baseSpec := baseSpec) (IsPrivateRoot (baseSpec := baseSpec))) roots

/-- Complete stateful source interpretation exposes no uncharged primitive requests. -/
theorem localObserve_bounds
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    {Selection : Type} (observer : CorrelatedObserver setup Selection)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) (state : BareState count)
    (creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : ObserverBounds (observer.main output execution) creates sourceCoins uniforms bases decaps roots) :
    PostBounds (localObserve source attachedVerify primitives count setup observer output execution state)
      (32 * creates + sourceCoins + uniforms) bases decaps roots := by
  constructor
  · simpa only [localObserve, isQueryBoundP_map_iff] using
      localSource_uniform_bound source attachedVerify primitives count (observer.main output execution)
        creates sourceCoins uniforms bounded.createBound bounded.sourceCoinBound bounded.uniformBound state
  · simpa only [localObserve, isQueryBoundP_map_iff] using
      localSource_class_bound source attachedVerify primitives count (observer.main output execution) _
        (fun _ => by simp [PublicClass, IsMlKemBaseQuery]) bases bounded.baseBound state
  · simpa only [localObserve, isQueryBoundP_map_iff] using
      localSource_class_bound source attachedVerify primitives count (observer.main output execution) _
        (fun _ => by simp [PublicClass, IsMlKemLogicalDecapsulationQuery]) decaps bounded.decapBound state
  · simpa only [localObserve, isQueryBoundP_map_iff] using
      localSource_class_bound source attachedVerify primitives count (observer.main output execution) _
        (fun _ => by simp [IsPrivateRoot]) roots bounded.rootBound state
/-- Uniform and base classes inherit their original caps because private root processing adds neither kind of ordinary request. -/
theorem sourcePost_public_bound {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (challenge : Option MlKem768Ciphertext)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (notDecapsulation : ∀ ciphertext, ¬ predicate (.inr ciphertext))
    (client : OracleComp (LocalPostSpec baseSpec) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (PublicClass predicate) bound) :
    (simulateQ (sourcePost source challenge) client).IsQueryBoundP predicate bound := by
  apply sourcePost_bound source challenge predicate client bound
  apply IsQueryBoundP.of_imp (p' := PublicClass predicate) _ bounded
  intro request selected
  cases request with
  | inl request => exact selected
  | inr request => exact (notDecapsulation request.ciphertext selected).elim

/-- Both original public decapsulation requests and private attempts are charged before any challenge branch is taken. -/
theorem sourcePost_decapsulation_bound {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (challenge : Option MlKem768Ciphertext)
    (client : OracleComp (LocalPostSpec baseSpec) Result) (publicBound privateBound : Nat)
    (publics : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) publicBound)
    (privates : client.IsQueryBoundP (IsPrivateRoot (baseSpec := baseSpec)) privateBound) :
    (simulateQ (sourcePost source challenge) client).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery (publicBound + privateBound) := by
  apply sourcePost_bound source challenge IsMlKemLogicalDecapsulationQuery client _
  have combined := PqxdhProjectionCollisions.isQueryBoundP_or publics privates
  apply IsQueryBoundP.of_imp _ combined
  intro request selected
  cases request with
  | inl request => exact Or.inl selected
  | inr request => exact Or.inr trivial


/-- Original observer classes bound the actual complete source continuation, including every private decapsulation attempt. -/
theorem observe_bounds
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    {Selection : Type} (observer : CorrelatedObserver setup Selection)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) (state : BareState count)
    (creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : ObserverBounds (observer.main output execution) creates sourceCoins uniforms bases decaps roots) :
    let client := observe source challenge attachedVerify primitives count setup observer output execution state
    client.IsQueryBoundP IsMlKemUniformQuery (32 * creates + sourceCoins + uniforms) ∧
    client.IsQueryBoundP IsMlKemBaseQuery bases ∧
    client.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (decaps + roots) := by
  have localBound := localObserve_bounds source attachedVerify primitives count setup observer output execution state
    creates sourceCoins uniforms bases decaps roots bounded
  exact ⟨sourcePost_public_bound source challenge _ (fun _ => by simp [IsMlKemUniformQuery]) _ _ localBound.uniforms,
    sourcePost_public_bound source challenge _ (fun _ => by simp [IsMlKemBaseQuery]) _ _ localBound.bases,
    sourcePost_decapsulation_bound source challenge _ _ _ localBound.decaps localBound.privateRoots⟩
/-- Real accepted non-target candidates pay actual native optional encapsulation, with every rejection and observer effect retained. -/
theorem acceptedCommon_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : CorrelatedObserver setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (state : BareState 1) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    (acceptedCommon parameters.source kem parameters.native attachedVerify primitives 1 setup observer output state
      parameters.server parameters.application parameters.ephemeralGen identity keys).IsQueryBoundP predicate
      (qEphemeral + (qNative + qObserver)) := by
  unfold acceptedCommon
  split
  · exact (observerBound _ _ _ _).mono (by omega)
  · apply isQueryBoundP_bind (by simpa only [ccaAmbient_eq_lift] using ephemeralBound)
    intro ephemeral _
    apply isQueryBoundP_bind (by simpa only [ccaAmbient_eq_lift] using nativeBound keys.pqKey)
    intro encapsulated _
    cases encapsulated <;> exact observerBound _ _ _ _

/-- All original acceptance/rejection branches share the same charged optional source bound. -/
theorem allCandidateCommon_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : CorrelatedObserver setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (state : BareState 1) :
    (allCandidateCommon parameters.source kem parameters.native attachedVerify primitives 1 setup observer output state
      parameters.server parameters.application parameters.ephemeralGen).IsQueryBoundP predicate
      (qEphemeral + (qNative + qObserver)) := by
  unfold allCandidateCommon
  cases output.bind (·.accepted) with
  | none => exact (observerBound _ _ _ _).mono (by omega)
  | some selected =>
      exact acceptedCommon_bound kem parameters attachedVerify primitives setup observer predicate
        qEphemeral qNative qObserver ephemeralBound nativeBound observerBound output state selected.1 selected.2

/-- The real abort encapsulation and every completed common branch precede challenger completion and remain charged. -/
theorem dispatch_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : CorrelatedObserver setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qTotal qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (totalBound : ∀ target, (ccaAmbient (kem.encaps target)).IsQueryBoundP predicate qTotal)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (prepared : Prepared setup Selection) :
    (dispatch kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP predicate
      (qEphemeral + (max qNative qTotal + qObserver)) := by
  unfold dispatch
  split
  · simp
  · split
    · apply isQueryBoundP_bind ephemeralBound
      intro ephemeral _
      split
      · simp
      · apply isQueryBoundP_bind ((totalBound _).mono (Nat.le_max_right _ _))
        intro encapsulated _
        simpa only [bind_pure_comp, isQueryBoundP_map_iff] using observerBound _ _ _ _
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        (allCandidateCommon_bound kem parameters attachedVerify primitives setup observer predicate
          qEphemeral qNative qObserver ephemeralBound nativeBound observerBound _ _).mono
          (by omega)

/-- Every prechallenge class is the complete generated prefix plus the full source dispatch; ghost challenger encapsulation is separately charged later. -/
theorem rootProtocol_prefix_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (observer : CorrelatedObserver setup selector.State)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qPrefix qEphemeral qNative qTotal qObserver : Nat)
    (prefixBound : ∀ target, (borrowedPrefix attachedVerify primitives setup selector target).IsQueryBoundP predicate qPrefix)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (totalBound : ∀ target, (ccaAmbient (kem.encaps target)).IsQueryBoundP predicate qTotal)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (target : PqxdhStatefulPhase1EufCma.TargetKemPublicKey) :
    ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP predicate
      (qPrefix + (qEphemeral + (max qNative qTotal + qObserver))) :=
  isQueryBoundP_bind (prefixBound target) (fun prepared _ => dispatch_bound kem parameters attachedVerify primitives
    setup observer predicate qEphemeral qNative qTotal qObserver ephemeralBound nativeBound totalBound observerBound prepared)

/-- The actual target encapsulation continuation retains all observer work and counts its logical blocked requests before suppression. -/
theorem targetAfterEncapsulation_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : CorrelatedObserver setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qObserver : Nat)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    (targetAfterEncapsulation kem parameters attachedVerify primitives setup observer prepared ephemeral encapsulated).IsQueryBoundP
      predicate qObserver := by
  unfold targetAfterEncapsulation
  cases encapsulated with
  | none => exact observerBound _ _ _ _
  | some pair =>
      rcases pair with ⟨ciphertext, secret⟩
      dsimp only
      split
      · exact observerBound _ _ _ _
      · exact observerBound _ _ _ _

/-- The actual native game pays one source ephemeral and optional encapsulation on every eligible accepted branch, without assuming success. -/
theorem nativeNext_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : CorrelatedObserver setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (prepared : Prepared setup Selection) :
    (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP predicate
      (qEphemeral + (qNative + qObserver)) := by
  unfold nativeNext
  split
  · unfold nativeTargetContinuation
    apply isQueryBoundP_bind ephemeralBound
    intro ephemeral _
    apply isQueryBoundP_bind (nativeBound _)
    intro encapsulated _
    exact targetAfterEncapsulation_bound kem parameters attachedVerify primitives setup observer predicate qObserver
      observerBound prepared ephemeral encapsulated
  · exact allCandidateCommon_bound kem parameters attachedVerify primitives setup observer predicate
      qEphemeral qNative qObserver ephemeralBound nativeBound observerBound _ _


/-- The pending protocol inherits complete original observer bounds; completed and absent-root branches add no queries. -/
theorem rootProtocol_resume_bounds
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : CorrelatedObserver setup selector.State)
    (creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : ∀ output execution, ObserverBounds (observer.main output execution)
      creates sourceCoins uniforms bases decaps roots)
    (target : PqxdhStatefulPhase1EufCma.TargetKemPublicKey) (ciphertext : MlKem768Ciphertext)
    (mode : Mode setup selector.State) (initial : Option PqxdhSecretInputKdf.RootOutput) :
    PostBounds ((rootProtocol kem parameters attachedVerify primitives setup selector observer).resume
      target ciphertext mode initial) (32 * creates + sourceCoins + uniforms) bases decaps roots := by
  cases mode with
  | completed decision => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
  | pending prepared ephemeral =>
      cases initial with
      | none => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
      | some root =>
          exact localObserve_bounds parameters.source attachedVerify primitives 1 setup observer _ _ prepared.2
            creates sourceCoins uniforms bases decaps roots (bounded _ _)

/-- Exact ordinary CCA caps apply to the concrete prefix and private continuation, with private attempts added only to decapsulation. -/
theorem rootProtocol_reduction_bounds
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : CorrelatedObserver setup selector.State)
    (uPre bPre dPre creates sourceCoins uniforms bases decaps roots : Nat)
    (prepareBound : ∀ target,
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemUniformQuery uPre ∧
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemBaseQuery bPre ∧
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemLogicalDecapsulationQuery dPre)
    (bounded : ∀ output execution, ObserverBounds (observer.main output execution)
      creates sourceCoins uniforms bases decaps roots) :
    (reduction parameters.source kem (rootProtocol kem parameters attachedVerify primitives setup selector observer)).MakesAtMostQueries
      uPre bPre dPre (32 * creates + sourceCoins + uniforms) bases (decaps + roots) :=
  reduction_bounds parameters.source kem _ _ _ _ _ _ _ _ prepareBound
    (rootProtocol_resume_bounds kem parameters attachedVerify primitives setup selector observer
      creates sourceCoins uniforms bases decaps roots bounded)

/-- Source sampling is proved on the original program, without erasing or adding any challenger draw. -/
theorem actualGame_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : CorrelatedObserver setup selector.State)
    (qPrefix qBase qDecap qUniform qBaseCalls qDecapCalls : Nat)
    (prefixBound : (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (program baseImpl kem setup selector)).IsTotalQueryBound qPrefix)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (uniforms : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemUniformQuery qUniform)
    (bases : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemBaseQuery qBaseCalls)
    (decaps : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qDecapCalls) :
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).IsTotalQueryBound
      (qPrefix + (qUniform + qBase * qBaseCalls + qDecap * qDecapCalls)) := by
  apply PqxdhPrivateRootGameBudgets.continuedSource_uniform_bound attachedVerify primitives baseImpl kem setup selector _ false _ _ prefixBound
  intro secret prepared
  exact PqxdhPrivateRootGameBudgets.evalKem_uniform_bound baseImpl kem secret qBase qDecap baseBound (decapBound secret) _ _ _ _
    (uniforms prepared) (bases prepared) (decaps prepared)


/-- Actual source generation costs are expanded separately from the proof-only borrowed challenger prefix. -/
theorem actualGame_uniform_from_calls
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : CorrelatedObserver setup selector.State)
    (qPrekey qKeygen qOneTime qBase qDecap qCreate qSourceCoins qCcaCoins qBaseCalls qDecapCalls
      uNext bNext dNext : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (oneTimeBound : ∀ identity before target,
      (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOneTime)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (creates : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (ccaCoinsBound : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery) qCcaCoins)
    (bases : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemBaseQuery) qBaseCalls)
    (decaps : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) qDecapCalls)
    (uniformsNext : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemUniformQuery uNext)
    (basesNext : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemBaseQuery bNext)
    (decapsNext : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery dNext) :
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).IsTotalQueryBound
      ((32 + ((qPrekey + (qKeygen + qOneTime)) +
        (32 * qCreate + qSourceCoins + qCcaCoins + qBase * qBaseCalls + qDecap * qDecapCalls))) +
        (uNext + qBase * bNext + qDecap * dNext)) :=
  actualGame_uniform_bound baseImpl kem parameters attachedVerify primitives setup selector observer
    _ _ _ _ _ _
    (PqxdhPrivateRootGameBudgets.program_uniform_from_calls attachedVerify primitives 1 baseImpl kem setup selector
      qPrekey qKeygen qOneTime qBase qDecap qCreate qSourceCoins qCcaCoins qBaseCalls qDecapCalls
      prekeyBound keygenBound oneTimeBound baseBound decapBound creates sourceCoins ccaCoinsBound bases decaps)
    baseBound decapBound uniformsNext basesNext decapsNext

/-- All complete-challenger hypotheses are derived from the concrete prefix and original private observer bounds. -/
theorem rootProtocol_sampler_bounds
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : CorrelatedObserver setup selector.State)
    (qKeygen qEncap qBase qDecap uPre bPre dPre creates sourceCoins uniforms bases decaps roots : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (prepareBound : ∀ target,
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemUniformQuery uPre ∧
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemBaseQuery bPre ∧
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemLogicalDecapsulationQuery dPre)
    (bounded : ∀ output execution, ObserverBounds (observer.main output execution)
      creates sourceCoins uniforms bases decaps roots) :
    SamplerBounds baseImpl kem (rootProtocol kem parameters attachedVerify primitives setup selector observer)
      qKeygen qEncap qBase qDecap uPre bPre dPre (32 * creates + sourceCoins + uniforms) bases decaps roots :=
  ⟨keygenBound, encapBound, baseBound, decapBound, prepareBound,
    rootProtocol_resume_bounds kem parameters attachedVerify primitives setup selector observer
      creates sourceCoins uniforms bases decaps roots bounded⟩

/-- This equality holds before any interpretation, so query costs and all ambient effects transfer exactly. -/
theorem randomMain_eq_branchMain
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec))) (protocol : Protocol baseSpec) :
    randomMain source kem runtime protocol = oneKeyBranchMain kem runtime (reduction source kem protocol) false := by
  simp only [randomMain, oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, reduction,
    Bool.false_eq_true, ite_false, publicImpl, pure_bind, bind_assoc]
  rfl

/-- Source-shaped completion, explicit correlated randomness, native ghost completion and fair CCA each pay their actual draws. -/
theorem correlated_world_ledger
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : CorrelatedObserver setup selector.State)
    (qKeygen qEncap qBase qDecap uPre bPre dPre creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : SamplerBounds baseImpl kem (rootProtocol kem parameters attachedVerify primitives setup selector observer)
      qKeygen qEncap qBase qDecap uPre bPre dPre (32 * creates + sourceCoins + uniforms) bases decaps roots) :
    let protocol := rootProtocol kem parameters attachedVerify primitives setup selector observer
    let before := qKeygen + (uPre + qBase * bPre + qDecap * dPre) + qEncap
    let after := (32 * creates + sourceCoins + uniforms) + qBase * bases + qDecap * (decaps + roots)
    (simulateQ (kemAmbientImpl baseImpl) (sourceMain parameters.source kem protocol)).IsTotalQueryBound
      (before + after) ∧
    (simulateQ (kemAmbientImpl baseImpl)
      (randomMain parameters.source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)).IsTotalQueryBound
      (before + 32 + after) ∧
    (simulateQ (kemAmbientImpl baseImpl)
      (nativeMain parameters.source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)).IsTotalQueryBound
      (before + 32 + after) ∧
    (PqxdhPrivateRootGameBudgets.oneKeyFairProgram baseImpl kem
      (reduction parameters.source kem protocol)).IsTotalQueryBound (before + 33 + after) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using source_uniform_bound parameters.source baseImpl kem _
      _ _ _ _ _ _ _ _ _ _ _ bounded
  · rw [randomMain_eq_branchMain]
    simpa only [Nat.add_assoc] using fixed_world_uniform_bound parameters.source baseImpl kem _
      _ _ _ _ _ _ _ _ _ _ _ bounded.keygen bounded.encaps bounded.base bounded.decaps bounded.prepare bounded.resume false
  · simpa only [Nat.add_assoc] using native_uniform_bound parameters.source baseImpl kem _
      _ _ _ _ _ _ _ _ _ _ _ bounded
  · exact (fair_uniform_bound parameters.source baseImpl kem _
      _ _ _ _ _ _ _ _ _ _ _ bounded).mono (by omega)

/-- Ambient generators make no logical CCA decapsulation requests; their internal primitive work retains its own caps. -/
theorem ccaAmbient_no_decap {Result : Type} (client : OracleComp (unifSpec + baseSpec) Result) :
    (ccaAmbient client).IsQueryBoundP IsMlKemLogicalDecapsulationQuery 0 := by
  apply ccaAmbient_bound
  exact IsQueryBoundP.of_imp (p' := fun _ => False) (fun _ hit => hit) (isQueryBoundP_false client 0)

/-- Concrete optional source calls and original observer budgets discharge all native continuation class premises. -/
theorem nativeNext_observer_bounds
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : CorrelatedObserver setup Selection)
    (uEphemeral uNative bEphemeral bNative creates sourceCoins uniforms bases decaps roots : Nat)
    (ephemeralUniform : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP IsMlKemUniformQuery uEphemeral)
    (nativeUniform : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP IsMlKemUniformQuery uNative)
    (ephemeralBase : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP IsMlKemBaseQuery bEphemeral)
    (nativeBase : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP IsMlKemBaseQuery bNative)
    (bounded : ∀ output execution, ObserverBounds (observer.main output execution)
      creates sourceCoins uniforms bases decaps roots)
    (prepared : Prepared setup Selection) :
    let client := nativeNext kem parameters attachedVerify primitives setup observer prepared
    client.IsQueryBoundP IsMlKemUniformQuery (uEphemeral + (uNative + (32 * creates + sourceCoins + uniforms))) ∧
    client.IsQueryBoundP IsMlKemBaseQuery (bEphemeral + (bNative + bases)) ∧
    client.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (decaps + roots) := by
  refine ⟨?_, ?_, ?_⟩
  · exact nativeNext_bound kem parameters attachedVerify primitives setup observer IsMlKemUniformQuery
      _ _ _ ephemeralUniform nativeUniform
      (fun challenge output execution state => (observe_bounds parameters.source challenge attachedVerify primitives 1
        setup observer output execution state creates sourceCoins uniforms bases decaps roots (bounded _ _)).1) prepared
  · exact nativeNext_bound kem parameters attachedVerify primitives setup observer IsMlKemBaseQuery
      _ _ _ ephemeralBase nativeBase
      (fun challenge output execution state => (observe_bounds parameters.source challenge attachedVerify primitives 1
        setup observer output execution state creates sourceCoins uniforms bases decaps roots (bounded _ _)).2.1) prepared
  · simpa only [Nat.zero_add] using nativeNext_bound kem parameters attachedVerify primitives setup observer
      IsMlKemLogicalDecapsulationQuery 0 0 (decaps + roots) (ccaAmbient_no_decap parameters.ephemeralGen)
      (fun target => ccaAmbient_no_decap (parameters.native.encaps target))
      (fun challenge output execution state => (observe_bounds parameters.source challenge attachedVerify primitives 1
        setup observer output execution state creates sourceCoins uniforms bases decaps roots (bounded _ _)).2.2) prepared

end BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localCoins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localCoins_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localCoins_excluded' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localCoins_excluded

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localSource_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localSource_uniform_step

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localSource_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localSource_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localSource_class_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localSource_class_step

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localSource_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localSource_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.sourcePost_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.sourcePost_step

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.sourcePost_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.sourcePost_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localObserve_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.localObserve_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.sourcePost_public_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.sourcePost_public_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.sourcePost_decapsulation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.sourcePost_decapsulation_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.observe_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.observe_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.acceptedCommon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.acceptedCommon_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.allCandidateCommon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.allCandidateCommon_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.dispatch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.dispatch_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.rootProtocol_prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.rootProtocol_prefix_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.targetAfterEncapsulation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.targetAfterEncapsulation_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.nativeNext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.nativeNext_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.rootProtocol_resume_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.rootProtocol_resume_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.rootProtocol_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.rootProtocol_reduction_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.actualGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.actualGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.actualGame_uniform_from_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.actualGame_uniform_from_calls

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.rootProtocol_sampler_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.rootProtocol_sampler_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.randomMain_eq_branchMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.randomMain_eq_branchMain

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.correlated_world_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.correlated_world_ledger

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.ccaAmbient_no_decap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.ccaAmbient_no_decap

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.nativeNext_observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds.nativeNext_observer_bounds
