import BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource
import BeaconcryptCore.Computational.PqxdhInitialRootEventBounds

/-!
The fixed first record of one selected owner is compared with its first-record key-last endpoint and split exactly into two parts. The completed part is the actual experiment whose accepted continuation is replaced by the constant `false`; the pending part is the same actual execution in which every non-accepted leaf returns `false` and the accepted leaf runs the complete source-event continuation. The ideal endpoint splits in the same way into the completed decisions of the actual preparation and its pending source observer.

The completed parts differ by the authenticated-root bound for the constant-`false` continuation, whose single root query is derived from the original source certificate. Together with the first-record target bound this leaves an explicit bound on the pending mass of the actual experiment: its pending-observer ideal plus the first-record target loss plus that completed-branch root loss. Every term is the advantage of a constructed reduction or an explicit statistical charge; no raw-record forgery bound is claimed here.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstRecordTarget
open PqxdhAdaptiveTargetPost PqxdhAdaptiveAcceptedResult PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhChallengeSecretRouting
open PqxdhPrivateRootSource PqxdhPrivateAcceptedRoot PqxdhInitializerSecrecy PqxdhSourceAuthenticatedRoot
open PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhHiddenRoot PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- A Boolean game split pointwise after a common first stage is split with the same masses. -/
theorem true_bind_split {α : Type} (mx : ProbComp α) (f g h : α → ProbComp Bool)
    (split : ∀ a, 𝒟[f a] {true} = 𝒟[g a] {true} + 𝒟[h a] {true}) :
    𝒟[mx >>= f] {true} = 𝒟[mx >>= g] {true} + 𝒟[mx >>= h] {true} := by
  have pointwise : ∀ a, Pr{let x ← f a}[x = true] = Pr{let x ← g a}[x = true] + Pr{let x ← h a}[x = true] :=
    fun a => by
      rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
      exact split a
  rw [← prEvent_eq_evalDist_singleton (mx >>= f), ← prEvent_eq_evalDist_singleton (mx >>= g),
    ← prEvent_eq_evalDist_singleton (mx >>= h)]
  simp only [OracleComp.prEvent_bind_eq_tsum, pointwise, mul_add, ENNReal.tsum_add]

section Actual
variable (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready →
  OracleComp (LocalPostSpec baseSpec) Bool)

/-- The accepted leaf of the actual target path; every rejected or common leaf returns `false`. -/
noncomputable def pendingAfterEncapsulation (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) : ProbComp Bool :=
  match encapsulated with
  | none => pure false
  | some (ciphertext, shared) =>
      match rootFailure env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
        prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey with
      | some _ => pure false
      | none => PqxdhInitialRootEventExperiment.nativeAccepted env baseImpl kem attachedVerify primitives program post accepted secret prepared
          (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
            ephemeral ciphertext (productionHiddenRoot env.source
              (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
                prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey) shared))

/-- The actual continuation with the same eligibility test and private generators, keeping only its accepted leaf. -/
noncomputable def pendingNext (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) : ProbComp Bool :=
  if targetEligible env.parameters prepared then do
    let ephemeral ← simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen
    let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (env.native.encaps prepared.1.context.generated.target)
    pendingAfterEncapsulation env baseImpl kem attachedVerify primitives program post accepted secret prepared ephemeral encapsulated
  else pure false

/-- The pending-branch mass: the identical actual source execution, true only when the accepted continuation runs and returns `true`. -/
noncomputable def pendingActual : ProbComp Bool :=
  PqxdhGeneratedNativeContinuation.nativeContinued attachedVerify primitives baseImpl kem setup (driver env.toDriverEnvironment program)
    (pendingNext env baseImpl kem attachedVerify primitives program post accepted) false

end Actual

/-- The constant-`false` accepted continuation. -/
def rejectAll : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready →
    OracleComp (LocalPostSpec baseSpec) Bool := fun _ _ => pure false

variable (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready →
  OracleComp (LocalPostSpec baseSpec) Bool)

/-- After encapsulation, each leaf of the actual target path splits into its constant-`false` leaf and its accepted-only leaf. -/
theorem after_split (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    𝒟[PqxdhInitialRootEventExperiment.nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program post accepted
      secret prepared ephemeral encapsulated] {true} =
    𝒟[PqxdhInitialRootEventExperiment.nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program post
      (rejectAll env program) secret prepared ephemeral encapsulated] {true} +
    𝒟[pendingAfterEncapsulation env baseImpl kem attachedVerify primitives program post accepted secret prepared ephemeral encapsulated] {true} := by
  rcases encapsulated with _ | ⟨ciphertext, shared⟩
  · simp [PqxdhInitialRootEventExperiment.nativeAfterEncapsulation, pendingAfterEncapsulation]
  · simp only [PqxdhInitialRootEventExperiment.nativeAfterEncapsulation, pendingAfterEncapsulation]
    split
    next failure same => simp [same]
    next same => simp [same, PqxdhInitialRootEventExperiment.nativeAccepted, rejectAll]

/-- The complete actual continuation, including eligibility and private generators, splits in the same way. -/
theorem next_split (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) :
    𝒟[PqxdhInitialRootEventExperiment.nativeNext env baseImpl kem attachedVerify primitives program post accepted secret prepared] {true} =
    𝒟[PqxdhInitialRootEventExperiment.nativeNext env baseImpl kem attachedVerify primitives program post
      (rejectAll env program) secret prepared] {true} +
    𝒟[pendingNext env baseImpl kem attachedVerify primitives program post accepted secret prepared] {true} := by
  unfold PqxdhInitialRootEventExperiment.nativeNext pendingNext
  split
  · apply true_bind_split
    intro ephemeral
    apply true_bind_split
    intro encapsulated
    exact after_split env baseImpl kem attachedVerify primitives program post accepted secret prepared ephemeral encapsulated
  · simp [ ]

/-- The actual root-event experiment is exactly its constant-`false` continuation plus the accepted-branch mass, for any executable accepted continuation. -/
theorem actual_split :
    𝒟[PqxdhInitialRootEventExperiment.actual env baseImpl kem attachedVerify primitives program post accepted] {true} =
    𝒟[PqxdhInitialRootEventExperiment.actual env baseImpl kem attachedVerify primitives program post (rejectAll env program)] {true} +
    𝒟[pendingActual env baseImpl kem attachedVerify primitives program post accepted] {true} := by
  unfold PqxdhInitialRootEventExperiment.actual pendingActual PqxdhGeneratedNativeContinuation.nativeContinued
  apply true_bind_split
  intro stopped
  rcases stopped with ⟨_ | output, state⟩
  · simp
  · exact next_split env baseImpl kem attachedVerify primitives program post accepted _ _

/-- The adversary post with its single target choice attached. -/
def unitPost : PqxdhAdaptiveTargetPost.Post Unit program.Selection baseSpec S (B + 1) :=
  fun selection reply => (fun bit => (some (), bit)) <$> post selection reply

/-- The single fixed target. -/
def unitTargets (target : Target S (B + 1)) : Unit → Target S (B + 1) := fun _ => target

/-- Projecting the unit-choice post back to its bit recovers the original post. -/
theorem mapPost_choose : mapPost (unitPost program post) (choose ()) = post := by
  funext selection reply
  simp [mapPost, unitPost, choose, Functor.map_map]

/-- The certificate projection of the unit-choice post is the original post. -/
theorem mapPost_snd : mapPost (unitPost program post) Prod.snd = post := by
  funext selection reply
  simp [mapPost, unitPost, Functor.map_map]

/-- The original source certificate, transported to the unit-choice post. -/
noncomputable def certificate (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post) :
    PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program (mapPost (unitPost program post) Prod.snd) :=
  (mapPost_snd program post).symm ▸ c

/-- The fixed first-record source event reaches the first-record key-last endpoint with the unit-choice target loss. -/
theorem first_target (target : Target S (B + 1)) (position : target.number.val = 1)
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post
        target.owner target.number target.ancestors target.disclosed).boolDistance
      (PqxdhAdaptiveMessageKeySource.firstIdeal env baseImpl kem attachedVerify primitives program
        (unitPost program post) (unitTargets target) ()) ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env baseImpl kem attachedVerify primitives program
      (unitPost program post) (unitTargets target) (certificate env baseImpl kem program post c) hmac fallback ordinaryFallback () := by
  have mapped := PqxdhAdaptiveNativeResult.actual_map env baseImpl kem attachedVerify primitives program
    (unitPost program post) (unitTargets target) ()
  rw [mapPost_choose] at mapped
  simp only [unitTargets] at mapped
  rw [mapped]
  exact PqxdhAdaptiveMessageKeySource.first_bound env baseImpl kem attachedVerify primitives program
    (unitPost program post) (unitTargets target) (certificate env baseImpl kem program post c) ()
    position compatible adapter functional hmac correct fallback ordinaryFallback

/-- The completed decisions of the actual preparation; every pending preparation contributes `false`. -/
noncomputable def commonOnly (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program post
    target.owner target.number target.ancestors target.disclosed
  match context with
  | .inl decision => pure decision
  | .inr _ => pure false

/-- The first-record key-last endpoint restricted to pending preparations: completed preparations contribute `false`. -/
noncomputable def pendingIdeal (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhAdaptiveMessageKeySource.firstPrepare env baseImpl kem attachedVerify primitives program
    (unitPost program post) (unitTargets target) ()
  let key ← $ᵗ RootOutput
  match context.1 with
  | .inl _ => pure false
  | .inr _ => PqxdhAdaptiveMessageKeySource.firstObserve env context key

/-- The first-record key-last endpoint is exactly its completed decisions plus its pending source-observer mass. -/
theorem ideal_split (target : Target S (B + 1)) :
    𝒟[PqxdhAdaptiveMessageKeySource.firstIdeal env baseImpl kem attachedVerify primitives program
      (unitPost program post) (unitTargets target) ()] {true} =
    𝒟[commonOnly env baseImpl kem attachedVerify primitives program post target] {true} +
    𝒟[pendingIdeal env baseImpl kem attachedVerify primitives program post target] {true} := by
  unfold PqxdhAdaptiveMessageKeySource.firstIdeal pendingIdeal PqxdhAdaptiveMessageKeySource.firstPrepare commonOnly
  simp only [bind_assoc, pure_bind, mapPost_choose, unitTargets]
  apply true_bind_split
  intro context
  rcases context with decision | input
  · simp [PqxdhAdaptiveMessageKeySource.firstObserve, PqxdhAdaptiveFirstMaterial.observe]
  · simp [ ]

set_option backward.isDefEq.respectTransparency false in
/-- The uniform-root endpoint of the constant-`false` root-event protocol is exactly the completed decisions of the actual preparation. -/
theorem completed_uniform (target : Target S (B + 1)) :
    𝒟[uniformGame (rootReduction env.source baseImpl kem
      (PqxdhInitialRootEventExperiment.protocol env kem attachedVerify primitives program post (rejectAll env program)))] =
    𝒟[commonOnly env baseImpl kem attachedVerify primitives program post target] := by
  apply EvalDistEq.evalDist_eq
  simp only [uniformGame, StateT.run'_eq, PqxdhInitialRootContext.reduction_complete,
    commonOnly, PqxdhInitialPreparedSourceInput.prior, PqxdhCorrelatedExtractFamily.prepare,
    bind_assoc, pure_bind, map_bind, map_pure]
  refine EvalDistEq.bind_right _ (fun keys => ?_)
  refine EvalDistEq.bind_right _ (fun mode => ?_)
  refine EvalDistEq.bind_right _ (fun pair => ?_)
  cases mode with
  | completed decision =>
    simp only [PqxdhInitialRootContext.firstMiss, PqxdhInitialRootEventExperiment.protocol, PqxdhAuthenticatedRootExperiment.protocol,
      PqxdhInitialRootContext.afterRoot, PqxdhInitialPreparedSourceInput.input,
      simulateQ_pure, StateT.run_pure, map_pure, EvalDistEq.refl]
  | pending prepared ephemeral =>
    simp only [PqxdhInitialRootContext.firstMiss, PqxdhInitialRootEventExperiment.protocol, PqxdhAuthenticatedRootExperiment.protocol,
      PqxdhInitialRootContext.afterRoot, PqxdhInitialPreparedSourceInput.input, rejectAll,
      simulateQ_pure, StateT.run_pure, map_bind, map_pure]
    exact OracleComp.EvalDistEq.bind_const ($ᵗ RootOutput) (pure false : ProbComp Bool)

/-- The constant-`false` protocol pays the original key-generation, encapsulation, base, decapsulation and preparation bills and nothing after its root. -/
theorem reject_sampler_bounds (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post) :
    PqxdhChallengeSecretQueryBounds.SamplerBounds baseImpl kem
      (PqxdhInitialRootEventExperiment.protocol env kem attachedVerify primitives program post (rejectAll env program))
      c.qKeygen c.qEncap c.qBase c.qDecap c.uPre c.bPre c.dPre 0 0 0 0 := by
  refine ⟨c.keygenBound, c.encapsBound, c.baseBound, c.decapsBound, ?_, ?_⟩
  · intro key
    have original := PqxdhAuthenticatedRootBudgets.prepare_bounds env baseImpl kem attachedVerify primitives program post c key
    exact ⟨original.uniforms, original.bases, original.decaps⟩
  · intro key ciphertext mode root
    cases mode with
    | completed decision => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
    | pending prepared ephemeral =>
      cases root with
      | none => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
      | some value => exact ⟨by trivial, by trivial, by trivial, by trivial⟩

/-- The constant-`false` root reduction makes only its initial root query. -/
theorem reject_root_queries (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post) :
    (rootReduction env.source baseImpl kem
      (PqxdhInitialRootEventExperiment.protocol env kem attachedVerify primitives program post (rejectAll env program))).IsQueryBoundP
      IsRoot 1 :=
  (PqxdhCorrelatedExpandQueryBounds.reduction_bounds env.source baseImpl kem _ _ _ _ _ _ _ _ _ _ _ _
    (reject_sampler_bounds env baseImpl kem attachedVerify primitives program post c)).2

/-- Explicit authenticated-root loss of the constant-`false` continuation: joint identity, KEM correctness error, one-key IND-CCA, Extract and one indexed HMAC term, each for its constructed reduction. -/
noncomputable def completedLoss (hmac : HmacSha512) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) : ℝ :=
  let p := PqxdhInitialRootEventExperiment.protocol env kem attachedVerify primitives program post (rejectAll env program)
  (PqxdhJointIdentity.advantage primitives
    (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
      (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
  (𝒟[simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)] {true}).toReal +
  (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
    (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA).toReal +
  PqxdhCorrelatedExtractFamily.advantage hmac
    (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
  ∑ index ∈ Finset.range 1,
    (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistance
      (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))

/-- The constant-`false` actual experiment is close to the completed decisions of the actual preparation, with the explicit completed-branch root loss. -/
theorem completed_bound (target : Target S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem) (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (PqxdhInitialRootEventExperiment.actual env baseImpl kem attachedVerify primitives program post (rejectAll env program)).boolDistance
      (commonOnly env baseImpl kem attachedVerify primitives program post target) ≤
    completedLoss env baseImpl kem attachedVerify primitives program post hmac fallback ordinaryFallback := by
  have result := PqxdhInitialRootEventComposition.authenticated_root_bound env baseImpl kem attachedVerify primitives program post
    (rejectAll env program) compatible adapter functional hmac sourceCorrect c.noSign c.noCreate fallback ordinaryFallback
    1 (reject_root_queries env baseImpl kem attachedVerify primitives program post c)
  have endpoint := completed_uniform env baseImpl kem attachedVerify primitives program post target
  have same : ∀ game : ProbComp Bool, game.boolDistance (uniformGame (rootReduction env.source baseImpl kem
      (PqxdhInitialRootEventExperiment.protocol env kem attachedVerify primitives program post (rejectAll env program)))) =
      game.boolDistance (commonOnly env baseImpl kem attachedVerify primitives program post target) := fun game => by
    simp only [ProbComp.boolDistance, endpoint]
  simp only [same] at result
  unfold completedLoss
  simpa only [prEvent_eq_evalDist_singleton] using result

/-- The fixed-target source experiment is exactly its constant-`false` continuation plus the mass on which the accepted source-event continuation runs and returns `true`. -/
theorem target_split (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain) :
    𝒟[PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed] {true} =
    𝒟[PqxdhInitialRootEventExperiment.actual env baseImpl kem attachedVerify primitives program post (rejectAll env program)] {true} +
    𝒟[pendingActual env baseImpl kem attachedVerify primitives program post
      (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program post selected number ancestors disclosed)] {true} :=
  actual_split env baseImpl kem attachedVerify primitives program post _

/-- A Boolean game has finite `true` mass. -/
theorem true_ne_top (game : ProbComp Bool) : 𝒟[game] {true} ≠ ⊤ := by
  rw [← prEvent_eq_evalDist_singleton _ true]
  exact prEvent_ne_top _

/-- The pending mass of the fixed first-record source experiment is close to the pending mass of its key-last endpoint, with the first-record target loss plus the completed-branch root loss. -/
theorem pending_bound (target : Target S (B + 1)) (position : target.number.val = 1)
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    |(𝒟[pendingActual env baseImpl kem attachedVerify primitives program post
        (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program post
          target.owner target.number target.ancestors target.disclosed)] {true}).toReal -
      (𝒟[pendingIdeal env baseImpl kem attachedVerify primitives program post target] {true}).toReal| ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env baseImpl kem attachedVerify primitives program
      (unitPost program post) (unitTargets target) (certificate env baseImpl kem program post c) hmac fallback ordinaryFallback () +
    completedLoss env baseImpl kem attachedVerify primitives program post hmac fallback ordinaryFallback := by
  have first := first_target env baseImpl kem attachedVerify primitives program post target position c
    compatible adapter functional hmac correct fallback ordinaryFallback
  have completed := completed_bound env baseImpl kem attachedVerify primitives program post target c
    compatible adapter functional hmac correct.root fallback ordinaryFallback
  simp only [ProbComp.boolDistance] at first completed
  rw [target_split, ideal_split, ENNReal.toReal_add (true_ne_top _) (true_ne_top _),
    ENNReal.toReal_add (true_ne_top _) (true_ne_top _)] at first
  rw [abs_le] at first completed ⊢
  constructor <;> linarith [first.1, first.2, completed.1, completed.2]

/-- The pending mass of the fixed first-record source experiment is at most the pending mass of its key-last endpoint plus the first-record target loss plus the completed-branch root loss. -/
theorem pending_le (target : Target S (B + 1)) (position : target.number.val = 1)
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (𝒟[pendingActual env baseImpl kem attachedVerify primitives program post
        (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program post
          target.owner target.number target.ancestors target.disclosed)] {true}).toReal ≤
    (𝒟[pendingIdeal env baseImpl kem attachedVerify primitives program post target] {true}).toReal +
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env baseImpl kem attachedVerify primitives program
      (unitPost program post) (unitTargets target) (certificate env baseImpl kem program post c) hmac fallback ordinaryFallback () +
    completedLoss env baseImpl kem attachedVerify primitives program post hmac fallback ordinaryFallback := by
  have bound := pending_bound env baseImpl kem attachedVerify primitives program post target position c
    compatible adapter functional hmac correct fallback ordinaryFallback
  rw [abs_le] at bound
  linarith [bound.2]

end BeaconcryptCore.Computational.PqxdhFirstRecordTarget

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.true_bind_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.true_bind_split

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.after_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.after_split

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.next_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.next_split

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.actual_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.actual_split

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.mapPost_choose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.mapPost_choose

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.mapPost_snd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.mapPost_snd

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.first_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.first_target

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.ideal_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.ideal_split

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.completed_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.completed_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.reject_sampler_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.reject_sampler_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.reject_root_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.reject_root_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.completed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.completed_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.target_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.target_split

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.true_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.true_ne_top

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.pending_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.pending_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordTarget.pending_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordTarget.pending_le
