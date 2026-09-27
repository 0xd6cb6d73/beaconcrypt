import BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets
import BeaconcryptCore.Computational.PrivateSelectorCoinBudgets

/-!
Syntactic private-program coin accounting retains every possible public source reply and complete primitive sampling. Creation stays a separate source service: its 32-byte seed belongs to the actual source/challenger ledger, not a second client coin allowance. The same constructed joint-use reduction retains signing, attempted static-DH and uniform caps; no primitive endpoint or global policy is changed.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily
open PqxdhPhase1AcceptanceOracle PqxdhJointPhase1Reports PqxdhDynamicIdentityRouting
open PqxdhJointPhase1AcceptanceComposition PqxdhJointPhase1SourceWriter PqxdhPrivateSourceCoins
open PqxdhPrivateKemSource PqxdhPrivateKemQueryBounds PqxdhPrivatePhase1Prefix
open PqxdhPrivateRootSource PqxdhPrivateRootQueryBounds PqxdhKemIndCca
open PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Arbitrary syntactic source classes include protocol-private work explicitly, through every possible public service reply. -/
theorem program_class_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (qCreate qGeneration qWriter qSelector qAccept : Nat)
    (creation : OracleComp.IsQueryBoundP
      (SourceSpec.query (.inl (.inr .create)) : OracleComp SourceSpec _) predicate qCreate)
    (generationBound : ∀ identity, (localCoins (generate baseImpl kem setup identity)).IsQueryBoundP
      (fun query => predicate (translated query)) qGeneration)
    (writerBound : ∀ index identity keys, (signingProgram index identity keys).IsQueryBoundP
      (fun query => predicate (.inl query)) qWriter)
    (selectorBound : ∀ secret publicTranscript,
      (simulateQ (localSelector baseImpl kem secret) (selector.main publicTranscript)).IsQueryBoundP
        (fun query => predicate (translated query)) qSelector)
    (acceptance : ∀ candidate, OracleComp.IsQueryBoundP
      (SourceSpec.query (.inr candidate) : OracleComp SourceSpec _) predicate qAccept) :
    (program baseImpl kem setup selector).IsQueryBoundP (fun query => predicate (translated query))
      (qCreate + (qGeneration + (qWriter + qSelector)) + qAccept) := by
  have afterBound : ∀ index publicIdentity generated,
      (afterGeneration baseImpl kem setup selector index publicIdentity generated).IsQueryBoundP
        (fun query => predicate (translated query)) (qWriter + qSelector) := by
    intro index publicIdentity generated
    apply isQueryBoundP_bind
      (publicSource_bound _ predicate qWriter (liftDynamic_query_bound _ predicate qWriter (writerBound _ _ _)))
    intro bundle _
    cases bundle with
    | none => trivial
    | some bundle =>
        simpa only [bind_pure_comp, isQueryBoundP_map_iff] using selectorBound generated.secret _
  have beforeBound : (beforeCandidate baseImpl kem setup selector).IsQueryBoundP
      (fun query => predicate (translated query)) (qCreate + (qGeneration + (qWriter + qSelector))) := by
    apply isQueryBoundP_bind (publicSource_bound _ predicate qCreate creation)
    intro created _
    cases created with
    | none => trivial
    | some created =>
        apply isQueryBoundP_bind (generationBound created.2.ed25519)
        intro generated _
        exact afterBound created.1 created.2 generated
  apply isQueryBoundP_bind beforeBound
  intro prepared _
  cases prepared with
  | none => trivial
  | some prepared =>
      simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        publicSource_bound _ predicate qAccept (acceptance prepared.2)

set_option backward.isDefEq.respectTransparency false in
/-- The same constructed one-target forgery reduction inherits each original private-program class, with no additional identity reservation. -/
theorem privateReduction_class_bound
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (kind : Kind) (q : Nat)
    (bounded : (program baseImpl kem setup selector).IsQueryBoundP
      (fun query => IsSourceClass (SourceClass (dynamicClass (IsClass kind))) (translated query)) q)
    (publicIdentity : PublicIdentity) :
    (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback publicIdentity).IsQueryBoundP
      (IsClass kind) q := by
  simpa only [privateReduction, Nat.mul_zero, ite_self, Nat.zero_add] using
    PqxdhPhase1AcceptanceOracle.reduction_query_bound primitives 0 0 fallback ordinaryFallback
      ((simulateQ compile (program baseImpl kem setup selector)).run []) kind q
      (compile_bound _ _ q bounded []) publicIdentity

set_option backward.isDefEq.respectTransparency false in
/-- The actual joint challenger adds its private target seed to the reduction's syntactic uniform cap, without exposing protocol-private coins. -/
theorem privateReduction_game_uniform_bound
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (qUniform : Nat)
    (bounded : (program baseImpl kem setup selector).IsQueryBoundP
      (fun query => IsSourceClass (SourceClass (dynamicClass (IsClass .uniform))) (translated query)) qUniform) :
    (game primitives (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback)).IsTotalQueryBound
      (32 + qUniform) := by
  exact PqxdhPhase1AcceptanceOracle.reductionGame_uniform_bound primitives 0 0 fallback ordinaryFallback
    ((simulateQ compile (program baseImpl kem setup selector)).run []) qUniform
    (compile_bound _ _ qUniform bounded [])

/-- The explicit source coin class is exactly the uniform class used by the existing joint-identity reduction. -/
theorem sourceUniform_eq_joint : SourceUniform =
    IsSourceClass (SourceClass (dynamicClass (IsClass .uniform))) := by
  funext query
  rcases query with (coin | request) | candidate
  · simp [SourceUniform, IsSourceClass, sourceQuery, SourceClass, dynamicClass, IsClass, PqxdhDynamicIdentityPool.IsUniform]
  · cases request with
    | create => rfl
    | reveal identity => rfl
    | service identity request => cases request <;> simp [SourceUniform, IsSourceClass, sourceQuery, SourceClass, dynamicClass, IsClass, PqxdhDynamicIdentityPool.IsUniform]
  · rfl

/-- The private source program pays complete local generation and selection coins; its creation and signing requests remain distinct source classes. -/
theorem program_private_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (qGeneration qSelector : Nat)
    (generationBound : ∀ identity, (generate baseImpl kem setup identity).IsTotalQueryBound qGeneration)
    (selectorBound : ∀ secret publicTranscript,
      (simulateQ (localSelector baseImpl kem secret) (selector.main publicTranscript)).IsQueryBoundP
        (fun query => SourceUniform (translated query)) qSelector) :
    (program baseImpl kem setup selector).IsQueryBoundP
      (fun query => SourceUniform (translated query)) (qGeneration + qSelector) := by
  simpa only [Nat.zero_add, Nat.add_zero] using
    program_class_bound baseImpl kem setup selector SourceUniform 0 qGeneration 0 qSelector 0
      (by rw [isQueryBoundP_query_iff]; simp [SourceUniform, IsSourceClass, sourceQuery, SourceClass, PqxdhDynamicIdentityPool.IsUniform])
      (fun identity => PrivateSelectorCoinBudgets.localCoins_uniform _ _ (generationBound identity))
      (fun index identity keys => signingProgram_excluded_bound index identity keys _
        (fun message => by simp [SourceUniform, IsSourceClass, sourceQuery, SourceClass, PqxdhDynamicIdentityPool.IsUniform]))
      selectorBound
      (fun candidate => by rw [isQueryBoundP_query_iff]; simp [SourceUniform, IsSourceClass, sourceQuery, SourceClass])

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient-one joint reduction makes at most the three actual signing requests, preserving its ordinary auxiliary DH service. -/
theorem privateReduction_sign_bound
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (selectorNoSign : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) IsSigning) 0) (publicIdentity : PublicIdentity) :
    (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback publicIdentity).IsQueryBoundP
      (IsClass .sign) 3 := by
  refine privateReduction_class_bound primitives baseImpl kem setup selector fallback ordinaryFallback .sign 3 ?_ publicIdentity
  have same : IsSigning = IsSourceClass (SourceClass (dynamicClass (IsClass .sign))) := by
    funext query
    cases query <;> rfl
  simpa only [same] using program_sign_bound baseImpl kem setup selector selectorNoSign

/-- The exact authentication reduction and its challenger retain complete private generation and selector coin costs, with one challenger-owned identity seed. -/
theorem privateReduction_uniform_ledger
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (qGeneration qSelector : Nat)
    (generationBound : ∀ identity, (generate baseImpl kem setup identity).IsTotalQueryBound qGeneration)
    (selectorBound : ∀ secret publicTranscript,
      (simulateQ (localSelector baseImpl kem secret) (selector.main publicTranscript)).IsQueryBoundP
        (fun query => SourceUniform (translated query)) qSelector) :
    (∀ publicIdentity,
      (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback publicIdentity).IsQueryBoundP
        (IsClass .uniform) (qGeneration + qSelector)) ∧
    (game primitives (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback)).IsTotalQueryBound
      (32 + (qGeneration + qSelector)) := by
  have coins : (program baseImpl kem setup selector).IsQueryBoundP
      (fun query => IsSourceClass (SourceClass (dynamicClass (IsClass .uniform))) (translated query))
      (qGeneration + qSelector) := by
    simpa only [sourceUniform_eq_joint] using
      program_private_uniform_bound baseImpl kem setup selector qGeneration qSelector generationBound selectorBound
  exact ⟨privateReduction_class_bound primitives baseImpl kem setup selector fallback ordinaryFallback .uniform
      (qGeneration + qSelector) coins,
    privateReduction_game_uniform_bound primitives baseImpl kem setup selector fallback ordinaryFallback
      (qGeneration + qSelector) coins⟩

/-- Every original chosen-DH source attempt is retained in the joint reduction's cap, including rejected peer encodings. -/
theorem privateReduction_staticDh_bound
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (qDh : Nat)
    (selectorBound : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec)
        (IsSourceClass (SourceClass (dynamicClass (IsClass .staticDh))))) qDh)
    (publicIdentity : PublicIdentity) :
    (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback publicIdentity).IsQueryBoundP
      (IsClass .staticDh) qDh := by
  refine privateReduction_class_bound primitives baseImpl kem setup selector fallback ordinaryFallback .staticDh qDh ?_ publicIdentity
  simpa only [Nat.zero_add, Nat.add_zero] using
    program_source_bound baseImpl kem setup selector
      (IsSourceClass (SourceClass (dynamicClass (IsClass .staticDh))))
      (fun coin => by simp [IsSourceClass, sourceQuery, SourceClass, dynamicClass, IsClass]) 0 0 qDh 0
      (by rw [isQueryBoundP_query_iff]; simp [IsSourceClass, sourceQuery, SourceClass, dynamicClass])
      (fun index publicIdentity generated =>
        signingProgram_excluded_bound index publicIdentity.ed25519
          (publicMaterial setup publicIdentity.ed25519 generated).keyTuple _
          (fun message => by simp [IsSourceClass, sourceQuery, SourceClass, dynamicClass, IsClass]))
      selectorBound
      (fun candidate => by rw [isQueryBoundP_query_iff]; simp [IsSourceClass, sourceQuery, SourceClass])

end BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.program_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.program_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.privateReduction_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.privateReduction_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.privateReduction_game_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.privateReduction_game_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.sourceUniform_eq_joint' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.sourceUniform_eq_joint

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.program_private_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.program_private_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.privateReduction_sign_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.privateReduction_sign_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.privateReduction_uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.privateReduction_uniform_ledger

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.privateReduction_staticDh_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets.privateReduction_staticDh_bound
