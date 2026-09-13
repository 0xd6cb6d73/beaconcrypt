import BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment
import BeaconcryptCore.Computational.PqxdhPrivateRootEufBudgets

/-!
The displayed authenticated-root forgery reduction uses the generated Phase1 program, including private generated prekey and one-time records. These resource consumers count that exact reduction's signing, converted-DH and uniform requests and its ordinary joint challenger's identity seed. Every cost follows the original program syntax; no evaluated generator-order equality transfers a query bound.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily
open PqxdhPhase1AcceptanceOracle PqxdhJointPhase1Reports PqxdhDynamicIdentityRouting
open PqxdhJointPhase1AcceptanceComposition PqxdhJointPhase1SourceWriter PqxdhPrivateSourceCoins
open PqxdhPrivateKemSource PqxdhPrivateKemQueryBounds PqxdhPrivatePhase1Prefix
open PqxdhPrivateRootSource PqxdhPrivateRootQueryBounds PqxdhKemIndCca
open PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

set_option backward.isDefEq.respectTransparency false in
/-- Original generated sampling and the complete generated driver contribute their actual private uniform calls; source identity creation remains separately charged by its challenger. -/
theorem program_uniform
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (driver : PqxdhGeneratedPhase1Prefix.Driver setup)
    (qGeneration qDriver : Nat)
    (generationBound : ∀ identity, (generate baseImpl kem setup identity).IsTotalQueryBound qGeneration)
    (driverBound : ∀ index identity generated secret transcript,
      (simulateQ (localSelector baseImpl kem secret) (driver.main index identity generated transcript)).IsQueryBoundP
        (fun query => SourceUniform (translated query)) qDriver) :
    (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver).IsQueryBoundP
      (fun query => SourceUniform (translated query)) (qGeneration + qDriver) := by
  have afterBound : ∀ index publicIdentity generated,
      (PqxdhGeneratedPhase1Prefix.afterGeneration baseImpl kem setup driver index publicIdentity generated).IsQueryBoundP
        (fun query => SourceUniform (translated query)) qDriver := by
    intro index publicIdentity generated
    have writer := signingProgram_excluded_bound index publicIdentity.ed25519
      (publicMaterial setup publicIdentity.ed25519 generated).keyTuple
      (fun query => SourceUniform (.inl query))
      (fun message => by simp [SourceUniform, IsSourceClass, sourceQuery, SourceClass, PqxdhDynamicIdentityPool.IsUniform])
    have result :
        (PqxdhGeneratedPhase1Prefix.afterGeneration baseImpl kem setup driver index publicIdentity generated).IsQueryBoundP
          (fun query => SourceUniform (translated query)) (0 + qDriver) := by
      apply isQueryBoundP_bind
        (publicSource_bound _ SourceUniform 0 (liftDynamic_query_bound _ SourceUniform 0 writer))
      intro bundle _
      cases bundle with
      | none => trivial
      | some bundle =>
          simp only [bind_pure_comp]
          rw [isQueryBoundP_map_iff]
          exact driverBound index publicIdentity (eraseGenerated generated) generated.secret _
    simpa only [Nat.zero_add] using result
  have beforeBound : (PqxdhGeneratedPhase1Prefix.beforeCandidate baseImpl kem setup driver).IsQueryBoundP
      (fun query => SourceUniform (translated query)) (0 + (qGeneration + qDriver)) := by
    apply isQueryBoundP_bind (publicSource_bound _ SourceUniform 0
      (by rw [isQueryBoundP_query_iff]; simp [SourceUniform, IsSourceClass, sourceQuery, SourceClass, PqxdhDynamicIdentityPool.IsUniform]))
    intro created _
    cases created with
    | none => trivial
    | some created =>
      apply isQueryBoundP_bind (PrivateSelectorCoinBudgets.localCoins_uniform _ qGeneration (generationBound created.2.ed25519))
      intro generated _
      exact afterBound created.1 created.2 generated
  have fullBound : (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver).IsQueryBoundP
      (fun query => SourceUniform (translated query)) (0 + (qGeneration + qDriver) + 0) := by
    apply isQueryBoundP_bind beforeBound
    intro prepared _
    cases prepared with
    | none => trivial
    | some prepared =>
      simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        publicSource_bound (SourceSpec.query (.inr prepared.2)) SourceUniform 0
          (by rw [isQueryBoundP_query_iff]; simp [SourceUniform, IsSourceClass, sourceQuery, SourceClass])
  simpa only [Nat.zero_add, Nat.add_zero] using fullBound

set_option maxHeartbeats 1000000 in
/-- The same constructed one-target forgery reduction inherits each original private-program class, with no additional identity reservation. -/
theorem reduction_class
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : PqxdhGeneratedPhase1Prefix.Driver setup) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (kind : Kind) (q : Nat)
    (bounded : (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver).IsQueryBoundP
      (fun query => IsSourceClass (SourceClass (dynamicClass (IsClass kind))) (translated query)) q)
    (publicIdentity : PublicIdentity) :
    (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup driver fallback ordinaryFallback publicIdentity).IsQueryBoundP
      (IsClass kind) q := by
  have compiled := compile_bound _ _ q bounded []
  have reduced := PqxdhPhase1AcceptanceOracle.reduction_query_bound primitives 0 0 fallback ordinaryFallback
    ((simulateQ compile (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver)).run []) kind q
    compiled publicIdentity
  exact reduced.mono (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The actual joint challenger adds its private target seed to the reduction's syntactic uniform cap, without exposing protocol-private coins. -/
theorem reduction_game_uniform
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : PqxdhGeneratedPhase1Prefix.Driver setup) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (qUniform : Nat)
    (bounded : (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver).IsQueryBoundP
      (fun query => IsSourceClass (SourceClass (dynamicClass (IsClass .uniform))) (translated query)) qUniform) :
    (game primitives (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup driver fallback ordinaryFallback)).IsTotalQueryBound
      (32 + qUniform) := by
  exact PqxdhPhase1AcceptanceOracle.reductionGame_uniform_bound primitives 0 0 fallback ordinaryFallback
    ((simulateQ compile (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver)).run []) qUniform
    (compile_bound _ _ qUniform bounded [])


open PqxdhPhase2GeneratedDriver PqxdhPhase2SourceSchedulerBounds
variable {M P I K X Response A : Type} {S B : Nat} {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (program : Program baseSpec setup.Context S (B + 1))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (qWrite : Nat) (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (qLocal : Nat) (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (budget : Budget) (bounded : ∀ reply, Bounded (program.main reply) budget)

include writerBound localBound bounded in
/-- All generated-driver private coins are charged from its actual writer and classified adaptive source schedule, including any locally interpreted base and selected decapsulation calls. -/
theorem driver_uniform
    (uBase uDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound uBase)
    (decapBound : ∀ secret ciphertext, (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound uDecap)
    (index : Nat) (identity : PublicIdentity) (generated : Generated setup Unit) (secret : KemSK)
    (transcript : Phase1PublicTranscript setup.Context) :
    let total := qWrite + bill qLocal budget
    (simulateQ (localSelector baseImpl kem secret)
      ((driver env.toDriverEnvironment program).main index identity generated transcript)).IsQueryBoundP
      (fun query => SourceUniform (translated query)) (total + total + uBase * total + uDecap * total) := by
  have total := PqxdhPhase2GeneratedDriverBounds.driver_total env.toDriverEnvironment program
    qWrite writerBound qLocal localBound budget bounded index identity generated transcript
  exact PrivateSelectorCoinBudgets.localSelector_uniform_bound baseImpl kem secret uBase uDecap baseBound
    (decapBound secret) _ _ _ _ _ total.isQueryBoundP total.isQueryBoundP total.isQueryBoundP total.isQueryBoundP

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The exact generated authentication reduction makes at most the three source-ordered signatures; the caller restrictions are the same checked schedule restrictions used by its authentication theorem. -/
theorem signing_bound
    (primitives : Primitives) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) Creating) 0)
    (publicIdentity : PublicIdentity) :
    (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
      (driver env.toDriverEnvironment program) fallback ordinaryFallback publicIdentity).IsQueryBoundP (IsClass .sign) 3 := by
  refine reduction_class primitives baseImpl kem setup (driver env.toDriverEnvironment program)
    fallback ordinaryFallback .sign 3 ?_ publicIdentity
  have same : IsSigning = IsSourceClass (SourceClass (dynamicClass (IsClass .sign))) := by
    funext query
    cases query <;> rfl
  simpa only [same] using
    (PqxdhPhase2GeneratedDriverBounds.program_source_caps env.toDriverEnvironment program baseImpl kem noSign noCreate).1

set_option maxHeartbeats 1000000 in
include writerBound localBound bounded in
/-- The original generated source schedule bounds every converted-static-DH attempt in the displayed joint reduction, including rejected service inputs. -/
theorem staticDh_bound
    (primitives : Primitives) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (publicIdentity : PublicIdentity) :
    (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
      (driver env.toDriverEnvironment program) fallback ordinaryFallback publicIdentity).IsQueryBoundP
      (IsClass .staticDh) (qWrite + bill qLocal budget) := by
  refine reduction_class primitives baseImpl kem setup (driver env.toDriverEnvironment program)
    fallback ordinaryFallback .staticDh (qWrite + bill qLocal budget) ?_ publicIdentity
  simpa only [Nat.zero_add, Nat.add_zero] using
    PqxdhGeneratedPhase1Prefix.program_source_bound baseImpl kem setup (driver env.toDriverEnvironment program)
      (IsSourceClass (SourceClass (dynamicClass (IsClass .staticDh))))
      (fun coin => by simp [IsSourceClass, sourceQuery, SourceClass, dynamicClass, IsClass])
      0 0 (qWrite + bill qLocal budget) 0
      (by rw [isQueryBoundP_query_iff]; simp [IsSourceClass, sourceQuery, SourceClass, dynamicClass])
      (fun index publicIdentity generated =>
        signingProgram_excluded_bound index publicIdentity.ed25519
          (publicMaterial setup publicIdentity.ed25519 generated).keyTuple _
          (fun message => by simp [IsSourceClass, sourceQuery, SourceClass, dynamicClass, IsClass]))
      (fun index publicIdentity generated transcript =>
        (PqxdhPhase2GeneratedDriverBounds.driver_total env.toDriverEnvironment program
          qWrite writerBound qLocal localBound budget bounded index publicIdentity generated transcript).isQueryBoundP)
      (fun candidate => by rw [isQueryBoundP_query_iff]; simp [IsSourceClass, sourceQuery, SourceClass])

set_option maxHeartbeats 1000000 in
include writerBound localBound bounded in
/-- Complete original-generation and driver sampling bounds instantiate the exact stopped joint reduction and its ordinary challenger; the latter additionally samples the target identity's 32-byte seed. -/
theorem uniform_ledger
    (primitives : Primitives) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (uPrekey uKeygen uOneTime uBase uDecap : Nat)
    (prekeyBound : ∀ identity, (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound uPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound uKeygen)
    (oneTimeBound : ∀ identity before target,
      (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound uOneTime)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound uBase)
    (decapBound : ∀ secret ciphertext, (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound uDecap) :
    let total := qWrite + bill qLocal budget
    let uniforms := (uPrekey + (uKeygen + uOneTime)) + (total + total + uBase * total + uDecap * total)
    (∀ publicIdentity,
      (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
        (driver env.toDriverEnvironment program) fallback ordinaryFallback publicIdentity).IsQueryBoundP (IsClass .uniform) uniforms) ∧
    (game primitives (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
      (driver env.toDriverEnvironment program) fallback ordinaryFallback)).IsTotalQueryBound (32 + uniforms) := by
  dsimp only
  have coins := program_uniform baseImpl kem setup (driver env.toDriverEnvironment program)
    (uPrekey + (uKeygen + uOneTime))
    ((qWrite + bill qLocal budget) + (qWrite + bill qLocal budget) +
      uBase * (qWrite + bill qLocal budget) + uDecap * (qWrite + bill qLocal budget))
    (PqxdhPrivateRootGameBudgets.generate_uniform_bound baseImpl kem setup uPrekey uKeygen uOneTime
      prekeyBound keygenBound oneTimeBound)
    (driver_uniform env program baseImpl kem qWrite writerBound qLocal localBound budget bounded
      uBase uDecap baseBound decapBound)
  simp only [PqxdhPrivateRootEufBudgets.sourceUniform_eq_joint] at coins
  exact ⟨reduction_class primitives baseImpl kem setup (driver env.toDriverEnvironment program)
      fallback ordinaryFallback .uniform _ coins,
    reduction_game_uniform primitives baseImpl kem setup (driver env.toDriverEnvironment program)
      fallback ordinaryFallback _ coins⟩

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.program_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.program_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.reduction_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.reduction_class

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.reduction_game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.reduction_game_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.driver_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.driver_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.signing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.signing_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.staticDh_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.staticDh_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEufResources.uniform_ledger
