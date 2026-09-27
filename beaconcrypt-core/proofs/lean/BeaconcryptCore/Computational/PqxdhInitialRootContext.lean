import BeaconcryptCore.Computational.PqxdhInitialServiceExperiment

/-!
The uniform-root endpoint of the current authenticated-root proof has a concrete first-miss cut. Its complete actual preparation precedes the fresh32-byte root draw. The continuation keeps that entire prepared context and caches the supplied root at its exact original coordinate before any Server initializer or later Beacon completion runs. Repeated roots therefore retain their original correlations. This is a decomposition of the established root endpoint, not a uniform-established-state assumption.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialRootContext
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhCorrelatedExtractFamily
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhKemIndCca
open PqxdhAuthenticatedRootExperiment PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhSourceAuthenticatedRoot
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Every actual pre-root coin callback and its complete result precede root sampling; no private root cache entry is added by preparation. -/
theorem coins_complete {Result : Type} (work : ProbComp Result) (cache : RootOracle.QueryCache) :
    (simulateQ uniformImpl (rootCoins work)).run cache = (fun result => (result, cache)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      change (simulateQ uniformImpl (RootSpec.query (.inl query) >>= fun answer => rootCoins (next answer))).run cache = _
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change (do
        let answer ← (unifSpec.query query : ProbComp _)
        (simulateQ uniformImpl (rootCoins (next answer))).run cache) = _
      simp only [ih, map_bind]

noncomputable def afterRoot (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : PqxdhChallengeSecretRouting.Protocol baseSpec)
    (prepared : PqxdhCorrelatedExtractFamily.Prepared protocol KemSK) (root : Option RootOutput)
    (cache : RootOracle.QueryCache) : ProbComp (Bool × RootOracle.QueryCache) :=
  (simulateQ uniformImpl (simulateQ (PqxdhCorrelatedExpand.rootPost fixed baseImpl kem prepared.secretKey prepared.ciphertext)
    (protocol.resume prepared.publicKey prepared.ciphertext prepared.state root))).run cache

noncomputable def firstMiss (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : PqxdhChallengeSecretRouting.Protocol baseSpec)
    (prepared : PqxdhCorrelatedExtractFamily.Prepared protocol KemSK) : ProbComp (Bool × RootOracle.QueryCache) :=
  match protocol.initialCoordinates prepared.publicKey prepared.ciphertext prepared.state with
  | none => afterRoot fixed baseImpl kem protocol prepared none ∅
  | some known => do
      let root ← $ᵗ RootOutput
      afterRoot fixed baseImpl kem protocol prepared (some root) ((∅ : RootOracle.QueryCache).cacheQuery (coordinates known) root)

set_option backward.isDefEq.respectTransparency false in
/-- The original initial root callback starts with the actual empty table and therefore draws one independent32-byte root, retaining it at the complete original message before the full continuation. -/
theorem first_miss (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : PqxdhChallengeSecretRouting.Protocol baseSpec)
    (prepared : PqxdhCorrelatedExtractFamily.Prepared protocol KemSK) :
    (simulateQ uniformImpl (PqxdhCorrelatedExpand.rootResume fixed baseImpl kem protocol prepared)).run ∅ =
      firstMiss fixed baseImpl kem protocol prepared := by
  unfold PqxdhCorrelatedExpand.rootResume firstMiss
  cases protocol.initialCoordinates prepared.publicKey prepared.ciphertext prepared.state with
  | none => rfl
  | some known =>
      have absent : (∅ : RootOracle.QueryCache) (coordinates known) = none := rfl
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        uniformImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ absent,
        uniformSampleImpl, bind_map_left, afterRoot]

/-- The entire endpoint factors through its actual pre-root sampler and the fresh-root continuation, preserving the full final cache rather than only a marginal root distribution. -/
theorem reduction_complete (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : PqxdhChallengeSecretRouting.Protocol baseSpec) :
    (simulateQ uniformImpl (PqxdhCorrelatedExpand.rootReduction fixed baseImpl kem protocol)).run ∅ =
      (PqxdhCorrelatedExtractFamily.prepare baseImpl kem protocol >>= firstMiss fixed baseImpl kem protocol) := by
  simp only [PqxdhCorrelatedExpand.rootReduction, simulateQ_bind, StateT.run_bind,
    coins_complete, bind_map_left, first_miss]

/-- The currently integrated authenticated-root uniform game supplies exactly this actual prepared-context sampler and fresh-root cut, including all rejected/completed branches. -/
theorem current_game {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) :
    uniformGame (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem (protocol env kem attachedVerify primitives program post)) =
      Prod.fst <$> (PqxdhCorrelatedExtractFamily.prepare baseImpl kem (protocol env kem attachedVerify primitives program post) >>=
        firstMiss env.source baseImpl kem (protocol env kem attachedVerify primitives program post)) := by
  simp only [uniformGame, StateT.run'_eq, reduction_complete]

set_option backward.isDefEq.respectTransparency false in
/-- At this source cut the added private initializer callbacks recover the same entire continuation and root cache. The supplied root and cache remain private interpreter arguments, not ordinary Extract-observer context. -/
theorem current_continuation {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (prepared : PqxdhCorrelatedExtractFamily.Prepared (protocol env kem attachedVerify primitives program post) KemSK)
    (root : Option RootOutput) (cache : RootOracle.QueryCache) :
    afterRoot env.source baseImpl kem (protocol env kem attachedVerify primitives program post) prepared root cache =
      (simulateQ uniformImpl (simulateQ (PqxdhInitialResponseService.source env.source)
        (simulateQ (PqxdhInitialServiceExperiment.rootPost env.source baseImpl kem prepared.secretKey prepared.ciphertext)
          (PqxdhInitialServiceExperiment.resume env attachedVerify primitives program post prepared.ciphertext prepared.state root)))).run cache := by
  have equation : simulateQ (PqxdhInitialResponseService.source env.source)
      (simulateQ (PqxdhInitialServiceExperiment.rootPost env.source baseImpl kem prepared.secretKey prepared.ciphertext)
        (PqxdhInitialServiceExperiment.resume env attachedVerify primitives program post prepared.ciphertext prepared.state root)) =
      simulateQ (PqxdhCorrelatedExpand.rootPost env.source baseImpl kem prepared.secretKey prepared.ciphertext)
        ((protocol env kem attachedVerify primitives program post).resume prepared.publicKey prepared.ciphertext prepared.state root) := by
    rw [← QueryImpl.simulateQ_compose, PqxdhInitialServiceExperiment.rootPost_source,
      QueryImpl.simulateQ_compose, PqxdhInitialServiceExperiment.resume_source env kem attachedVerify primitives program post prepared.publicKey]
  rw [equation]
  rfl

end BeaconcryptCore.Computational.PqxdhInitialRootContext

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootContext.coins_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootContext.coins_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootContext.first_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootContext.first_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootContext.reduction_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootContext.reduction_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootContext.current_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootContext.current_game

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootContext.current_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootContext.current_continuation
