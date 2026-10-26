import BeaconcryptCore.Computational.PqxdhInitialRootEventBounds

/-!
The actual source-event root reductions carry a single transparent ledger. Every fixed-source ratchet callback is counted, including the retained local randomness, original auxiliary work, private root requests, and ordinary KEM oracle simulation. HMAC and Extract endpoint sampling are additional costs, not free ambient work. These are formal oracle-query and sampling bounds; deterministic source evaluation, table operations and primitive runtimes remain explicit runtime costs rather than being equated by equality in distribution.
-/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialRootEventResources
open PqxdhJointKdf
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhJointKdfGame PqxdhChallengeSecretRouting
open PqxdhStatefulPhase1EufCma PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateRootSource
open PqxdhPhase2GeneratedDriver PqxdhPrivateAcceptedRoot
open PqxdhAuthenticatedRootExperiment (Post)
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhSecretInputKdf

variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (qPost : Nat) (postTotal : ∀ choice reply, (post choice reply).IsTotalQueryBound qPost)
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

/-- Full reduction sampling includes preparation, the complete continued source work and every private-root decapsulation. -/
def coins : Nat :=
  let n := 7 + qPost * 67
  c.qKeygen + ((c.uPre + c.qBase * c.bPre + c.qDecap * c.dPre) + c.qEncap) +
    (n * PqxdhInitialRootEventBounds.callbackBill c.qLocal c.qAux .uniform + c.qBase * n + c.qDecap * (n + n))

include postTotal
/-- Every indexed root HMAC reduction has one challenge query. Both evaluated challengers also pay their ordinary 64-byte secret-key generation. -/
theorem hmac_queries (hmac : HmacSha512) :
    let p := PqxdhInitialRootEventAccepted.protocol env attachedVerify primitives program post kem selected number ancestors disclosed
    let client := rootReduction env.source baseImpl kem p
    let qCoins := coins env baseImpl kem program post c qPost
    client.IsQueryBoundP PqxdhCorrelatedExpandQueryBounds.IsCoin qCoins ∧
    client.IsQueryBoundP IsRoot (1 + (7 + qPost * 67)) ∧
    ∀ index,
      (indexedReduction hmac client index).IsQueryBoundP PqxdhSecretInputInitializer.IsHmacUniformQuery
        (qCoins + 64 * (1 + (7 + qPost * 67))) ∧
      (indexedReduction hmac client index).IsQueryBoundP PqxdhSecretInputKdf.IsHmacChallengeQuery 1 ∧
      (hmacPrfRealGame hmac (indexedReduction hmac client index)).IsTotalQueryBound
        (64 + qCoins + 64 * (1 + (7 + qPost * 67))) ∧
      (hmacPrfRandomGame (indexedReduction hmac client index)).IsTotalQueryBound
        (64 + qCoins + 64 * (1 + (7 + qPost * 67))) := by
  exact PqxdhAuthenticatedRootEndpoint.reduction_resources env.source baseImpl kem _ hmac
    _ _ _ _ _ _ _ _ _ _ _
    (PqxdhInitialRootEventBounds.sampler_bounds attachedVerify primitives env baseImpl kem program post c qPost postTotal selected number ancestors disclosed)

/-- The exact correlated Extract family has at most one initial and one per continued source callback request, with explicit real/random challenger sampling. -/
theorem extract_queries (hmac : HmacSha512) :
    let p := PqxdhInitialRootEventAccepted.protocol env attachedVerify primitives program post kem selected number ancestors disclosed
    let client := PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p
    let qCoins := coins env baseImpl kem program post c qPost
    client.IsQueryBoundP PqxdhCorrelatedExtractQueryBounds.IsCoin qCoins ∧
    client.IsQueryBoundP PqxdhCorrelatedExtractQueryBounds.IsFamily (1 + (7 + qPost * 67)) ∧
    (PqxdhCorrelatedExtractFamily.realGame hmac client).IsTotalQueryBound (32 + qCoins) ∧
    (PqxdhCorrelatedExtractFamily.randomGame client).IsTotalQueryBound (qCoins + 64 * (1 + (7 + qPost * 67))) := by
  have caps := PqxdhInitialRootEventBounds.sampler_bounds attachedVerify primitives env baseImpl kem program post c qPost postTotal selected number ancestors disclosed
  have queries := PqxdhCorrelatedExtractQueryBounds.reduction_bounds env.source hmac baseImpl kem _ _ _ _ _ _ _ _ _ _ _ _ caps
  have games := PqxdhCorrelatedExtractQueryBounds.reduction_uniform_ledger env.source hmac baseImpl kem _ _ _ _ _ _ _ _ _ _ _ _ caps
  exact ⟨queries.1, queries.2, games.1, games.2⟩

/-- The source-event ordinary CCA reduction preserves all prechallenge oracle budgets and charges both public and private continued decapsulations. -/
theorem cca_queries :
    let p := PqxdhInitialRootEventAccepted.protocol env attachedVerify primitives program post kem selected number ancestors disclosed
    (PqxdhChallengeSecretRouting.reduction env.source kem p).MakesAtMostQueries
      c.uPre c.bPre c.dPre
      ((7 + qPost * 67) * PqxdhInitialRootEventBounds.callbackBill c.qLocal c.qAux .uniform)
      (7 + qPost * 67) ((7 + qPost * 67) + (7 + qPost * 67)) := by
  have caps := PqxdhInitialRootEventBounds.sampler_bounds attachedVerify primitives env baseImpl kem program post c qPost postTotal selected number ancestors disclosed
  exact PqxdhChallengeSecretQueryBounds.reduction_bounds env.source kem _ _ _ _ _ _ _ _ caps.prepare caps.resume

/-- Both CCA challenger branches have the complete interpreted source bill and the branch-independent 32-byte challenge sample. -/
theorem cca_challenger (bit : Bool) :
    let p := PqxdhInitialRootEventAccepted.protocol env attachedVerify primitives program post kem selected number ancestors disclosed
    (simulateQ (kemAmbientImpl baseImpl)
      (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem p) bit)).IsTotalQueryBound
      (c.qKeygen + ((c.uPre + c.qBase * c.bPre + c.qDecap * c.dPre) +
        (c.qEncap + (32 + ((7 + qPost * 67) * PqxdhInitialRootEventBounds.callbackBill c.qLocal c.qAux .uniform +
          c.qBase * (7 + qPost * 67) + c.qDecap * ((7 + qPost * 67) + (7 + qPost * 67))))))) := by
  have caps := PqxdhInitialRootEventBounds.sampler_bounds attachedVerify primitives env baseImpl kem program post c qPost postTotal selected number ancestors disclosed
  exact PqxdhChallengeSecretQueryBounds.fixed_world_uniform_bound env.source baseImpl kem _
    _ _ _ _ _ _ _ _ _ _ _ caps.keygen caps.encaps caps.base caps.decaps caps.prepare caps.resume bit

omit postTotal in
/-- The correctness-error endpoint invokes each ordinary KEM operation once and pays their complete sampling costs. -/
theorem correctness_queries :
    (simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)).IsTotalQueryBound
      (c.qKeygen + c.qEncap + c.qDecap) := by
  exact PqxdhAuthenticatedRootErrorResources.error_uniform baseImpl kem c.qKeygen c.qEncap c.qDecap c.keygenBound c.encapsBound c.decapsBound

include c
omit postTotal in
/-- Authentication uses the original source prefix: exactly the three signing calls and one selected identity creation cap are preserved. -/
theorem signing_queries :
    let work := PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program)
    work.IsQueryBoundP (fun query => PqxdhJointPhase1AcceptanceComposition.IsSigning
      (PqxdhPrivateSourceCoins.translated query)) 3 ∧
    work.IsQueryBoundP (fun query => PqxdhPrivatePhase1Prefix.Creating
      (PqxdhPrivateSourceCoins.translated query)) 1 := by
  exact PqxdhAuthenticatedRootComposition.prefix_source_caps env baseImpl kem program c.noSign c.noCreate

end BeaconcryptCore.Computational.PqxdhInitialRootEventResources

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventResources.hmac_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventResources.hmac_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventResources.extract_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventResources.extract_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventResources.cca_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventResources.cca_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventResources.cca_challenger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventResources.cca_challenger

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventResources.correctness_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventResources.correctness_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventResources.signing_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventResources.signing_queries
