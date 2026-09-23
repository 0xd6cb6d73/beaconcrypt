import BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps
import BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources
import BeaconcryptCore.Computational.PqxdhInitialRootEventResources
import BeaconcryptCore.Computational.PqxdhEvolvingChainComposition

/-!
One original source certificate supplies the query ledgers for the actual root-event, initializer, first-chain and every later-chain reduction. All samplers below use the literal authenticated preparation. Source callback and disclosure-history caps are derived from that preparation, including the complete continued selector interface. The target record fixes the checker length and each later remaining depth. Main and candidate reductions pay their own ordinary challenger coins, while candidate HKDF evaluations are counted separately. No whole-observer resource premise is accepted.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitializerSecrecy
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment
open PqxdhInitialPreparedSourceCaps

/-- Both reduction queries and each literal ordinary challenger are recorded, without treating deterministic local work as random-oracle queries. -/
structure KdfLedger {Context : Type} (hmac : HmacSha512) (sample : SecretInputSampler Context)
    (observe : FullObserver Context) (qSample qObserve : Nat) : Prop where
  challenge : (fullExpandReduction .ratchet sample observe).IsQueryBoundP IsHmacChallengeQuery 2
  uniform : (fullExpandReduction .ratchet sample observe).IsQueryBoundP PqxdhFullSecretInputKdf.IsHmacUniformQuery (qSample + qObserve)
  extractReal : (extractRealGame hmac sample (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound (qSample + qObserve)
  extractUniform : (extractUniformGame sample (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound (qSample + (64 + qObserve))
  hmacReal : (hmacPrfRealGame hmac (fullExpandReduction .ratchet sample observe)).IsTotalQueryBound (64 + (qSample + qObserve))
  hmacRandom : (hmacPrfRandomGame (fullExpandReduction .ratchet sample observe)).IsTotalQueryBound (qSample + (64 + (64 + qObserve)))

/-- An evolving transition also pays the independently sampled complete76-byte child. -/
structure ChildLedger {Context : Type} (hmac : HmacSha512) (sample : SecretInputSampler Context)
    (observe : FullObserver Context) (random : ProbComp Bool) (qSample qObserve : Nat)
    : Prop extends KdfLedger hmac sample observe qSample qObserve where
  child : random.IsTotalQueryBound (qSample + (76 + qObserve))

variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

local notation "sourcePrior" => PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed
local notation "qPost" => postCap env baseImpl kem program post c
local notation "qCallback" => callbackCap env baseImpl kem program post c
local notation "qSelector" => selectorCap env baseImpl kem program post c
local notation "qKnown" => knownCap env baseImpl kem program post c disclosed
local notation "qCheck" => (number.val - 1 + 1)
local notation "caps" => supported_caps env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed
local notation "priorBound" => prior_uniform env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed

def priorBudget : Nat := c.qKeygen + ((c.uPre + c.qBase * c.bPre + c.qDecap * c.dPre) + c.qEncap)
local notation "qPrior" => priorBudget env baseImpl kem program post c
local notation "initialU" => PqxdhInitialSourceInitialResources.uniformCap qPost qCallback qCallback qSelector c.qAux
local notation "firstU" => PqxdhInitialHalfResources.uniformCap qPost qCheck qCallback qCallback qSelector c.qAux
local notation "firstQ" => PqxdhInitialHalfResources.candidateCap qPost qCheck qKnown
local notation "firstJoint" => PqxdhInitialSourceFirstResources.joint sourcePrior
local notation "firstObserve" => PqxdhInitialSourceFirstResources.reductionObserver env.source env.recordWriter env.senderId env.route env.decode sourcePrior

/-- The actual source input retains exactly the externally fixed selected record number throughout preparation. -/
theorem input_number (input : PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup))
    (supported : Sum.inr input ∈ support sourcePrior) : input.number = number := by
  simp only [PqxdhInitialPreparedSourceInput.prior, support_map] at supported
  obtain ⟨context, _, equality⟩ := supported
  cases mode : context.state with
  | completed decision => simp [PqxdhInitialPreparedSourceInput.input, mode] at equality
  | pending prepared ephemeral =>
    simp only [PqxdhInitialPreparedSourceInput.input, mode, Sum.inr.injEq] at equality
    subst input
    rfl

/-- The first source transition uses the exact target checker length and all caps derived from the original authenticated preparation. -/
theorem first_caps (input : PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup))
    (supported : Sum.inr input ∈ support sourcePrior) :
    PqxdhInitialSourceFirstResources.Caps input qPost qCheck qKnown qCallback qCallback qSelector c.qAux := by
  have bounded := caps input supported
  refine ⟨bounded.postBound, ?_, bounded.knownBound, bounded.preBound, bounded.applicationBound, bounded.selectorBound, bounded.auxBound⟩
  rw [input_number env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed input supported]

local notation "firstCaps" => first_caps env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed

/-- The actual initial64 reduction and all four primitive games use the same preparation and full source event; only the two ordinary HMAC challenges are externalized. -/
theorem initial_queries (hmac : HmacSha512) :
    KdfLedger hmac (PqxdhInitialSourceInitialSecrecy.sampler sourcePrior)
      (PqxdhInitialSourceInitialSecrecy.observer env.source env.recordWriter env.senderId env.route env.decode)
      (qPrior + 32) initialU := by
  have query := PqxdhInitialSourceInitialResources.reduction_queries env.source env.recordWriter env.senderId env.route env.decode
    qPost qCheck qKnown qCallback qCallback qSelector c.qAux sourcePrior firstCaps qPrior priorBound
  have games := PqxdhInitialSourceInitialResources.challenger_queries env.source env.recordWriter env.senderId env.route env.decode
    qPost qCheck qKnown qCallback qCallback qSelector c.qAux sourcePrior firstCaps hmac qPrior priorBound
  exact ⟨query.1, query.2, games.1, games.2.1, games.2.2.1, games.2.2.2⟩

/-- Main and candidate first-chain reductions include the original source preparation, full76 parent and retained source/checker continuation, plus each literal challenger bill. -/
theorem first_queries (hmac : HmacSha512) (forTester : Bool) :
    ChildLedger hmac firstJoint (firstObserve forTester)
      (RawCtxSelectedParentSecrecy.random (RawCtxSupportedSample.sum sourcePrior)
        (PqxdhInitialSourceFirstResources.address sourcePrior) (firstObserve forTester))
      (qPrior + 76) firstU := by
  have query := (PqxdhInitialSourceFirstResources.reduction_queries env.source env.recordWriter env.senderId env.route env.decode
    sourcePrior qPost qCheck qKnown qCallback qCallback qSelector c.qAux firstCaps qPrior priorBound).1 forTester
  have games := PqxdhInitialSourceFirstResources.challenger_queries env.source env.recordWriter env.senderId env.route env.decode
    sourcePrior qPost qCheck qKnown qCallback qCallback qSelector c.qAux firstCaps hmac qPrior priorBound forTester
  exact ⟨⟨query.1, query.2, games.1, games.2.1, games.2.2.1, games.2.2.2.1⟩, games.2.2.2.2⟩

variable (depth : Nat)
local notation "remaining" => (number.val - 1 - 1 - depth)
local notation "laterSample" => PqxdhInitialSampledParent.sample env.source env.recordWriter env.senderId env.route env.decode depth sourcePrior
local notation "laterAddress" => PqxdhInitialSampledParent.address (prior := sourcePrior) env.source env.recordWriter env.senderId env.route env.decode depth
local notation "laterJoint" => RawCtxSelectedParentSecrecy.joint laterSample laterAddress
local notation "laterObserve" => PqxdhInitialSampledReduction.reductionObserver env.source env.recordWriter env.senderId env.route env.decode depth remaining sourcePrior
local notation "laterV" => qPrior + (64 + PqxdhInitialSourcePreparedSecrecy.sampleBudget qPost qCallback qCallback qSelector c.qAux)
local notation "laterU" => PqxdhInitialSourcePreparedSecrecy.observerBudget remaining qPost qCallback qCallback qSelector c.qAux

/-- Every ordered later reduction uses its same global source prefix, complete sampled parent and exact remaining target depth. The main and candidate games each carry their own ordinary challenger bill. -/
theorem later_queries (hmac : HmacSha512) (forTester : Bool) :
    ChildLedger hmac laterJoint (laterObserve forTester)
      (RawCtxSelectedParentSecrecy.random laterSample laterAddress (laterObserve forTester))
      (laterV + 76) laterU := by
  have query := (PqxdhInitialSampledReduction.reduction_queries env.source env.recordWriter env.senderId env.route env.decode
    depth remaining sourcePrior qPost qCallback qCallback qSelector c.qAux qKnown caps qPrior priorBound).1 forTester
  have games := PqxdhInitialSampledReduction.challenger_queries env.source env.recordWriter env.senderId env.route env.decode
    depth remaining sourcePrior qPost qCallback qCallback qSelector c.qAux qKnown caps qPrior priorBound hmac forTester
  exact ⟨⟨query.1, query.2, games.1, games.2.1, games.2.2.1, games.2.2.2.1⟩, games.2.2.2.2⟩

/-- The complete first source checker counts each real fixed-HKDF candidate evaluation separately from its ordinary uniform queries. -/
theorem first_candidates :
    ∀ context output result, result ∈ support
      (PqxdhInitialHalfSecrecy.observed env.source env.recordWriter (PqxdhInitialSourceFirstResources.mark env.source sourcePrior)
        env.senderId env.route env.decode (PqxdhInitialSourceFirstResources.view env.source sourcePrior) context output) →
      (RawCtxFullPreimageTester.evaluate output (PqxdhInitialHalfSecrecy.candidates result)).IsTotalQueryBound firstQ := by
  exact (PqxdhInitialSourceFirstResources.reduction_queries env.source env.recordWriter env.senderId env.route env.decode
    sourcePrior qPost qCheck qKnown qCallback qCallback qSelector c.qAux firstCaps qPrior priorBound).2

/-- Every later checker has its own exact remaining-depth candidate bill over the same actual preparation and source prefix. -/
theorem later_candidates :
    ∀ context output result, result ∈ support
      (PqxdhInitialSampledParent.observed (prior := sourcePrior) env.source env.recordWriter env.senderId env.route env.decode depth remaining context output) →
      (RawCtxFullPreimageTester.evaluate output (PqxdhInitialCommonSecrecy.candidates result)).IsTotalQueryBound
        (PqxdhInitialSampledResources.candidateCap remaining qPost qKnown) := by
  exact (PqxdhInitialSampledReduction.reduction_queries env.source env.recordWriter env.senderId env.route env.decode
    depth remaining sourcePrior qPost qCallback qCallback qSelector c.qAux qKnown caps qPrior priorBound).2

local notation "rootProtocol" => PqxdhInitialRootEventAccepted.protocol env attachedVerify primitives program post kem selected number ancestors disclosed
local notation "rootClient" => PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem rootProtocol
local notation "rootQ" => PqxdhInitialRootEventResources.coins env baseImpl kem program post c qPost
local notation "rootN" => (7 + qPost * 67)
local notation "rootR" => (1 + rootN)
local notation "postTotal" => PqxdhInitialPreparedSourceCaps.post_total env baseImpl kem program post c

/-- Root reduction, primitive challengers, authentication and correctness resources are all attached to the same concrete source-event protocol. -/
structure RootLedger (hmac : HmacSha512) : Prop where
  coins : (rootClient).IsQueryBoundP PqxdhCorrelatedExpandQueryBounds.IsCoin rootQ
  roots : (rootClient).IsQueryBoundP PqxdhCorrelatedExpandHybrid.IsRoot rootR
  hmacs : ∀ index,
    (PqxdhCorrelatedExpandHybrid.indexedReduction hmac rootClient index).IsQueryBoundP PqxdhSecretInputInitializer.IsHmacUniformQuery (rootQ + 64 * rootR) ∧
    (PqxdhCorrelatedExpandHybrid.indexedReduction hmac rootClient index).IsQueryBoundP IsHmacChallengeQuery 1 ∧
    (hmacPrfRealGame hmac (PqxdhCorrelatedExpandHybrid.indexedReduction hmac rootClient index)).IsTotalQueryBound (64 + rootQ + 64 * rootR) ∧
    (hmacPrfRandomGame (PqxdhCorrelatedExpandHybrid.indexedReduction hmac rootClient index)).IsTotalQueryBound (64 + rootQ + 64 * rootR)
  extracts : let client := PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem rootProtocol
    client.IsQueryBoundP PqxdhCorrelatedExtractQueryBounds.IsCoin rootQ ∧
    client.IsQueryBoundP PqxdhCorrelatedExtractQueryBounds.IsFamily rootR ∧
    (PqxdhCorrelatedExtractFamily.realGame hmac client).IsTotalQueryBound (32 + rootQ) ∧
    (PqxdhCorrelatedExtractFamily.randomGame client).IsTotalQueryBound (rootQ + 64 * rootR)
  cca : (PqxdhChallengeSecretRouting.reduction env.source kem rootProtocol).MakesAtMostQueries
    c.uPre c.bPre c.dPre
    (rootN * PqxdhInitialRootEventBounds.callbackBill c.qLocal c.qAux .uniform) rootN (rootN + rootN)
  ccaGames : ∀ bit, (simulateQ (kemAmbientImpl baseImpl)
    (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl))
      (PqxdhChallengeSecretRouting.reduction env.source kem rootProtocol) bit)).IsTotalQueryBound
      (c.qKeygen + ((c.uPre + c.qBase * c.bPre + c.qDecap * c.dPre) +
        (c.qEncap + (32 + (rootN * PqxdhInitialRootEventBounds.callbackBill c.qLocal c.qAux .uniform +
          c.qBase * rootN + c.qDecap * (rootN + rootN))))))
  correctness : (simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)).IsTotalQueryBound
    (c.qKeygen + c.qEncap + c.qDecap)
  signing : let work := PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program)
    work.IsQueryBoundP (fun query => PqxdhJointPhase1AcceptanceComposition.IsSigning (PqxdhPrivateSourceCoins.translated query)) 3 ∧
    work.IsQueryBoundP (fun query => PqxdhPrivatePhase1Prefix.Creating (PqxdhPrivateSourceCoins.translated query)) 1

/-- All root-event ledgers consume this same original certificate; its source post partition supplies the complete continued request count. -/
theorem root_queries (hmac : HmacSha512) :
    RootLedger env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed hmac := by
  have queries := PqxdhInitialRootEventResources.hmac_queries env baseImpl kem attachedVerify primitives program post c
    qPost postTotal selected number ancestors disclosed hmac
  exact ⟨queries.1, queries.2.1, queries.2.2,
    PqxdhInitialRootEventResources.extract_queries env baseImpl kem attachedVerify primitives program post c qPost postTotal selected number ancestors disclosed hmac,
    PqxdhInitialRootEventResources.cca_queries env baseImpl kem attachedVerify primitives program post c qPost postTotal selected number ancestors disclosed,
    PqxdhInitialRootEventResources.cca_challenger env baseImpl kem attachedVerify primitives program post c qPost postTotal selected number ancestors disclosed,
    PqxdhInitialRootEventResources.correctness_queries env baseImpl kem program post c,
    PqxdhInitialRootEventResources.signing_queries env baseImpl kem program post c⟩

/-- The ordinary-game ledger at exactly this ordered later depth. -/
def LaterLedger (hmac : HmacSha512) : Prop := ∀ forTester,
  ChildLedger hmac laterJoint (laterObserve forTester)
    (RawCtxSelectedParentSecrecy.random laterSample laterAddress (laterObserve forTester)) (laterV + 76) laterU

/-- Candidate evaluations at exactly this ordered later depth. -/
def LaterTester : Prop := ∀ context output result, result ∈ support
  (PqxdhInitialSampledParent.observed (prior := sourcePrior) env.source env.recordWriter env.senderId env.route env.decode depth remaining context output) →
  (RawCtxFullPreimageTester.evaluate output (PqxdhInitialCommonSecrecy.candidates result)).IsTotalQueryBound
    (PqxdhInitialSampledResources.candidateCap remaining qPost qKnown)

/-- The final value-consistent source endpoint also pays its own complete preparation, root32, shared64, source work and conservative initializer-miss bill. -/
theorem ideal_uniform :
    (PqxdhInitialSourceAliases.consistent env.source env.recordWriter env.senderId env.route env.decode sourcePrior number.val).IsTotalQueryBound
      ((qPrior + (32 + 64)) + (initialU + 32 * (1 + (7 + qPost * 67)))) := by
  exact PqxdhInitialSourceAliasResources.consistent_uniform env.source env.recordWriter env.senderId env.route env.decode
    qPost qCheck qKnown qCallback qCallback qSelector c.qAux sourcePrior firstCaps number.val qPrior priorBound

/-- The single source certificate checks all primitive game budgets and every real candidate evaluation used by the authenticated evolving-chain sum. No sampler, observer or history cap is supplied separately. -/
structure Ledger (hmac : HmacSha512) : Prop where
  root : RootLedger env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed hmac
  initial : KdfLedger hmac (PqxdhInitialSourceInitialSecrecy.sampler sourcePrior)
    (PqxdhInitialSourceInitialSecrecy.observer env.source env.recordWriter env.senderId env.route env.decode) (qPrior + 32) initialU
  first : ∀ forTester, ChildLedger hmac firstJoint (firstObserve forTester)
    (RawCtxSelectedParentSecrecy.random (RawCtxSupportedSample.sum sourcePrior)
      (PqxdhInitialSourceFirstResources.address sourcePrior) (firstObserve forTester)) (qPrior + 76) firstU
  later : ∀ atDepth, atDepth < number.val - 1 →
    LaterLedger env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed atDepth hmac
  ideal : (PqxdhInitialSourceAliases.consistent env.source env.recordWriter env.senderId env.route env.decode sourcePrior number.val).IsTotalQueryBound
    ((qPrior + (32 + 64)) + (initialU + 32 * (1 + (7 + qPost * 67))))
  firstTester : ∀ context output result, result ∈ support
    (PqxdhInitialHalfSecrecy.observed env.source env.recordWriter (PqxdhInitialSourceFirstResources.mark env.source sourcePrior)
      env.senderId env.route env.decode (PqxdhInitialSourceFirstResources.view env.source sourcePrior) context output) →
    (RawCtxFullPreimageTester.evaluate output (PqxdhInitialHalfSecrecy.candidates result)).IsTotalQueryBound firstQ
  laterTester : ∀ atDepth, atDepth < number.val - 1 →
    LaterTester env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed atDepth

/-- This one checked consumer instantiates every root, initializer, first-chain and later-chain resource obligation for the exact original authenticated source preparation. -/
theorem complete (hmac : HmacSha512) :
    Ledger env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed hmac := by
  exact ⟨root_queries env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed hmac,
    initial_queries env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed hmac,
    first_queries env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed hmac,
    fun depth _ => later_queries env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed depth hmac,
    ideal_uniform env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed,
    first_candidates env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed,
    fun depth _ => later_candidates env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed depth⟩

end BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.input_number' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.input_number

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.first_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.first_caps

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.initial_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.initial_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.first_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.first_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.later_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.later_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.first_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.first_candidates

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.later_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.later_candidates

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.root_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.root_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.complete

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.ideal_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources.ideal_uniform
