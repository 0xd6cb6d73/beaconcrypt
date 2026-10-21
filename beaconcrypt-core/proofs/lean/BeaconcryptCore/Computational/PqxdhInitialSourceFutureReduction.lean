import BeaconcryptCore.Computational.PqxdhInitialFutureInputReduction
import BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy

/-!
The literal supported source continuation now uses its real correlated child. The full-output tester receives all 76 child bytes and adaptively evaluates actual public HKDF candidates. Its 2^-352 comparison term is the size of a fixed 32-byte-input function's image among uniform76 outputs, not hidden entropy after observing the nonce or next chain. The source-derived sampler, complete continuation, original Fresh/Gate and query bills are preserved; retained predecessor retries and global source-origin selection are separate obligations.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceFutureReduction
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
open PqxdhInitialSourcePreparedSecrecy
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
  (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache))
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
  (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
  (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
  (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
  (ancestors disclosed : List RatchetChain)
  (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
  (depth remaining : Nat)


local notation "initial" => PqxdhInitialNativeInitializer.initial source selectedMessage previousRoot response64
local notation "mark" => PqxdhInitialSelectedOrigin.mark source selectedMessage
local notation "execution" => PqxdhInitialSourceExperiment.execution response64 index metadata ready post before
local notation "root" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected
local notation "state" => (PqxdhInitialSourceExperiment.initialState root shared privateState cache, ([] : List RootOutput))
local notation "sourceView" => view source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
local notation "sourceSample" => sample source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth
local notation "sourceAddress" => address source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected shared privateState cache depth

variable (qPost qPre qApplication qSelector qAux : Nat)
  (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
  (preBound : ∀ query ambientState rootCache, (pre other query ambientState rootCache).IsTotalQueryBound qPre)
  (applicationBound : ∀ query ambientState rootCache, (application other query ambientState rootCache).IsTotalQueryBound qApplication)
  (selectorBound : ∀ query ambientState rootCache, (selector other query ambientState rootCache).IsTotalQueryBound qSelector)
  (auxBound : ∀ query ambientState rootCache, (aux other query ambientState rootCache).IsTotalQueryBound qAux)


local notation "costs" => PqxdhInitialAuditedResources.retainedCosts qPre qApplication qSelector qAux
local notation "Q" => candidateBudget before disclosed remaining qPost
local notation "U" => observerBudget remaining qPost qPre qApplication qSelector qAux
local notation "V" => sampleBudget qPost qPre qApplication qSelector qAux


/-- The actual future candidate event with a real child pays the exact joint-sampler tester endpoints; no candidate independence from that child is assumed. -/
theorem source_bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) :
    Pr{let x ← PqxdhInitialFutureInputReduction.realFuture source writer mark sender route decode sourceView sourceSample sourceAddress}[x = true] ≤
      2 * ((2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (PqxdhInitialFutureInputReduction.testerLoss
        source writer mark sender route decode sourceView hmac sourceSample sourceAddress)) := by
  exact PqxdhInitialFutureInputReduction.real_bound source writer mark sender route decode sourceView hmac correct sourceSample sourceAddress

include bounded preBound applicationBound selectorBound auxBound in
/-- The same source-derived tester has two HMAC challenge calls and pays its complete prepared/parent/observer uniform bill, plus at most one real full-HKDF evaluation per actual candidate. -/
theorem tester_queries :
    let observe := PqxdhInitialCommonSecrecy.aliasTester source writer mark sender route decode sourceView
    (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint sourceSample sourceAddress) observe).IsQueryBoundP IsHmacChallengeQuery 2 ∧
      (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint sourceSample sourceAddress) observe).IsQueryBoundP
        PqxdhFullSecretInputKdf.IsHmacUniformQuery ((V + 76) + U) ∧
      (∀ context output result, result ∈ support
        (PqxdhInitialCommonSecrecy.observed source writer mark sender route decode sourceView context output) →
        (RawCtxFullPreimageTester.evaluate output (PqxdhInitialCommonSecrecy.candidates result)).IsTotalQueryBound Q) := by
  have boundedTester := reduction_queries source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
    qPost qPre qApplication qSelector qAux bounded preBound applicationBound selectorBound auxBound
  exact ⟨(boundedTester.1 true).1, (boundedTester.1 true).2, boundedTester.2⟩

include bounded preBound applicationBound selectorBound auxBound in
/-- Every challenger retains the actual prepared sampler, uniform parent and complete source observer; replacement key/output samples are billed separately. -/
theorem tester_challengers (hmac : HmacSha512) :
    let observe := PqxdhInitialCommonSecrecy.aliasTester source writer mark sender route decode sourceView
    let joint := RawCtxSelectedParentSecrecy.joint sourceSample sourceAddress
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound ((V + 76) + U) ∧
      (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound ((V + 76) + (64 + U)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound (64 + ((V + 76) + U)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound ((V + 76) + (64 + (64 + U))) ∧
      (RawCtxSelectedParentSecrecy.random sourceSample sourceAddress observe).IsTotalQueryBound ((V + 76) + (76 + U)) := by
  exact challenger_queries source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
    qPost qPre qApplication qSelector qAux bounded preBound applicationBound selectorBound auxBound hmac true

end BeaconcryptCore.Computational.PqxdhInitialSourceFutureReduction

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFutureReduction.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFutureReduction.source_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFutureReduction.tester_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFutureReduction.tester_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFutureReduction.tester_challengers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFutureReduction.tester_challengers
