import BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture

/-! The fixed-source later chain transition composes its same-event source simulations, explicit collision accounting, concrete main/tester primitive reductions and cached-prefix normalization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceLaterSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
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
local notation "sourceRun" => PqxdhInitialNativeAuditCarried.carried source writer (pre other) (application other) initial (selector other) (aux other)
  mark sender route decode execution depth (depth + 1) state
local notation "sourceView" => view source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
local notation "sourceSample" => sample source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth
local notation "sourceAddress" => address source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected shared privateState cache depth
local notation "external" => PqxdhInitialNativeAudit.external (pre other) (application other) initial (selector other) (aux other)





local notation "actualGame" => PqxdhInitialSourcePreparedSecrecy.actual source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
local notation "randomGame" => PqxdhInitialSourcePreparedSecrecy.random source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
local notation "continuation" => PqxdhInitialSourceLaterMixture.resumed source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth
local notation "early" => sourceSample >>= fun context => ($ᵗ FullOutput) >>= continuation (depth + 1) context
local notation "later" => sourceSample >>= fun context => ($ᵗ FullOutput) >>= continuation (depth + 2) context
local notation "parentSample" => PqxdhInitialSourceLaterMixture.parents source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth
local notation "badEvent" => PqxdhInitialSourceLaterMixture.bad source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected shared privateState cache depth
local notation "observation" => PqxdhInitialSourcePreparedSecrecy.observe source previousRoot response64 selected number ancestors disclosed
local notation "sourceGame" => PqxdhInitialSourceExperiment.game source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache
local notation "normalized" => PqxdhInitialNativeAdjacent.normalized source writer mark sender route decode execution
  (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other) depth state.1 >>= observation

variable (qPost qPre qApplication qSelector qAux : Nat)
  (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
  (preBound : ∀ query ambientState rootCache, (pre other query ambientState rootCache).IsTotalQueryBound qPre)
  (applicationBound : ∀ query ambientState rootCache, (application other query ambientState rootCache).IsTotalQueryBound qApplication)
  (selectorBound : ∀ query ambientState rootCache, (selector other query ambientState rootCache).IsTotalQueryBound qSelector)
  (auxBound : ∀ query ambientState rootCache, (aux other query ambientState rootCache).IsTotalQueryBound qAux)

local notation "primitiveLoss" => PqxdhInitialSourcePreparedSecrecy.loss source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining qPost

include bounded preBound applicationBound selectorBound auxBound in
/-- The original source event pays the two actual collision comparisons around the constructed main/tester reduction, with both endpoint simulations proved from the same source sampler. -/
theorem normalized_bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (position : number.val = (depth + 1) + remaining + 1) :
    ENNReal.ofReal ((sourceGame (depth + 1)).boolDistAdvantage normalized) ≤
      ENNReal.ofReal (primitiveLoss hmac) + 2 * (((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹) := by
  have realBound := PqxdhInitialSourceLaterMixture.real_bound source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining position
  have randomBound := PqxdhInitialSourceLaterMixture.random_bound source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining position
  have primitive := PqxdhInitialSourcePreparedSecrecy.bound source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
    qPost qPre qApplication qSelector qAux bounded preBound applicationBound selectorBound auxBound hmac correct
  have collision := PqxdhInitialSourceLaterMixture.collision_bound source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth qPost bounded
  have triangle : (early).boolDistAdvantage later ≤
      (early).boolDistAdvantage actualGame + (actualGame).boolDistAdvantage randomGame + (randomGame).boolDistAdvantage later := by
    exact (ProbComp.boolDistAdvantage_triangle early actualGame later).trans
      (by have bound := ProbComp.boolDistAdvantage_triangle actualGame randomGame later; linarith)
  have total : ENNReal.ofReal ((early).boolDistAdvantage later) ≤
      ENNReal.ofReal (primitiveLoss hmac) + 2 * Pr[badEvent | parentSample] := by
    have forward := ENNReal.ofReal_le_ofReal triangle
    simp only [ProbComp.boolDistAdvantage] at forward
    rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _),
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at forward
    have back : ENNReal.ofReal ((randomGame).boolDistAdvantage later) ≤ Pr[badEvent | parentSample] := by
      simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using randomBound
    apply forward.trans
    calc
      _ ≤ (Pr[badEvent | parentSample] + ENNReal.ofReal (primitiveLoss hmac)) + Pr[badEvent | parentSample] :=
        add_le_add (add_le_add realBound (ENNReal.ofReal_le_ofReal primitive)) back
      _ = _ := by rw [two_mul]; ac_rfl
  have complete := total.trans (add_le_add le_rfl (mul_le_mul_right collision 2))
  have earlyEq := PqxdhInitialSourceLaterMixture.resumed_real source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth
  have laterEq := PqxdhInitialSourceLaterMixture.resumed_normalized source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth
  simpa only [ProbComp.boolDistAdvantage, probOutput_congr rfl earlyEq, probOutput_congr rfl laterEq] using complete

include bounded preBound applicationBound selectorBound auxBound in
/-- One complete later chain transition in the original source experiment reduces to the constructed Extract/HMAC games, two explicit prior-input collision charges and the coefficient-one cached-prefix sum. Both sides use the identical selected publication and actual full-history freshness event. -/
theorem source_bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (position : number.val = (depth + 1) + remaining + 1) :
    ENNReal.ofReal ((sourceGame (depth + 1)).boolDistAdvantage (sourceGame (depth + 2))) ≤
      ENNReal.ofReal (primitiveLoss hmac) + 2 * (((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹) +
        ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  have normalizedBound := normalized_bound source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
    qPost qPre qApplication qSelector qAux bounded preBound applicationBound selectorBound auxBound hmac correct position
  have sourceBound := PqxdhInitialNativeAdjacent.adjacent_bound source writer mark sender route decode execution
    (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other) depth 0 qPost bounded state.1
    (PqxdhInitialSourceExperiment.initial_valid root shared privateState cache depth).1
    (PqxdhInitialSourceExperiment.initial_valid root shared privateState cache depth).2 observation
  have comparison : ENNReal.ofReal ((sourceGame (depth + 1)).boolDistAdvantage (sourceGame (depth + 2))) ≤
      ENNReal.ofReal ((sourceGame (depth + 1)).boolDistAdvantage normalized) +
        ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
    unfold PqxdhInitialSourcePreparedSecrecy.observe at sourceBound ⊢
    simpa only [PqxdhInitialSourceExperiment.game, PqxdhInitialSourceExperiment.run_source,
      bind_pure_comp, Nat.zero_add] using sourceBound
  exact comparison.trans (add_le_add normalizedBound le_rfl)

end BeaconcryptCore.Computational.PqxdhInitialSourceLaterSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterSecrecy.normalized_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterSecrecy.normalized_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterSecrecy.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterSecrecy.source_bound
