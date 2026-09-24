import BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates
import BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy

/-!
The future input-candidate bound is instantiated with the literal source-supported cut, original initializer, saved disclosure/audit seed and original complete post schedule. The source callback certificate derives its complete candidate and masked uniform bills. This endpoint concerns the independent parent/child comparison already used by the evolving-chain proof; it does not silently transfer that bound to actual fixed HKDF, or classify a retained parent retry as a child-input guess.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceFutureInput
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

include bounded preBound applicationBound selectorBound auxBound in
/-- The native fresh candidate event in the entire original stopped suffix has the displayed source-derived cap; no whole-observer or no-future-reveal premise is supplied. -/
theorem source_bound :
    Pr[= true | PqxdhInitialFutureInputCandidates.future source writer mark sender route decode sourceView sourceSample sourceAddress] ≤
      2 * ((Q : ENNReal) / (2 ^ 256 : ENNReal)) := by
  apply PqxdhInitialFutureInputCandidates.future_bound
  intro context output result reached
  have counted := PqxdhInitialSourceSecrecyResources.candidates_bound source writer (pre other) (application other)
    initial (selector other) (aux other) mark sender route decode execution depth state root ancestors disclosed
    selected number remaining qPost bounded costs
    (PqxdhInitialAuditedResources.retained_callbacks source selectedMessage previousRoot response64
      (pre other) (application other) (selector other) (aux other) qPre qApplication qSelector qAux
      preBound applicationBound selectorBound auxBound) context output result reached
  simpa only [PqxdhInitialSourceSecrecyResources.candidateBudget, PqxdhInitialSourceSecrecyResources.callbackBudget,
    PqxdhInitialSupportedCertificate.priorBudget, PqxdhInitialSourceExperiment.execution, List.length_nil, Nat.add_zero,
    candidateBudget] using counted

include bounded preBound applicationBound selectorBound auxBound in
/-- The concrete target-free future tester pays the actual prefix budget, both76-byte samples, and the complete derived source continuation budget. -/
theorem masked_uniform :
    (PqxdhInitialFutureInputCandidates.masked source writer mark sender route decode sourceView sourceSample sourceAddress).IsTotalQueryBound
      (V + (76 + (76 + U))) := by
  apply PqxdhInitialFutureInputCandidates.masked_uniform
  · exact sample_uniform source writer selectedMessage previousRoot response64 other sender route decode
      index metadata ready post before selected number ancestors disclosed shared privateState cache depth
      qPost qPre qApplication qSelector qAux bounded preBound applicationBound selectorBound auxBound
  · intro context output
    have counted := PqxdhInitialSourceSecrecyResources.observed_uniform source writer (pre other) (application other)
      initial (selector other) (aux other) mark sender route decode execution depth state root ancestors disclosed
      selected number remaining qPost bounded costs
      (PqxdhInitialAuditedResources.retained_callbacks source selectedMessage previousRoot response64
        (pre other) (application other) (selector other) (aux other) qPre qApplication qSelector qAux
        preBound applicationBound selectorBound auxBound) context output
    simpa only [PqxdhInitialSourcePreparedSecrecy.view, PqxdhInitialSourceSecrecyResources.uniformBudget, PqxdhInitialSourceSecrecyResources.callbackBudget,
      PqxdhInitialParentObserverBudgets.Costs.cap, PqxdhInitialAuditedResources.retainedCosts, observerBudget] using counted

end BeaconcryptCore.Computational.PqxdhInitialSourceFutureInput

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFutureInput.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFutureInput.source_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFutureInput.masked_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFutureInput.masked_uniform
