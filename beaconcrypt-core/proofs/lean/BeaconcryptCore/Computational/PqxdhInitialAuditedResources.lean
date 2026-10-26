import BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried
import BeaconcryptCore.Computational.PqxdhInitialNativeBudgets
import BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets

/-!
The actual audited source and carried sampler consume the separate original callback resource contracts used by the stopped observer. Their complete uniform bill comes from the seven-callback first builder and sixty-seven callbacks per original post request, with the actual private76/native64 costs and an explicit maximum over external costs. The actual retained initializer supplies its own32-call contract. Candidate bookkeeping and literal source projections add no random query; no distribution equality transports a resource bound.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialAuditedResources
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient PqxdhInitialNativeAudit
open PqxdhInitialParentObserverBudgets (Costs ExternalUniform)
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

def externalBudget (costs : Costs) : PqxdhInitialNativeBudgets.ExternalBudget :=
  ⟨costs.qPre, costs.qApplication, costs.qInitial, costs.qSelector, costs.qAux⟩

def uniformBudget (costs : Costs) (qPost : Nat) : Nat :=
  (7 + qPost * 67) * PqxdhInitialNativeBudgets.callbackCap (externalBudget costs)

section Callbacks
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (costs : Costs) (bounded : ExternalUniform costs pre application initial selector aux)
include bounded

/-- Every actual external callback keeps its separately stated source cost when the initializer's private audit is erased from its optional public reply. -/
theorem local_bounds : PqxdhInitialNativeBudgets.LocalBounds (external pre application initial selector aux) (externalBudget costs) := by
  intro query state cache
  rcases query with query | (reply | (secrets | (query | query)))
  · exact bounded.pre query state cache
  · exact bounded.application reply state cache
  · change (((Prod.snd <$> initial secrets).run state).run cache).IsTotalQueryBound costs.qInitial
    simp only [StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
    exact bounded.initial secrets state cache
  · exact bounded.selector query state cache
  · exact bounded.aux query state cache

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)

/-- The entire original first-builder/post program with its chronological candidate audit has the computed source uniform cap; no whole-program resource premise is used. -/
theorem source_uniform (stage qPost : Nat) (sourceBound : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) :
    ((simulateQ (handler source writer stage pre application initial selector aux)
      (PqxdhInitialNativeCarried.original source mark sender route decode execution)).run state).IsTotalQueryBound (uniformBudget costs qPost) := by
  apply (isQueryBound_map_iff _ (Prod.map id Prod.fst) _ _ _).mp
  rw [program_erase source writer stage pre application initial selector aux]
  exact PqxdhInitialNativeBudgets.source_uniform source writer stage (external pre application initial selector aux)
    (externalBudget costs) (local_bounds pre application initial selector aux costs bounded)
    mark sender route decode execution qPost sourceBound state.1

/-- The exact descriptor-carrying audited source sampler pays the same derived original source cap, preserving every cache, private field and candidate entry. -/
theorem carried_uniform (depth stage qPost : Nat) (sourceBound : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) :
    (PqxdhInitialNativeAuditCarried.carried source writer pre application initial selector aux mark sender route decode execution
      depth stage state).IsTotalQueryBound (uniformBudget costs qPost) :=
  PqxdhInitialNativeAuditCarried.carried_uniform source writer pre application initial selector aux mark sender route decode execution
    depth stage (uniformBudget costs qPost) state
    (PqxdhInitialNativeBudgets.source_uniform source writer stage (external pre application initial selector aux)
      (externalBudget costs) (local_bounds pre application initial selector aux costs bounded)
      mark sender route decode execution qPost sourceBound state.1)

end Callbacks
def retainedCosts (qPre qApplication qSelector qAux : Nat) : Costs :=
  ⟨qPre, qApplication, 32, qSelector, qAux⟩

/-- The concrete original retained root-cache initializer discharges its32-call entry under every cache and state; only the four other individual original callback costs remain parameters. -/
theorem retained_callbacks (source : FixedHkdfSha512NoSaltSource)
    (selected : PqxdhCorrelatedExtractFamily.Message) (previousRoot : RootOutput)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache))
    (application : Response → Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache))
    (qPre qApplication qSelector qAux : Nat)
    (preBound : ∀ query state cache, (pre query state cache).IsTotalQueryBound qPre)
    (applicationBound : ∀ query state cache, (application query state cache).IsTotalQueryBound qApplication)
    (selectorBound : ∀ query state cache, (selector query state cache).IsTotalQueryBound qSelector)
    (auxBound : ∀ query state cache, (aux query state cache).IsTotalQueryBound qAux) :
    ExternalUniform (retainedCosts qPre qApplication qSelector qAux) pre application
      (PqxdhInitialNativeInitializer.initial source selected previousRoot response) selector aux :=
  ⟨preBound, applicationBound, PqxdhInitialNativeInitializer.initial_uniform source selected previousRoot response,
    selectorBound, auxBound⟩

end BeaconcryptCore.Computational.PqxdhInitialAuditedResources

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAuditedResources.local_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAuditedResources.local_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAuditedResources.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAuditedResources.source_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAuditedResources.carried_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAuditedResources.carried_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAuditedResources.retained_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAuditedResources.retained_callbacks
