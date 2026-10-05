import BeaconcryptCore.Computational.PqxdhLaterExecutableResources
import BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources

/-! Complete source-instantiated query classes for the actual later-record component client, retaining every source preparation, cached continuation, native callback and material draw. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhLaterExecutableSourceBills
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhSourceSharedPreparationResources
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (qPost qSelector qLocal qPeer qPlaintext qWriter : Nat)
    (postBound : ∀ selection response, (post selection response).IsTotalQueryBound qPost)
    (selectorBound : ∀ secret query state,
      (evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives 1 query).run state)).IsTotalQueryBound qSelector)
    (localBound : ∀ secret query state, PqxdhOrdinaryNativeCache.sourceSafe query →
      ((PqxdhOrdinaryNativeCache.cacheFree attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret query).run state).IsTotalQueryBound qLocal)
    (peerBound : ∀ state, (callbacks.reservePeer.run state).IsTotalQueryBound qPeer)
    (plaintextBound : ∀ size state, ((callbacks.reservePlaintext size).run state).IsTotalQueryBound qPlaintext)
    (writerBound : ∀ fields state, ((callbacks.responseWrite fields).run state).IsTotalQueryBound qWriter)

variable (qEphemeral qEncaps : Nat)
    (ephemeralBound : (simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen).IsTotalQueryBound qEphemeral)
    (nativeEncapsBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (env.native.encaps target)).IsTotalQueryBound qEncaps)
    (encapsBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncaps)

variable (qPre qOne qPhase1Write qMain : Nat)
    (preBound : ∀ identity, (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPre)
    (oneBound : ∀ identity before target, (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOne)
    (phase1WriteBound : ∀ candidate state, ((callbacks.phase1Write candidate).run state).IsTotalQueryBound qPhase1Write)
    (mainBound : ∀ published, (program.main published).IsTotalQueryBound qMain)


variable (qKeygen : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain)

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

open PqxdhLaterExecutableResources PqxdhLaterExecutableCompletion
open PqxdhLaterSharedMessageResources

include postBound selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound keygenBound in
/-- The ordinary executable client's four classes are discharged from the original source interfaces. No whole-observer or successful-cut resource premise is introduced. -/
theorem source_bills (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) :
    (client setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.UniformRoute
      (uniformCost qKeygen qPre qOne qPhase1Write qMain qPost qSelector qLocal qEphemeral qEncaps qPeer qPlaintext qWriter + 184 +
        parentCost false qPost (PqxdhInitialPreparedSourceCaps.callbackCap env0 baseImpl kem program post c)
          (PqxdhInitialPreparedSourceCaps.selectorCap env0 baseImpl kem program post c) c.qAux +
        tailAllowance setup env callbacks program post baseImpl kem c) ∧
    (client setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute
      (((69 * qMain + 1 + 69 * qPost) + (7 + qPost * 67)) +
        (1 + PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c)) ∧
    (client setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
      (1 + PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) ∧
    (client setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery)
      (1 + PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) := by
  have original := fun hash => PqxdhLaterSharedMessageResources.later setup env callbacks program post attachedVerify primitives baseImpl kem
    qPost qSelector qLocal qPeer qPlaintext qWriter postBound selectorBound localBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound qPre qOne qPhase1Write qMain
    preBound oneBound phase1WriteBound mainBound qKeygen keygenBound selected number ancestors disclosed c hash depth
  exact ⟨client_uniform setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth _ (original false),
    client_hash setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth _ (original true),
    client_record_bills setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth⟩

end BeaconcryptCore.Computational.PqxdhLaterExecutableSourceBills

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableSourceBills.source_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableSourceBills.source_bills
