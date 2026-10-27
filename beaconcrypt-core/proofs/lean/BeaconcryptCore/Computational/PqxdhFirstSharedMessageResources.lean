import BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources
import BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix
import BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds

/-!
The first-record key-order prefix consumes the full concrete preparation bill and adds exactly the full64, nonce12, and next-chain32 sampling interfaces. Forwarding the entire source computation uses only uniform and hash requests in the selected-key challenger; no selected seal or raw opening is introduced before the cut. These resource facts do not simulate the later native key-taking observer.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhFirstSharedMessageResources
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

include postBound selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound keygenBound in
/-- The actual first-record prefix pays all preparation work and the full 64+12+32 bytes; every earlier hash remains shared. -/
theorem first (hash : Bool) :
    (PqxdhFirstSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed).IsQueryBoundP (HashClass hash)
      (if hash then 69 * qMain + 1 + 69 * qPost else
        uniformCost qKeygen qPre qOne qPhase1Write qMain qPost qSelector qLocal qEphemeral qEncaps qPeer qPlaintext qWriter + 108) := by
  have prepared := PqxdhSourceSharedPreparationResources.prepare setup env callbacks program post attachedVerify primitives baseImpl kem
    qPost qSelector qLocal qPeer qPlaintext qWriter postBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound qPre qOne qPhase1Write qMain
    preBound oneBound phase1WriteBound mainBound qKeygen keygenBound selectorBound localBound hash
  have inputBound := (isQueryBoundP_map_iff _
    (PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed) _).mpr prepared
  have whole := isQueryBoundP_bind inputBound (fun context _ =>
    isQueryBoundP_bind (coins ($ᵗ HmacBlock) 64 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) hash) (fun initial _ =>
      isQueryBoundP_bind (coins ($ᵗ NonceOutput) 12 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 12) hash) (fun nonce _ =>
        (isQueryBoundP_map_iff _ (fun chain => (context, initial, nonce, chain)) _).mpr
          (coins ($ᵗ RootOutput) 32 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) hash))))
  convert whole using 1
  · simp only [PqxdhFirstSharedMessagePrefix.run, PqxdhSourceSharedInput.run, bind_pure_comp]
  · cases hash <;> simp [coinsCost]

include postBound selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound keygenBound in
/-- Forwarding the actual complete first-record prefix preserves both source budgets and makes no selected seal or raw opening before the cut. -/
theorem forwarded :
    (simulateQ RawCtxSourceSharedRom.forward (PqxdhFirstSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed)).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute (69 * qMain + 1 + 69 * qPost) ∧
    (simulateQ RawCtxSourceSharedRom.forward (PqxdhFirstSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed)).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute (uniformCost qKeygen qPre qOne qPhase1Write qMain qPost qSelector qLocal qEphemeral qEncaps qPeer qPlaintext qWriter + 108) ∧
    (simulateQ RawCtxSourceSharedRom.forward (PqxdhFirstSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed)).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    (simulateQ RawCtxSourceSharedRom.forward (PqxdhFirstSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed)).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  have bounded := fun hash => first setup env callbacks program post attachedVerify primitives baseImpl kem
    qPost qSelector qLocal qPeer qPlaintext qWriter postBound selectorBound localBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound qPre qOne qPhase1Write qMain
    preBound oneBound phase1WriteBound mainBound qKeygen keygenBound selected number ancestors disclosed hash
  exact RawCtxPrefixKeyOrder.forward_bills _ _ _ (bounded true) (bounded false)

include postBound selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound keygenBound in
/-- Evaluating the same prefix charges each shared digest miss at its full 64-byte cap, for the complete original cache and continuation. The selected challenger's 32-byte key draw is separate. -/
theorem evaluated (cache : CtxRO.QueryCache) :
    ((simulateQ hashImpl (PqxdhFirstSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed)).run cache).IsTotalQueryBound
      ((uniformCost qKeygen qPre qOne qPhase1Write qMain qPost qSelector qLocal qEphemeral qEncaps qPeer qPlaintext qWriter + 108) + 64 * (69 * qMain + 1 + 69 * qPost)) := by
  have bounded := fun hash => first setup env callbacks program post attachedVerify primitives baseImpl kem
    qPost qSelector qLocal qPeer qPlaintext qWriter postBound selectorBound localBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound qPre qOne qPhase1Write qMain
    preBound oneBound phase1WriteBound mainBound qKeygen keygenBound selected number ancestors disclosed hash
  exact AdaptiveCtxSharedSourceBounds.hash_run_bound _ _ _ (bounded false) (bounded true) cache

end BeaconcryptCore.Computational.PqxdhFirstSharedMessageResources

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstSharedMessageResources.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstSharedMessageResources.first

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstSharedMessageResources.forwarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstSharedMessageResources.forwarded

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstSharedMessageResources.evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstSharedMessageResources.evaluated
