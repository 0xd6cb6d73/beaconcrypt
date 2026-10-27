import BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources
import BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix
import BeaconcryptCore.Computational.PqxdhPreparedSharedParentBounds
import BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps
import BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds

/-!
The complete later-record prefix pays the original source preparation, shared 64-byte initializer, all cached-parent continuation work, and the 76+12+32 material draws. Source callback bounds are explicit, and the native later continuation retains its original final publication/freshness decision.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources
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
local notation "Packet" => PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK

def parentCost (hash : Bool) (postCap callbackCap selectorCap auxCap : Nat) : Nat :=
  (7 + postCap * 67) * (if hash then 1 else 76 + callbackCap + callbackCap + 32 + selectorCap + auxCap)

include postBound in
/-- Every reached candidate executes its literal parent preparation or completed branch; the post and callback caps come from the original source interfaces. -/
theorem after (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (hash : Bool) (depth : Nat) (packet : Packet) (output : HmacBlock) :
    (PqxdhLaterSharedParent.after setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed packet output depth).IsQueryBoundP (HashClass hash)
      (parentCost hash qPost (PqxdhInitialPreparedSourceCaps.callbackCap env0 baseImpl kem program post c)
        (PqxdhInitialPreparedSourceCaps.selectorCap env0 baseImpl kem program post c) c.qAux) := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision => trivial
  | pending generated ephemeral =>
    simp only [PqxdhLaterSharedParent.after, PqxdhSourceSharedInput.input,
      PqxdhInitialPreparedSourceInput.input, PqxdhSourceSharedPreparation.restore,
      PqxdhCommonSharedDispatch.restoreMode, PqxdhSharedParentInput.run,
      bind_pure_comp]
    apply (isQueryBoundP_map_iff (p := HashClass hash) _ _ _).mpr
    apply PqxdhPreparedSharedParentBounds.bills env0 callbacks baseImpl kem attachedVerify primitives secretKey ciphertext
      _ output depth qPost (PqxdhInitialPreparedSourceCaps.callbackCap env0 baseImpl kem program post c)
      (PqxdhInitialPreparedSourceCaps.callbackCap env0 baseImpl kem program post c)
      (PqxdhInitialPreparedSourceCaps.selectorCap env0 baseImpl kem program post c) c.qAux
    have caps := PqxdhInitialPreparedSourceCaps.callbacks env0 baseImpl kem attachedVerify primitives program post c secretKey ciphertext
    exact ⟨postBound _, caps.1, caps.2.1, caps.2.2.1, caps.2.2.2, le_rfl⟩

include postBound selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound keygenBound in
/-- The actual later-record prefix pays source preparation, every cached-parent continuation, and all 64+76+12+32 sampled bytes. -/
theorem later (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (hash : Bool) (depth : Nat) :
    (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth).IsQueryBoundP (HashClass hash)
      (if hash then (69 * qMain + 1 + 69 * qPost) + (7 + qPost * 67) else
        uniformCost qKeygen qPre qOne qPhase1Write qMain qPost qSelector qLocal qEphemeral qEncaps qPeer qPlaintext qWriter + 184 +
          parentCost false qPost (PqxdhInitialPreparedSourceCaps.callbackCap env0 baseImpl kem program post c)
            (PqxdhInitialPreparedSourceCaps.selectorCap env0 baseImpl kem program post c) c.qAux) := by
  have prepared := PqxdhSourceSharedPreparationResources.prepare setup env callbacks program post attachedVerify primitives baseImpl kem
    qPost qSelector qLocal qPeer qPlaintext qWriter postBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound qPre qOne qPhase1Write qMain
    preBound oneBound phase1WriteBound mainBound qKeygen keygenBound selectorBound localBound hash
  have whole := isQueryBoundP_bind prepared (fun packet _ =>
    isQueryBoundP_bind (coins ($ᵗ HmacBlock) 64 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) hash) (fun initial _ =>
      isQueryBoundP_bind (after setup env callbacks program post attachedVerify primitives baseImpl kem qPost postBound
        selected number ancestors disclosed c hash depth packet initial) (fun context _ =>
        isQueryBoundP_bind (coins ($ᵗ FullOutput) 76 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76) hash) (fun parent _ =>
          isQueryBoundP_bind (coins ($ᵗ NonceOutput) 12 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 12) hash) (fun nonce _ =>
            (isQueryBoundP_map_iff _ (fun chain =>
              (((context, RawCtxSelectedParentEntry.fromOutput (PqxdhLaterSharedMessagePrefix.address setup context) parent),
                PqxdhOrderedChainHybrids.nextChain parent), nonce, chain)) _).mpr
              (coins ($ᵗ RootOutput) 32 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) hash))))))
  convert whole using 1
  · simp only [PqxdhLaterSharedMessagePrefix.run, PqxdhLaterSharedParent.run, bind_assoc, bind_pure_comp]
  · cases hash <;> simp [coinsCost, parentCost]
    omega

include postBound selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound keygenBound in
/-- Forwarding the complete later-record prefix preserves both source bills and makes no selected seal or raw opening before the cut. -/
theorem forwarded (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) :
    (simulateQ RawCtxSourceSharedRom.forward (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      ((69 * qMain + 1 + 69 * qPost) + (7 + qPost * 67)) ∧
    (simulateQ RawCtxSourceSharedRom.forward (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
      (uniformCost qKeygen qPre qOne qPhase1Write qMain qPost qSelector qLocal qEphemeral qEncaps qPeer qPlaintext qWriter + 184 +
        parentCost false qPost (PqxdhInitialPreparedSourceCaps.callbackCap env0 baseImpl kem program post c)
          (PqxdhInitialPreparedSourceCaps.selectorCap env0 baseImpl kem program post c) c.qAux) ∧
    (simulateQ RawCtxSourceSharedRom.forward (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    (simulateQ RawCtxSourceSharedRom.forward (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  have bounded := fun hash => later setup env callbacks program post attachedVerify primitives baseImpl kem
    qPost qSelector qLocal qPeer qPlaintext qWriter postBound selectorBound localBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound qPre qOne qPhase1Write qMain
    preBound oneBound phase1WriteBound mainBound qKeygen keygenBound selected number ancestors disclosed c hash depth
  exact RawCtxPrefixKeyOrder.forward_bills _ _ _ (bounded true) (bounded false)

include postBound selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound keygenBound in
/-- Evaluating the whole later prefix pays a 64-byte cap for each possible shared-ROM miss. The original cache and complete cached continuation remain present; the selected challenger's 32-byte key draw is separate. -/
theorem evaluated (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) (cache : CtxRO.QueryCache) :
    ((simulateQ hashImpl (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).run cache).IsTotalQueryBound
      ((uniformCost qKeygen qPre qOne qPhase1Write qMain qPost qSelector qLocal qEphemeral qEncaps qPeer qPlaintext qWriter + 184 +
          parentCost false qPost (PqxdhInitialPreparedSourceCaps.callbackCap env0 baseImpl kem program post c)
            (PqxdhInitialPreparedSourceCaps.selectorCap env0 baseImpl kem program post c) c.qAux) +
        64 * ((69 * qMain + 1 + 69 * qPost) + (7 + qPost * 67))) := by
  have bounded := fun hash => later setup env callbacks program post attachedVerify primitives baseImpl kem
    qPost qSelector qLocal qPeer qPlaintext qWriter postBound selectorBound localBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound qPre qOne qPhase1Write qMain
    preBound oneBound phase1WriteBound mainBound qKeygen keygenBound selected number ancestors disclosed c hash depth
  exact AdaptiveCtxSharedSourceBounds.hash_run_bound _ _ _ (bounded false) (bounded true) cache

end BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources.after

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources.later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources.later

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources.forwarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources.forwarded

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources.evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources.evaluated
