import BeaconcryptCore.Computational.PqxdhInitialSentinelRecords
import BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon

/-!
The initializer analysis marker is removed from the actual first Beacon receive through its typed source callbacks. Preparation, application and initializer service are identical on both sides; the complete shared/private/cache interpreter is retained. No statement identifies arbitrary untyped KDF requests with ratchet requests.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSentinelBeacon
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhPhase2SourceAux
open PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpandHybrid
open PqxdhInitialRootLabelService PqxdhInitialBeaconAmbient PqxdhInitialGenericProtocolBuilder
open RawCtxSelectedParentTable PqxdhInitialSentinelSource
variable {ι I D K X Response A KemSK : Type} {baseSpec : OracleSpec ι}

section Current
variable
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (selected : Message) (response : PqxdhInitialRootLabelService.Response)

noncomputable def evaluated
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (Base A)) :
    QueryImpl (PqxdhInitialFusedCompiler.Spec I D K X Response)
      (Ambient A (BareState count) RootOracle.QueryCache) := fun query state =>
  simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
    ((PqxdhInitialPrivateBeacon.compiler attachedVerify primitives count fixed kdf
      localImpl baseImpl kem secret challenge query).run state)

/-- Every raw callback retains its original ordinary computation and complete shared/private/root-cache state under arbitrary private KDF substitution. -/
theorem raw_source (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (Base A)) :
    (fun query => evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
      selected response kdf (.inr (.inl (.inl query)))) =
      (fun query => PqxdhInitialBeaconAmbient.lift (N := BareState count) (C := RootOracle.QueryCache)
        (RawCtxSharedPrimitive.nativeImpl fixed.crypto kdf query)) := by
  funext query state
  simp only [evaluated, PqxdhInitialPrivateBeacon.compiler, PqxdhInitialPrivateBeacon.raw,
    PqxdhInitialCurrentBeacon.coins_labelled, StateT.run]
  funext cache
  change (fun result => (result, cache)) <$>
    ((fun result => (result.1, (result.2, state.2))) <$>
      (RawCtxSharedPrimitive.nativeImpl fixed.crypto kdf query).run state.1) =
    (fun result => ((result.1, (result.2, state.2)), cache)) <$>
      (RawCtxSharedPrimitive.nativeImpl fixed.crypto kdf query).run state.1
  simp only [Functor.map_map]

private theorem receive_adapter (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (Base A)) :
    RawCtxMixedShared.sharedImpl fixed.crypto writer kdf ∘ₛ RawCtxMixedOwner.receiveAdapter =
      RawCtxSharedPrimitive.nativeImpl fixed.crypto kdf ∘ₛ RawCtxSourceOpen.nativeAdapter := by
  funext query
  simp only [RawCtxMixedOwner.receiveAdapter, QueryImpl.compose]
  rw [← QueryImpl.simulateQ_compose, RawCtxMixedShared.shared_receive]

/-- The actual complete native receive call ignores the analysis marker inside the same current ambient interpreter. -/
theorem calls_marker (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (other target : RootOutput) (extra : NonceOutput) :
    PqxdhInitialGenericBeaconNative.calls (fun query =>
      evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge selected response
        (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target) (.inr (.inl (.inl query)))) =
      PqxdhInitialGenericBeaconNative.calls (fun query =>
        evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge selected response
          (priorKdf prior) (.inr (.inl (.inl query)))) := by
  rw [raw_source, raw_source]
  apply congrArg₂ RawCtxChainOwner.Calls.mk
  · funext kernel sequence context
    simp only [compose_lift, simulate_lift]
    apply congrArg PqxdhInitialBeaconAmbient.lift
    have original := receive_marker (A := A) fixed writer prior other target extra kernel sequence context
    simpa only [receive_adapter] using original
  · rfl


/-- Removing the marker preserves the complete original fused Beacon owner, including all preparation, initialization, rejection and publication branches. -/
theorem owner_marker (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (other target : RootOutput) (extra : NonceOutput)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxBeaconLifecycle.State (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (PqxdhGeneratedBeaconState.KemHandle K)) :
    simulateQ (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge selected response
      (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target))
      (PqxdhInitialFusedOwner.owner decode raw state) =
    simulateQ (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge selected response
      (priorKdf prior)) (PqxdhInitialFusedOwner.owner decode raw state) := by
  rw [← RawCtxGenericRoleStorage.beacon_roundtrip id id (fun _ => rfl) state,
    PqxdhInitialGenericBeaconNative.owner_native, PqxdhInitialGenericBeaconNative.owner_native,
    calls_marker attachedVerify primitives count fixed localImpl baseImpl kem secret challenge selected response writer]
  rfl

end Current
end BeaconcryptCore.Computational.PqxdhInitialSentinelBeacon

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelBeacon.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelBeacon.raw_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelBeacon.calls_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelBeacon.calls_marker

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelBeacon.owner_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelBeacon.owner_marker
