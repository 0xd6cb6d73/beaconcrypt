import BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates
import BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison

/-! The actual later sampler supplies proof-erased descriptor certificates to a complete ordinary component client. All prior complete/cached decisions and the entire saved request plus adaptive Post remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
open PqxdhNativeSharedPrefix PqxdhSelectedFirstRecord RawCtxSelectedParentTable PqxdhJointKdfGame RawCtxSelectedMessageDriver PqxdhJointKdf
local notation "Front" => PqxdhInitialPostContext.NativeFront M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1)
local notation "Trace" => PqxdhInitialOriginPost.Trace Bool S (B + 1)
local notation "Carrier" => PqxdhLaterSavedSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)

abbrev Output := Bool ⊕ (Carrier × (Option Bool ×
  PqxdhFirstRecordConfidentiality.InsState M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)))


/-- Resume the exact sampled descriptor. The explicit selected key appears only in the component interpreter, not in this executable interface. Arbitrary known-byte correlations are retained. -/
noncomputable def suffix (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c)) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec
    (Output (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response)
      (A := A) (KemSK := KemSK) (S := S) (B := B)) :=
  match shape : result.val.2.1.1.1 with
  | .inl decision => pure (.inl decision)
  | .inr (_, .inl decision) => pure (.inl decision)
  | .inr (start, .inr pending) => do
    let fits : PqxdhInitialOriginCertificates.Fits (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c) pending.1 := by
      simpa only [PqxdhLaterExecutableCertificates.PacketFits, shape] using result.property
    let completed ← PqxdhLaterSavedPostCompiler.complete
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
      (initialLocal (A := A) (N := BareState 1) (env0).source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem result.val.1.1 result.val.1.2))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
      (view (productionStream env.source.crypto) pending.2.store.1)
      result.val.2.1.2 result.val.2.2.1 result.val.2.2.2
      (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode
      ⟨0, Nat.zero_lt_succ _⟩ (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c) pending.1 result.val.2.1.1.2.material fits pending.2
    pure (.inr (result.val, completed))

/-- Execute all original preparation and material draws through the same component interface before the complete saved continuation. -/
noncomputable def client (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec
    (Output (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response)
      (A := A) (KemSK := KemSK) (S := S) (B := B)) := do
  let result ← simulateQ RawCtxSourceSharedRom.forward
    (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
      selected number ancestors disclosed c depth)
  suffix setup env callbacks program post attachedVerify primitives baseImpl kem c result

local instance : MeasurableSpace
    (Output (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response)
      (A := A) (KemSK := KemSK) (S := S) (B := B) × AdaptiveCtxDynamicKnownKeys.SourceState) := ⊤

/-- The ordinary selected-key game has exactly the complete source distribution with the key sampled after the actual shared-ROM prefix. The law includes the full continuation and component state. -/
theorem key_order (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) :
    𝒟[AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
      (client setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth)] =
    𝒟[(do
      let result ← (simulateQ AdaptiveCtxSharedTarget.sharedImpl
        (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
          selected number ancestors disclosed c depth)).run (∅, [])
      let key ← $ᵗ CtxKey
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto key)
        (suffix setup env callbacks program post attachedVerify primitives baseImpl kem c result.1)).run
          (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource result.2))] := by
  apply evalDist_eq_of_evalSPMF_eq
  exact RawCtxPrefixKeyOrder.source_game_vcvioLegacy true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto _ _

/-- The complete sampled saved continuation counts every attempted selected seal, raw opening and public hash before any refusal. Source-local uniform and native primitive work remain separate ledger classes. -/
theorem suffix_bills (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c)) :
    (suffix setup env callbacks program post attachedVerify primitives baseImpl kem c result).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (1 + (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c)) ∧
    (suffix setup env callbacks program post attachedVerify primitives baseImpl kem c result).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (1 + (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c)) ∧
    (suffix setup env callbacks program post attachedVerify primitives baseImpl kem c result).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute (1 + (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c)) := by
  unfold suffix
  split
  · exact ⟨by trivial, by trivial, by trivial⟩
  · exact ⟨by trivial, by trivial, by trivial⟩
  · rename_i start pending shape
    let fits : PqxdhInitialOriginCertificates.Fits (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c) pending.1 := by
      simpa only [PqxdhLaterExecutableCertificates.PacketFits, shape] using result.property
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
      PqxdhLaterSavedPostBounds.component_bills
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
      (initialLocal (A := A) (N := BareState 1) (env0).source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem result.val.1.1 result.val.1.2))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
      (view (productionStream env.source.crypto) pending.2.store.1)
      result.val.2.1.2 result.val.2.2.1 result.val.2.2.2
      (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode
      ⟨0, Nat.zero_lt_succ _⟩ (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c) pending.1 result.val.2.1.1.2.material fits pending.2

/-- The enclosing original source preparation adds no selected seal or raw opening. The complete arbitrary-position client has the same explicit selected request caps. -/
theorem client_record_bills (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) :
    (client setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (1 + (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c)) ∧
    (client setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (1 + (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c)) := by
  constructor
  · unfold client
    simpa only [Nat.zero_add] using isQueryBoundP_bind (PqxdhFirstBeaconRecordCtx.forward_no_seal _)
      (fun result _ => (suffix_bills setup env callbacks program post attachedVerify primitives baseImpl kem c result).1)
  · unfold client
    simpa only [Nat.zero_add] using isQueryBoundP_bind (PqxdhFirstBeaconRecordCtx.forward_no_open _)
      (fun result _ => (suffix_bills setup env callbacks program post attachedVerify primitives baseImpl kem c result).2.1)

/-- Every earlier source hash is retained, including complete cached continuations; only the original post allowance and one saved request are added after that prefix. -/
theorem client_hash (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth qHash : Nat)
    (bounded : (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth).IsQueryBoundP (HashClass true) qHash) :
    (client setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute (qHash + (1 + (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c))) := by
  rw [← PqxdhLaterSavedSampler.run_erase setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth,
    ← PqxdhLaterExecutableCertificates.certified_erase env callbacks baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c depth,
    isQueryBoundP_map_iff, isQueryBoundP_map_iff] at bounded
  unfold client
  apply isQueryBoundP_bind (m := 1 + (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c)) ?_
    (fun result _ => (suffix_bills setup env callbacks program post attachedVerify primitives baseImpl kem c result).2.2)
  simp only [RawCtxSourceSharedRom.forward, QueryImpl.simulateQ_compose]
  apply RawCtxSelectedSealConsumer.lifted_bound
  change (simulateQ AdaptiveCtxSharedTarget.forward _).IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash
  apply AdaptiveCtxSharedTarget.forward_bound
  simpa only [AdaptiveCtxSharedTarget.forward_hash_class] using bounded

end BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion.key_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion.key_order
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion.suffix_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion.suffix_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion.client_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion.client_record_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion.client_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion.client_hash
