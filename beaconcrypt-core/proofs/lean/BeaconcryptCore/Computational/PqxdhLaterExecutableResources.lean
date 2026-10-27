import BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion
import BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds
import BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds

/-! The actual source certificate supplies all uniform callback costs to the complete later-record executable continuation. Native and base work are retained in the original evaluated source caps. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace BeaconcryptCore.Computational.PqxdhLaterExecutableResources
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


/-- A conservative shared callback allowance includes both preparation/application classes, the actual root initializer, selector and auxiliary source work. -/
def callbackAllowance (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) : Nat :=
  1 + PqxdhInitialPreparedSourceCaps.callbackCap env0 baseImpl kem program post c +
    PqxdhInitialPreparedSourceCaps.callbackCap env0 baseImpl kem program post c + 32 +
    PqxdhInitialPreparedSourceCaps.selectorCap env0 baseImpl kem program post c + c.qAux

/-- This exact source callback compiler supplies the complete evaluated uniform allowance, including the certificate's base and decapsulation work. -/
theorem external_uniform (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (secret : KemSK) (challenge : MlKem768Ciphertext) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (query : (PqxdhSelectedCallbackCompiler.External (SelectorSpec baseSpec)
      (IdentityHandle I) (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted)
      Response PqxdhPhase2DecapsulationRouting.Shared).Domain)
    (before : Local A (BareState 1) RootOracle.QueryCache) :
    ((PqxdhPreparedSelectedCallbacks.compiler attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem secret challenge
      selectedMessage previousRoot response callbacks (.inl query)).run before).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.UniformRoute (callbackAllowance setup env callbacks program post baseImpl kem c) := by
  have bill := (PqxdhPreparedSelectedCallbackBounds.bills env0 baseImpl kem attachedVerify primitives program post secret challenge callbacks c selectedMessage previousRoot response query before).2.1
  apply bill.mono
  rcases query with query | (reply | (secrets | (query | query))) <;>
    simp only [PqxdhSelectedCallbackCompiler.cost, callbackAllowance, PqxdhInitialPreparedSourceCaps.callbackCap, PqxdhInitialPreparedSourceCaps.selectorCap] <;> omega


/-- Saved publication callbacks plus every original Post request; this conservatively charges all sixteen owner services at the complete actual allowance. -/
def tailAllowance (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) : Nat :=
  1 + (callbackAllowance setup env callbacks program post baseImpl kem c + callbackAllowance setup env callbacks program post baseImpl kem c) +
    PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c * (16 * callbackAllowance setup env callbacks program post baseImpl kem c)

open PqxdhLaterExecutableCompletion in
/-- The full executable sampled suffix pays the actual source certificate on every branch; common decisions retain their original Boolean and no continuation cost is omitted. -/
theorem suffix_uniform (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c)) :
    (suffix setup env callbacks program post attachedVerify primitives baseImpl kem c result).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.UniformRoute (tailAllowance setup env callbacks program post baseImpl kem c) := by
  unfold suffix
  split
  · trivial
  · trivial
  · rename_i start pending shape
    let fits : PqxdhInitialOriginCertificates.Fits (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 := by
      simpa only [PqxdhLaterExecutableCertificates.PacketFits, shape] using result.property
    simpa only [bind_pure_comp, isQueryBoundP_map_iff, tailAllowance] using
      PqxdhLaterSavedUniformBounds.complete_cost
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
      (initialLocal (A := A) (N := BareState 1) (env0).source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem result.val.1.1 result.val.1.2))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
      (view (productionStream env.source.crypto) pending.2.store.1)
      result.val.2.1.2 result.val.2.2.1 result.val.2.2.2
      (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode
      ⟨0, Nat.zero_lt_succ _⟩ AdaptiveCtxDynamicKnownBounds.UniformRoute
      (callbackAllowance setup env callbacks program post baseImpl kem c) (by unfold callbackAllowance; omega)
      (external_uniform setup env callbacks program post attachedVerify primitives baseImpl kem c
        result.val.1.1 result.val.1.2 start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
      (PqxdhInitialPreparedSourceCaps.postCap (PqxdhSourceSharedPreparation.environment setup env callbacks ∅) baseImpl kem program post c) pending.1 result.val.2.1.1.2.material fits pending.2

open PqxdhLaterExecutableCompletion in
/-- The complete executable adds its fully paid continuation to the original complete prefix allowance, including cached continuations and all pre-key draws. -/
theorem client_uniform (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth qUniform : Nat)
    (bounded : (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth).IsQueryBoundP (HashClass false) qUniform) :
    (client setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.UniformRoute (qUniform + (tailAllowance setup env callbacks program post baseImpl kem c)) := by
  rw [← PqxdhLaterSavedSampler.run_erase setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth,
    ← PqxdhLaterExecutableCertificates.certified_erase env callbacks baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c depth,
    isQueryBoundP_map_iff, isQueryBoundP_map_iff] at bounded
  unfold client
  apply isQueryBoundP_bind (m := tailAllowance setup env callbacks program post baseImpl kem c) ?_
    (fun result _ => suffix_uniform setup env callbacks program post attachedVerify primitives baseImpl kem c result)
  simp only [RawCtxSourceSharedRom.forward, QueryImpl.simulateQ_compose]
  apply RawCtxSelectedSealConsumer.lifted_bound
  change (simulateQ AdaptiveCtxSharedTarget.forward _).IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qUniform
  apply AdaptiveCtxSharedTarget.forward_bound
  simpa only [AdaptiveCtxSharedTarget.forward_uniform_class] using bounded

end BeaconcryptCore.Computational.PqxdhLaterExecutableResources

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableResources.external_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableResources.external_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableResources.suffix_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableResources.suffix_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableResources.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableResources.client_uniform
