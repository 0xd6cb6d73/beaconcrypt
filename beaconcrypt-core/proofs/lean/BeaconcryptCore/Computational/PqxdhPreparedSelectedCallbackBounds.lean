import BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbacks
import BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps

/-!
The actual authenticated source certificate pays every callback in the selected-message compiler. Preparation/application include the local primitive and permitted decapsulation work, initialization retains its 32-byte root-cache allowance, and selector creation/base/decapsulation and publication work stay explicit. No whole-observer bound is assumed.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialBeaconAmbient PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment
open PqxdhPhase1AcceptanceOracle PqxdhPrivateKemSource PqxdhGeneratedBeaconState
open PqxdhInitialPreparedSourceInput PqxdhInitialSourcePreparedSecrecy
open PqxdhInitialPreparedSourceCaps PqxdhNativeSharedPrefix
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (secret : KemSK) (challenge : MlKem768Ciphertext)

/-- The actual source preparation executes its original local and decapsulation work within the authenticated certificate. -/
theorem preparation (query : (PqxdhBeaconPhase2Shared.Spec (IdentityHandle I) (DhPair setup) (KemHandle K)
      (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared).Domain)
    (state : ExternalState A (BareState 1) RootOracle.QueryCache) :
    ((PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret challenge query).run state).IsTotalQueryBound
      (callbackCap env baseImpl kem program post c) := by
  have original := interpreted_callback env baseImpl kem attachedVerify primitives program post c secret challenge (.inl query) ((state.1.1, ∅), state.1.2)
  simpa only [PqxdhPreparedPrefixCallbacks.preparation, PqxdhPreparedPrefixCallbacks.rootLocal,
    PqxdhInitialCtxFreeCallbacks.cacheFree, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using original

/-- The actual optional application getter retains every callback cost, including permitted decapsulation. -/
theorem application (reply : Response) (state : ExternalState A (BareState 1) RootOracle.QueryCache) :
    ((PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret challenge reply).run state).IsTotalQueryBound
      (callbackCap env baseImpl kem program post c) := by
  have original := interpreted_callback env baseImpl kem attachedVerify primitives program post c secret challenge (.inr (.inr reply)) ((state.1.1, ∅), state.1.2)
  simpa only [PqxdhPreparedPrefixCallbacks.application, PqxdhPreparedPrefixCallbacks.rootLocal,
    PqxdhInitialCtxFreeCallbacks.cacheFree, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using original

/-- The concrete selector keeps its original creation, uniform, base and permitted decapsulation charge. -/
theorem selector (query : (SelectorSpec baseSpec).Domain) (state : ExternalState A (BareState 1) RootOracle.QueryCache) :
    ((PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
      (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge) query).run state).IsTotalQueryBound
      (selectorCap env baseImpl kem program post c) := by
  simpa only [PqxdhPreparedPrefixCallbacks.selectorLocal, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    selector_uniform env baseImpl kem attachedVerify primitives program post c secret challenge query state.1.2 state.2

def sourceEnvironment (callbacks : PqxdhSourceAuxiliary.Callbacks A) :=
  { env with aux := PqxdhSourceAuxiliary.server callbacks }

/-- The actual publication dispatch retains its original finite callback allowance; only the unmodified CTX cache projection is removed. -/
theorem auxiliary (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (c : PqxdhAuthenticatedRootBudgets.Certificate (sourceEnvironment env callbacks) baseImpl kem program post)
    (query : PqxdhServerRegistrationPublication.AuxSpec.Domain)
    (state : ExternalState A (BareState 1) RootOracle.QueryCache) :
    ((PqxdhPreparedPrefixCallbacks.auxiliaryLocal (N := BareState 1) (C := RootOracle.QueryCache) callbacks query).run state).IsTotalQueryBound c.qAux := by
  have original := c.auxBound query (state.1.1, ∅)
  simpa only [sourceEnvironment, PqxdhPreparedPrefixCallbacks.auxiliaryLocal,
    PqxdhSourceAuxiliary.server, PqxdhSourceAuxiliary.lift, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using original

/-- The selected-message compiler pays the literal authenticated source certificate: preparation/application C, initializer 32, selector D and actual auxiliary A. It adds no hash, selected seal or opening request. -/
theorem bills (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (c : PqxdhAuthenticatedRootBudgets.Certificate (sourceEnvironment env callbacks) baseImpl kem program post)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (query : (PqxdhSelectedCallbackCompiler.External (SelectorSpec baseSpec)
      (IdentityHandle I) (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted)
      Response PqxdhPhase2DecapsulationRouting.Shared).Domain)
    (state : Local A (BareState 1) RootOracle.QueryCache) :
    let work := (PqxdhPreparedSelectedCallbacks.compiler attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret challenge
      selectedMessage previousRoot response callbacks (.inl query)).run state
    work.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 0 ∧
    work.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
      (PqxdhSelectedCallbackCompiler.cost
        (callbackCap (sourceEnvironment env callbacks) baseImpl kem program post c)
        (callbackCap (sourceEnvironment env callbacks) baseImpl kem program post c) 32
        (selectorCap (sourceEnvironment env callbacks) baseImpl kem program post c) c.qAux query) ∧
    work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  apply PqxdhSelectedCallbackCompiler.callback_bills
  · exact preparation (sourceEnvironment env callbacks) baseImpl kem attachedVerify primitives program post c secret challenge
  · exact application (sourceEnvironment env callbacks) baseImpl kem attachedVerify primitives program post c secret challenge
  · exact initial_local_uniform env.source selectedMessage previousRoot response
  · exact selector (sourceEnvironment env callbacks) baseImpl kem attachedVerify primitives program post c secret challenge
  · exact auxiliary env baseImpl kem program post callbacks c

end BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds.preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds.preparation

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds.application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds.application

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds.selector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds.selector

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds.auxiliary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds.auxiliary

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds.bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbackBounds.bills
