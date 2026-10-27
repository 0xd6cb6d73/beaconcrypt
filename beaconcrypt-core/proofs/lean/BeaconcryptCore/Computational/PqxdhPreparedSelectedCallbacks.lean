import BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler

/-!
Preparation, application, retained initialization, selector and publication callbacks are instantiated with their actual source implementations. The selected message key is absent from this compiler. Its KEM/private identity service and retained root cache stay in local reduction state, and every initializer preserves its original root/two-chain audit.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbacks
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSelectedCallbackCompiler
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhPhase2SourceAux PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhKemIndCca PqxdhPrivateKemSource PqxdhInitializerSecrecy
variable {ι I D K X Response A KemSK : Type} {baseSpec : OracleSpec ι}
variable (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)

local notation "pre" => PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives count source localImpl baseImpl kem secret challenge
local notation "application" => PqxdhPreparedPrefixCallbacks.application attachedVerify primitives count source localImpl baseImpl kem secret challenge
local notation "initial" => initialLocal (A := A) (N := BareState count) source selectedMessage previousRoot response
local notation "selector" => PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
  (PqxdhInitialPendingCurrent.selector attachedVerify primitives count baseImpl kem secret challenge)
local notation "aux" => PqxdhPreparedPrefixCallbacks.auxiliaryLocal (N := BareState count) (C := RootOracle.QueryCache) callbacks

noncomputable def compiler := PqxdhSelectedCallbackCompiler.lower pre application initial selector aux

/-- The concrete callback compiler retains the original source preparation, optional application result, root-cache initializer, private selector and actual auxiliary effects through the same CTX interpreter. -/
theorem source_step (writer : RawCtxMixedShared.Writer) (stage S B : Nat)
    (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder) (key : CtxRomAuth.CtxKey)
    (query : (PqxdhSelectedCallbackCompiler.External (SelectorSpec baseSpec)
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K)
      (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared).Domain)
    (state : Local A (BareState count) RootOracle.QueryCache) (before : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1.1, attach result.1.2 result.2.cache)) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode source.crypto key)
        ((compiler attachedVerify primitives count source localImpl baseImpl kem secret challenge selectedMessage previousRoot response callbacks
          (.inl query)).run state)).run before =
      (PqxdhInitialNativeAudit.handler (S := S) (B := B) source writer stage
        (PqxdhInitialCurrentBeacon.preparation attachedVerify primitives count source localImpl baseImpl kem secret challenge)
        (PqxdhInitialCurrentBeacon.application attachedVerify primitives count source localImpl baseImpl kem secret challenge)
        (PqxdhInitialNativeInitializer.initial source selectedMessage previousRoot response)
        (PqxdhInitialPendingAmbient.selectorLift (PqxdhInitialPendingCurrent.selector attachedVerify primitives count baseImpl kem secret challenge))
        (fun request => PqxdhInitialBeaconAmbient.lift (PqxdhSourceAuxiliary.server callbacks request)) (.inr query)).run
          (attach state before.cache) := by
  have original := PqxdhSelectedCallbackCompiler.callback_source pre application initial selector aux
    source writer stage S B real decode key query state before
  simpa only [compiler, PqxdhPreparedPrefixCallbacks.preparation_source,
    PqxdhPreparedPrefixCallbacks.application_source, PqxdhNativeSharedPrefix.initial_source,
    PqxdhPreparedPrefixCallbacks.selector_source, PqxdhPreparedPrefixCallbacks.auxiliary_source] using original

end BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbacks.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbacks.source_step
