import BeaconcryptCore.Computational.PqxdhPreparedSelectedCallbacks
import BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler

/-!
Preparation, application, retained initialization, selector and publication callbacks are instantiated with their actual source implementations. The selected message key is absent from this compiler. Its KEM/private identity service and retained root cache stay in local reduction state, and every initializer preserves its original root/two-chain audit.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhPreparedSelectedInitialOwner
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

open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open PqxdhFullSecretInputKdf

noncomputable def owner (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes)
    (before : PqxdhSelectedInitialOwnerCompiler.Beacon (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K)) :=
  simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent target nonce next read)
    (PqxdhSelectedInitialOwnerCompiler.owner raw before)

noncomputable def sourceExternal := PqxdhSelectedInitialOwnerCompiler.sourceExternal pre application initial selector aux

/-- All concrete original source callbacks, including the retained root audit, appear in this complete native attempted-finish equation. No selected message key is supplied to the executable owner. -/
theorem source_owner (writer : RawCtxMixedShared.Writer) (prior : Prior) (parent : Option Entry)
    (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes)
    (before : PqxdhSelectedInitialOwnerCompiler.Beacon (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K))
    (state : Local A (BareState count) RootOracle.QueryCache × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result =>
      (Prod.map id (RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key)) result.1,
        RawCtxSelectedReceiveCompiler.project result.2)) <$>
      (PqxdhSelectedStateInterpreter.evaluate
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (owner attachedVerify primitives count source localImpl baseImpl kem secret challenge selectedMessage previousRoot response callbacks
          prior parent target nonce next read raw before)).run state =
      (PqxdhInitialGenericBeacon.owner
        (fun query => sourceExternal attachedVerify primitives count source localImpl baseImpl kem secret challenge selectedMessage previousRoot response callbacks (.inl query))
        (PqxdhSelectedMessageBeacon.nativeCalls source writer prior parent key target nonce next)
        (fun reply => sourceExternal attachedVerify primitives count source localImpl baseImpl kem secret challenge selectedMessage previousRoot response callbacks (.inr (.inl reply)))
        (fun secrets => sourceExternal attachedVerify primitives count source localImpl baseImpl kem secret challenge selectedMessage previousRoot response callbacks (.inr (.inr (.inl secrets)))) read raw
        (RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key) before)).run
          (RawCtxSelectedReceiveCompiler.project state) :=
  PqxdhSelectedInitialOwnerCompiler.compiled_owner pre application initial selector aux source writer prior parent key target nonce next read raw before state

/-- The native owner comparison uses the actual original audited source callbacks on the complete attached state, including every private/root effect and initializer candidate append. -/
theorem external_source (writer : RawCtxMixedShared.Writer) (stage S B : Nat)
    (query : (PqxdhSelectedCallbackCompiler.External (SelectorSpec baseSpec)
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K)
      (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared).Domain)
    (state : Local A (BareState count) RootOracle.QueryCache × CtxRomAuth.CtxRO.QueryCache) :
    (fun result => (result.1, attach result.2.1 result.2.2)) <$>
      (sourceExternal attachedVerify primitives count source localImpl baseImpl kem secret challenge selectedMessage previousRoot response callbacks query).run state =
      (PqxdhInitialNativeAudit.handler (S := S) (B := B) source writer stage
        (PqxdhInitialCurrentBeacon.preparation attachedVerify primitives count source localImpl baseImpl kem secret challenge)
        (PqxdhInitialCurrentBeacon.application attachedVerify primitives count source localImpl baseImpl kem secret challenge)
        (PqxdhInitialNativeInitializer.initial source selectedMessage previousRoot response)
        (PqxdhInitialPendingAmbient.selectorLift (PqxdhInitialPendingCurrent.selector attachedVerify primitives count baseImpl kem secret challenge))
        (fun request => PqxdhInitialBeaconAmbient.lift (PqxdhSourceAuxiliary.server callbacks request)) (.inr query)).run
          (attach state.1 state.2) := by
  have original := PqxdhSelectedInitialOwnerCompiler.external_native pre application initial selector aux
    source writer stage S B query state
  simpa only [sourceExternal, PqxdhPreparedPrefixCallbacks.preparation_source,
    PqxdhPreparedPrefixCallbacks.application_source, PqxdhNativeSharedPrefix.initial_source,
    PqxdhPreparedPrefixCallbacks.selector_source, PqxdhPreparedPrefixCallbacks.auxiliary_source] using original

end BeaconcryptCore.Computational.PqxdhPreparedSelectedInitialOwner

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSelectedInitialOwner.source_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSelectedInitialOwner.source_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSelectedInitialOwner.external_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSelectedInitialOwner.external_source
