-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills
import BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEffectBounds
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup
/-! The complete genuine-startup/current-source World program has the same all-real and CTX record observations as its derived gated native reference, including the original ledger, produced frames, raw attempts, origin map and persistent platform state. The ordered chain, integrity and privacy bounds then use the actual reference bills rather than a whole-source security law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Secret Reader Response Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))




open PqxdhRecordLiftBudget (RecordKind WorldRecord recordBudget)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
variable (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)


local notation "sourceProgram" => RegistrationNativePlatformSelectiveEntropyStartup.program (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
local notation "referenceProgram" => RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary

/-- The complete actual source record view is preserved by the derived gated-native interpretation in the real chain world. -/
theorem real_transport (route : RawCtxServerRouting.SenderDecoder) :
    RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route sourceProgram =
      RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route referenceProgram := by
  rw [RegistrationNativeRecordViewCrypto.real_source,RegistrationNativeRecordViewCrypto.real_source]
  exact congrArg (Functor.map (fun result => RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) result.2.produced))
    (RegistrationNativePlatformSelectiveEntropyStartup.program_source setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
      (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source (fun _ => false)) setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)))
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route PqxdhRecordLiftProtocol.initialPrivate)

/-- Every CTX record hybrid retains that same original value, produced stage, raw attempts, origin map and shared platform state. -/
theorem ctx_transport (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode)
    (route : RawCtxServerRouting.SenderDecoder) :
    RegistrationNativeRecordPackage.ctx modes setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route sourceProgram =
      RegistrationNativeRecordPackage.ctx modes setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route referenceProgram := by
  rw [RegistrationNativeRecordPackage.ctx_source,RegistrationNativeRecordPackage.ctx_source]
  exact congrArg (Functor.map (fun result => RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) result.2.base.produced))
    (RegistrationNativePlatformSelectiveEntropyStartup.program_source setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
      (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)))
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route PqxdhRecordLiftIdeal.CtxPrivate.initial)
/-- The actual complete corrected source has the ordered chain, CTX integrity and privacy comparison, with all bills derived from its genuine startup and native callback frame. -/
theorem source_random_bound (route : RawCtxServerRouting.SenderDecoder)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (allowance : Fin 14 → PqxdhRecordLiftInterface.EffectKind → Nat)
    (framed : ∀ credential, RegistrationNativeEntropyFrame.Frame
      (RegistrationNativePlatformSelectiveEntropyQuery.environment (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none)) 0 allowance)
    (reserveCoins : Nat) (reserveBounded : ∀ amount before, ((reserveFrame amount).run before).IsTotalQueryBound reserveCoins)
    (constructorCoins mlCoins : Nat)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (observe : RegistrationNativeRecordPackage.View n (State n KemSK ProviderState Platform source) Value → Bool)
    (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal ((observe <$> RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route sourceProgram).boolDistance
      (observe <$> RegistrationNativeRecordPackage.ctx (fun _ => .random) setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route sourceProgram)) ≤
      RegistrationNativeRecordViewCrypto.chainLoss setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route referenceProgram budget observe hmac +
        RegistrationNativeRecordViewCrypto.authLoss setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route referenceProgram budget observe fallback
          (RegistrationNativePlatformSelectiveReferenceBills.programBill budget bounds allowance reserveCoins constructorCoins mlCoins .hash) (RegistrationNativePlatformSelectiveReferenceBills.programBill budget bounds allowance reserveCoins constructorCoins mlCoins .raw) +
        RegistrationNativeRecordViewCrypto.privacyLoss setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route referenceProgram budget observe := by
  rw [real_transport,ctx_transport]
  exact RegistrationNativeRecordViewCrypto.random_bound setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route referenceProgram budget observe
    (RegistrationNativePlatformSelectiveReferenceBills.record_bounded setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary budget bounded)
    (RegistrationNativePlatformSelectiveReferenceBills.programBill budget bounds allowance reserveCoins constructorCoins mlCoins)
    (fun kind => RegistrationNativePlatformSelectiveReferenceBills.program_categories setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary budget bounded allowance framed reserveCoins reserveBounded
      constructorCoins mlCoins constructorBound mlBound route kind)
    hmac correct fallback

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto.real_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto.real_transport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto.ctx_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto.ctx_transport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto.source_random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto.source_random_bound
