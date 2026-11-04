-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotIdeal
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSource
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource
/-! The original public produced/raw record event reaches the same ideal execution jointly extended by computed opaque slot receipts. Ordinary primitive reductions observe only the original public decision; labels enter solely in ideal analysis. Startup, one KEM comparison, one initialized recovery loss and ordered complete-prefix record reductions are unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
open RegistrationNativePlatformG3UniformRecordProgram (Sample sample after program)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_run)
open PqxdhRecordLiftCtxBills (effectBill worldBill)
variable (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform)
local notation "work" => program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous

variable (samplerCoins : Nat) (samplerBound : (sample setup budget selected).IsTotalQueryBound samplerCoins)
    (allowance : Fin 14 → PqxdhRecordLiftInterface.EffectKind → Nat)
    (framed : ∀ (parameters : Sample KemSK (budget.cap 4 + budget.cap 5)) credential,
      RegistrationNativeEntropyFrame.Frame (RegistrationNativePlatformSelectiveEntropyQuery.environment (n := budget.cap 4 + budget.cap 5) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source credential parameters.seed parameters.scalar parameters.candidate (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate) selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none)) 0 allowance)
    (reserveCoins : Nat) (reserveBounded : ∀ amount before, ((reserveFrame amount).run before).IsTotalQueryBound reserveCoins)
    (constructorCoins mlCoins : Nat)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)

variable (observe : Value × RegistrationNativeLedger.State →
    List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) → PqxdhRecordLiftWorld.RawCounters → Bool)
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)


noncomputable def joint := RegistrationNativePlatformRecordSlotIdeal.joint
  (fun _ => .random) setup codec route work

noncomputable def ideal : ProbComp Bool :=
  (fun result => RegistrationNativePlatformG3UniformOpaqueRecord.event source observe
    (RegistrationNativePlatformRecordSlotCursor.view (fun reached => reached.base.produced) result)) <$>
      joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous

/-- The original public ideal decision is exactly its projection from the genuine joint slot-ghost execution. Opaque labels do not enter the primitive reduction interface. -/
theorem ideal_source :
    RegistrationNativePlatformG3UniformRecordSource.ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe =
    ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe :=
  RegistrationNativePlatformRecordSlotIdeal.source (fun _ => .random) setup codec route work
    (RegistrationNativePlatformG3UniformOpaqueRecord.event source observe)

include bounded samplerBound framed reserveBounded constructorBound mlBound in
/-- The original public record event reaches the joint ideal analysis run with exactly the existing ordinary primitive and recovery loss. The extra ghost coordinate is observed only after that comparison. -/
theorem source_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal ((RegistrationNativePlatformG3UniformOpaqueSource.actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) representation budget previous).boolDistance
      (ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe)) ≤
      RegistrationNativePlatformG3UniformRecordSource.priorLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe +
        RegistrationNativePlatformG3UniformRecordCrypto.loss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous samplerCoins allowance reserveCoins constructorCoins mlCoins (RegistrationNativePlatformG3UniformOpaqueRecord.event source observe) setup.hmac fallback := by
  rw [← ideal_source]
  exact RegistrationNativePlatformG3UniformRecordSource.source_distance setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous
    samplerCoins samplerBound allowance framed reserveCoins reserveBounded constructorCoins mlCoins constructorBound mlBound observe
    representation correct functional candidate fallback
include bounded samplerBound framed reserveBounded constructorBound mlBound in
/-- Any original record event is bounded by the same ideal event plus the explicit initialized reduction loss. -/
theorem event_bound (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[RegistrationNativePlatformG3UniformOpaqueSource.actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) representation budget previous] {true} ≤
      𝒟[ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe] {true} +
        (RegistrationNativePlatformG3UniformRecordSource.priorLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe +
          RegistrationNativePlatformG3UniformRecordCrypto.loss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous samplerCoins allowance reserveCoins constructorCoins mlCoins (RegistrationNativePlatformG3UniformOpaqueRecord.event source observe) setup.hmac fallback) := by
  exact (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance _ _).trans
    (add_le_add le_rfl (source_distance setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous samplerCoins samplerBound allowance framed reserveCoins reserveBounded constructorCoins mlCoins constructorBound mlBound observe representation correct functional candidate fallback))

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison.ideal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison.ideal_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison.source_distance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison.event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison.event_bound
