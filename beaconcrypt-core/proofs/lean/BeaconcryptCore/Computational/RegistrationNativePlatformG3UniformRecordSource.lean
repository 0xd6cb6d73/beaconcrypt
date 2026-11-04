-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordCrypto
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource
/-! The original initialized runtime produced/raw event reaches one all-random gated record client. The bound retains the original startup, one KEM shift, one initialized recovery client, and one complete-prefix client for each ordered record reduction. Primitive security remains expressed by its explicit advantages. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSource
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

noncomputable def priorLoss : ℝ≥0∞ :=
  ENNReal.ofReal (RegistrationNativePlatformG3UniformOpaqueSource.initialLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) budget selected previous +
    RegistrationNativePlatformG3UniformOpaqueSource.kemLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) budget selected previous) +
    RegistrationNativePlatformG3UniformOpaque.recoveryLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous

noncomputable def ideal : ProbComp Bool := (RegistrationNativePlatformG3UniformOpaqueRecord.event source observe) <$>
  RegistrationNativeRecordPackage.ctx (fun _ => .random) setup codec route work

include bounded samplerBound framed reserveBounded constructorBound mlBound in
/-- The complete original runtime record event has its initialized all-random comparison with derived reduction bills. -/
theorem source_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal ((RegistrationNativePlatformG3UniformOpaqueSource.actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) representation budget previous).boolDistance
      (ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe)) ≤
      priorLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe +
        RegistrationNativePlatformG3UniformRecordCrypto.loss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous samplerCoins allowance reserveCoins constructorCoins mlCoins (RegistrationNativePlatformG3UniformOpaqueRecord.event source observe) setup.hmac fallback := by
  have law := (RegistrationNativePlatformG3UniformOpaqueGame.game_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) budget selected previous).map Prod.fst
  have realLaw : RegistrationNativePlatformG3UniformOpaqueSource.hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) budget selected previous =ᵈ
      (RegistrationNativePlatformG3UniformOpaqueRecord.event source observe) <$> RegistrationNativeRecordViewCrypto.real setup codec route work := by
    simpa only [RegistrationNativePlatformG3UniformOpaqueSource.hidden,
      RegistrationNativePlatformG3UniformRecordProgram.real_source] using law
  have first := RegistrationNativePlatformG3UniformOpaqueSource.source_distance setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) representation correct functional budget bounded selected previous candidate
  have firstBound : ENNReal.ofReal ((RegistrationNativePlatformG3UniformOpaqueSource.actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) representation budget previous).boolDistance
      ((RegistrationNativePlatformG3UniformOpaqueRecord.event source observe) <$> RegistrationNativeRecordViewCrypto.real setup codec route work)) ≤ priorLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe := by
    simpa only [ProbComp.boolDistance,realLaw.evalDist_eq,priorLoss] using first
  have last := RegistrationNativePlatformG3UniformRecordCrypto.random_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous samplerCoins samplerBound allowance framed reserveCoins reserveBounded constructorCoins mlCoins constructorBound mlBound (RegistrationNativePlatformG3UniformOpaqueRecord.event source observe) setup.hmac correct fallback
  have triangle := ProbComp.boolDistance_triangle
    (RegistrationNativePlatformG3UniformOpaqueSource.actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) representation budget previous)
    ((RegistrationNativePlatformG3UniformOpaqueRecord.event source observe) <$> RegistrationNativeRecordViewCrypto.real setup codec route work)
    (ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe)
  exact (ENNReal.ofReal_le_ofReal triangle).trans
    ((ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).le.trans (add_le_add firstBound last))
include bounded samplerBound framed reserveBounded constructorBound mlBound in
/-- Any original record event is bounded by the same ideal event plus the explicit initialized reduction loss. -/
theorem event_bound (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[RegistrationNativePlatformG3UniformOpaqueSource.actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) representation budget previous] {true} ≤
      𝒟[ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe] {true} +
        (priorLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe +
          RegistrationNativePlatformG3UniformRecordCrypto.loss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous samplerCoins allowance reserveCoins constructorCoins mlCoins (RegistrationNativePlatformG3UniformOpaqueRecord.event source observe) setup.hmac fallback) := by
  exact (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance _ _).trans
    (add_le_add le_rfl (source_distance setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous samplerCoins samplerBound allowance framed reserveCoins reserveBounded constructorCoins mlCoins constructorBound mlBound observe representation correct functional candidate fallback))

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSource.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSource.source_distance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSource.event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSource.event_bound
