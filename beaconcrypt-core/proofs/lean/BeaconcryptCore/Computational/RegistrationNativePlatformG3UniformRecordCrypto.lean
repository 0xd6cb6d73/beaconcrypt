-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordBounds
/-! One complete warm-prefix client consumes the ordered chain, integrity and privacy reductions. Each advantage names that complete client and its derived resource bill; conditional absolute advantages are not substituted for a single reduction. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordCrypto
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

variable (observe : RegistrationNativeRecordPackage.View (budget.cap 4 + budget.cap 5)
    (RegistrationNativePlatformSelectiveEntropyEnvironment.State (budget.cap 4 + budget.cap 5) KemSK RegistrationNativeKemSwitchSource.Phase Platform source) Value → Bool)
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)

noncomputable def loss (hmac : PqxdhSecretInputKdf.HmacSha512) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) : ℝ≥0∞ :=
  RegistrationNativeRecordViewCrypto.chainLoss setup codec route work budget observe hmac +
    RegistrationNativeRecordViewCrypto.authLoss setup codec route work budget observe fallback
      (RegistrationNativePlatformG3UniformRecordBounds.bill bounds budget samplerCoins allowance reserveCoins constructorCoins mlCoins .hash)
      (RegistrationNativePlatformG3UniformRecordBounds.bill bounds budget samplerCoins allowance reserveCoins constructorCoins mlCoins .raw) +
    RegistrationNativeRecordViewCrypto.privacyLoss setup codec route work budget observe

include bounded samplerBound framed reserveBounded constructorBound mlBound in
/-- Whole-prefix source bills give coefficient one for each ordered record reduction. -/
theorem random_bound (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal ((observe <$> RegistrationNativeRecordViewCrypto.real setup codec route work).boolDistance
      (observe <$> RegistrationNativeRecordPackage.ctx (fun _ => .random) setup codec route work)) ≤
      loss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous samplerCoins allowance reserveCoins constructorCoins mlCoins observe hmac fallback := by
  exact RegistrationNativeRecordViewCrypto.random_bound setup codec route work budget observe
    (RegistrationNativePlatformG3UniformRecordBounds.record_bounded setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous)
    (RegistrationNativePlatformG3UniformRecordBounds.bill bounds budget samplerCoins allowance reserveCoins constructorCoins mlCoins)
    (RegistrationNativePlatformG3UniformRecordBounds.program_categories setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous samplerCoins samplerBound allowance framed reserveCoins reserveBounded constructorCoins mlCoins constructorBound mlBound)
    hmac correct fallback
end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordCrypto

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordCrypto.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordCrypto.random_bound
