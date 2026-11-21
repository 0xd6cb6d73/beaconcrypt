-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordProgram
/-! The full warm reduction client retains the original record budgets and adds only its explicit independent sampler coins to the actual gated source bills. All possible public platform failures remain inside the same client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordBounds
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

include bounded in
/-- The complete sampler-plus-source client uses exactly the original send and raw-receive allowances. -/
theorem record_bounded : PqxdhRecordLiftLaterWorlds.RecordBounded budget (RegistrationNativeRecordPackage.client work) := by
  intro kind
  apply CborRecordWorldClient.client_bound
  simp only [isQueryBoundP_map_iff,program]
  apply RegistrationNativePlatformRecordPrefixBounds.record_bound
  intro parameters
  exact RegistrationNativePlatformSelectiveReferenceBounds.program_record setup checks wire source parameters.seed parameters.scalar parameters.candidate (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate) selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.materials) bounds mode adversary budget bounded kind

variable (samplerCoins : Nat) (samplerBound : (sample setup budget selected).IsTotalQueryBound samplerCoins)
    (allowance : Fin 14 → PqxdhRecordLiftInterface.EffectKind → Nat)
    (framed : ∀ (parameters : Sample KemSK (budget.cap 4 + budget.cap 5)) credential,
      RegistrationNativeEntropyFrame.Frame (RegistrationNativePlatformSelectiveEntropyQuery.environment (n := budget.cap 4 + budget.cap 5) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source credential parameters.seed parameters.scalar parameters.candidate (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate) selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none)) 0 allowance)
    (reserveCoins : Nat) (reserveBounded : ∀ amount before, ((reserveFrame amount).run before).IsTotalQueryBound reserveCoins)
    (constructorCoins mlCoins : Nat)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)

def bill (kind : BudgetKind) : Nat := effectBill kind .coin * samplerCoins +
  RegistrationNativePlatformSelectiveReferenceBills.programBill budget bounds allowance reserveCoins constructorCoins mlCoins kind

include bounded samplerBound framed reserveBounded constructorBound mlBound in
/-- Every CTX category has one whole-prefix bill, derived from the actual body and separate reduction sampler. -/
theorem program_categories (kind : BudgetKind) :
    Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)).frameRead route
        (RegistrationNativeRecordPackage.client work) PqxdhRecordLiftProtocol.initialControl)
      (bill bounds budget samplerCoins allowance reserveCoins constructorCoins mlCoins kind) := by
  have actual : Weighted (worldBill kind) work (bill bounds budget samplerCoins allowance reserveCoins constructorCoins mlCoins kind) := by
    unfold program bill
    apply weighted_bind (worldBill kind) _ _ _ _ (RegistrationNativePlatformRecordPrefixBounds.sample_bound _ samplerCoins samplerBound kind)
    intro parameters
    exact RegistrationNativePlatformSelectiveReferenceBills.world_categories setup checks wire source parameters.seed parameters.scalar parameters.candidate (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate) selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.materials) bounds mode adversary budget bounded allowance (framed parameters) reserveCoins reserveBounded constructorCoins mlCoins constructorBound mlBound kind
  apply weighted_run (worldBill kind) (categoryCost kind)
  · apply CborRawRecordLiftBounds.client_weighted
    simpa only [RegistrationNativeRecordPackage.client,Weighted,isQueryBound_map_iff] using actual
  · exact fun query control => PqxdhRecordLiftCtxBills.handler_categories kind (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)).frameRead route query control
end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordBounds.record_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordBounds.record_bounded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordBounds.program_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordBounds.program_categories
