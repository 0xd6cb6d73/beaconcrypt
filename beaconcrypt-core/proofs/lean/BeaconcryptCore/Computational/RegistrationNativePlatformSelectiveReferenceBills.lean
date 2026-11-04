-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBounds
import BeaconcryptCore.Computational.RegistrationNativeRecordCrypto
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEffectBounds
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup
/-! The actual genuine startup and corrected gated reference body have explicit record and CTX service bills. These follow from the original source budget, literal startup prefix, native per-query frame and narrow public reserve receipt. The same cursor client and private platform state are retained through the ordered chain/integrity/privacy reductions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills
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


open PqxdhRecordLiftInterface (EffectKind)
open PqxdhRecordLiftBudget (WorldEffect)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_add weighted_run operationBill)
open PqxdhRecordLiftCtxBills (effectBill worldBill)

def effectTotal (budget : PqxdhDeploymentInterface.Budget) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (allowance : Fin 14 → EffectKind → Nat) (reserveCoins constructorCoins mlCoins : Nat) (kind : EffectKind) :=
  RegistrationNativeSelectiveRecordStartup.startupCost constructorCoins mlCoins kind +
    RegistrationNativePlatformGatedNativeEffectBounds.effectBudget budget bounds allowance reserveCoins kind

def programBill (budget : PqxdhDeploymentInterface.Budget) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (allowance : Fin 14 → EffectKind → Nat) (reserveCoins constructorCoins mlCoins : Nat) (kind : BudgetKind) : Nat :=
  effectBill kind .coin * effectTotal budget bounds allowance reserveCoins constructorCoins mlCoins .coin +
    effectBill kind .hash * effectTotal budget bounds allowance reserveCoins constructorCoins mlCoins .hash +
    effectBill kind .administrative * effectTotal budget bounds allowance reserveCoins constructorCoins mlCoins .administrative +
    operationBill kind .send * budget.sends + operationBill kind .raw * budget.receives

variable (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))

include bounded in
/-- The actual reference program retains the original joint record cap through both result packaging and cursor admission. -/
theorem record_bounded : PqxdhRecordLiftLaterWorlds.RecordBounded budget
    (RegistrationNativeRecordPackage.client (RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary)) := by
  intro kind
  apply CborRecordWorldClient.client_bound
  simpa only [isQueryBoundP_map_iff] using
    RegistrationNativePlatformSelectiveReferenceBounds.program_record setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary budget bounded kind

variable (allowance : Fin 14 → EffectKind → Nat)
    (framed : ∀ credential, RegistrationNativeEntropyFrame.Frame
      (RegistrationNativePlatformSelectiveEntropyQuery.environment (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none)) 0 allowance)
    (reserveCoins : Nat) (reserveBounded : ∀ amount before, ((reserveFrame amount).run before).IsTotalQueryBound reserveCoins)
    (constructorCoins mlCoins : Nat)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)

include bounded framed reserveBounded constructorBound mlBound in
/-- The actual startup and gated body have their complete derived CTX World bill, including separate public allocator coins. -/
theorem world_categories (kind : BudgetKind) :
    Weighted (worldBill kind)
      (RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary)
      (programBill budget bounds allowance reserveCoins constructorCoins mlCoins kind) := by
  have effects := fun effect : EffectKind => weighted_indicator (WorldEffect effect) (effectBill kind effect) _ _
    (RegistrationNativePlatformSelectiveReferenceBounds.program_effect setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary budget bounded allowance framed reserveCoins reserveBounded
      constructorCoins mlCoins constructorBound mlBound effect)
  have records := fun record : RecordKind => weighted_indicator (WorldRecord record) (operationBill kind record) _ _
    (RegistrationNativePlatformSelectiveReferenceBounds.program_record setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary budget bounded record)
  have together := weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _
    (weighted_add _ _ _ _ _ (effects .coin) (effects .hash)) (effects .administrative)) (records .send)) (records .raw)
  rw [PqxdhRecordLiftCtxBills.worldBill_split]
  simpa only [programBill,effectTotal,recordBudget] using together

include bounded framed reserveBounded constructorBound mlBound in
/-- The same literal client has its actual source-derived bill in every CTX service category. -/
theorem program_categories (route : RawCtxServerRouting.SenderDecoder) (kind : BudgetKind) :
    Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)).frameRead route
        (RegistrationNativeRecordPackage.client (RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary)) PqxdhRecordLiftProtocol.initialControl)
      (programBill budget bounds allowance reserveCoins constructorCoins mlCoins kind) := by
  apply weighted_run (worldBill kind) (categoryCost kind)
  · apply CborRawRecordLiftBounds.client_weighted
    simpa only [Weighted,isQueryBound_map_iff] using world_categories setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary budget bounded allowance framed reserveCoins reserveBounded
      constructorCoins mlCoins constructorBound mlBound kind
  · exact fun query control => PqxdhRecordLiftCtxBills.handler_categories kind
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)).frameRead route query control
end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills.record_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills.record_bounded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills.world_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills.world_categories

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills.program_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills.program_categories
