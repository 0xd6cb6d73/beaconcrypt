-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup
import BeaconcryptCore.Computational.RegistrationNativeRecordCrypto

/-! The arbitrary-World record reductions are billed from actual selective native startup, original ledger query caps and the restricted native callback Frame. The shared startup ML-pin hash is charged once. No environment-start substitution or caller-supplied compiled-program bill is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec EffectKind)
open PqxdhRecordLiftBudget (WorldEffect WorldRecord recordBudget)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_add weighted_run operationBill)
open PqxdhRecordLiftCtxBills (effectBill worldBill)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveRecordStartup (program effectTotal)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def programBill (budget : PqxdhDeploymentInterface.Budget) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat) (kind : BudgetKind) : Nat :=
  effectBill kind .coin * effectTotal bounds budget allowance constructorCoins mlCoins .coin +
    effectBill kind .hash * effectTotal bounds budget allowance constructorCoins mlCoins .hash +
    effectBill kind .administrative * effectTotal bounds budget allowance constructorCoins mlCoins .administrative +
    operationBill kind .send * budget.sends + operationBill kind .raw * budget.receives

/-- The actual ML-pin startup contributes one shared hash, before the original public and record hashing bills. -/
theorem hash_bill (budget : PqxdhDeploymentInterface.Budget) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat) :
    programBill budget bounds allowance constructorCoins mlCoins .hash =
      1 + (budget.hash + (PqxdhRecordLiftInterface.Caps.mk budget 0).envTotal allowance .hash) + budget.sends + budget.receives := by
  simp [programBill, effectBill, effectTotal, RegistrationNativeSelectiveRecordStartup.startupCost,
    PqxdhRecordLiftBudget.directCost, operationBill, PqxdhRecordLiftCtxProgramBounds.lookupCost,
    PqxdhRecordLiftCtxProgramBounds.openingCost, PqxdhRecordLiftCtxProgramBounds.sealingCost]

theorem raw_bill (budget : PqxdhDeploymentInterface.Budget) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat) :
    programBill budget bounds allowance constructorCoins mlCoins .raw = budget.receives := by
  simp [programBill, effectBill, operationBill, PqxdhRecordLiftCtxProgramBounds.lookupCost,
    PqxdhRecordLiftCtxProgramBounds.openingCost, PqxdhRecordLiftCtxProgramBounds.sealingCost]

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (budget : PqxdhDeploymentInterface.Budget)
  (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))

include bounded in
/-- Packaging and the actual cursor filter retain the exact original record caps. -/
theorem record_bounded : PqxdhRecordLiftLaterWorlds.RecordBounded budget
    (RegistrationNativeRecordPackage.client (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary)) := by
  intro kind
  apply CborRecordWorldClient.client_bound
  simpa only [isQueryBoundP_map_iff] using RegistrationNativeSelectiveRecordStartup.program_record (n := n) setup checks wire source ensureInit
    identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary budget bounded kind

variable (allowance : Fin 14 → EffectKind → Nat)
  (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance)
  (constructorCoins mlCoins : Nat)
  (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
  (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)

include bounded framed constructorBound mlBound in
/-- Every CTX World category follows from the actual effect and record counts of the native full program. -/
theorem world_categories (kind : BudgetKind) :
    Weighted (worldBill kind)
      (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary)
      (programBill budget bounds allowance constructorCoins mlCoins kind) := by
  have effects := fun effect : EffectKind => weighted_indicator (WorldEffect effect) (effectBill kind effect) _ _
    (RegistrationNativeSelectiveRecordStartup.program_effect setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary budget bounded allowance framed constructorCoins mlCoins constructorBound mlBound effect)
  have records := fun record : PqxdhRecordLiftBudget.RecordKind => weighted_indicator (WorldRecord record) (operationBill kind record) _ _
    (RegistrationNativeSelectiveRecordStartup.program_record (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary budget bounded record)
  have together := weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _
    (weighted_add _ _ _ _ _ (effects .coin) (effects .hash)) (effects .administrative)) (records .send)) (records .raw)
  rw [PqxdhRecordLiftCtxBills.worldBill_split]
  simpa only [programBill, recordBudget] using together

include bounded framed constructorBound mlBound in
/-- The compiled actual native program has the derived bill in every CTX service category. -/
theorem program_categories (route : RawCtxServerRouting.SenderDecoder) (kind : BudgetKind) :
    Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule (RegistrationNativeWire.ledgerCodec wire).frameRead route
        (RegistrationNativeRecordPackage.client (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
          selectedOwner selectedAccept bounds mode adversary)) PqxdhRecordLiftProtocol.initialControl)
      (programBill budget bounds allowance constructorCoins mlCoins kind) := by
  apply weighted_run (worldBill kind) (categoryCost kind)
  · apply CborRawRecordLiftBounds.client_weighted
    simpa only [Weighted, isQueryBound_map_iff] using world_categories setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary budget bounded allowance framed constructorCoins mlCoins constructorBound mlBound kind
  · exact fun query control => PqxdhRecordLiftCtxBills.handler_categories kind (RegistrationNativeWire.ledgerCodec wire).frameRead route query control

def programCoins (budget : PqxdhDeploymentInterface.Budget) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat) : Nat :=
  programBill budget bounds allowance constructorCoins mlCoins .uniform + 64 * programBill budget bounds allowance constructorCoins mlCoins .hash

include bounded framed constructorBound mlBound in
/-- All chain observers inherit the actual native service-coin bill. -/
theorem chain_coins (route : RawCtxServerRouting.SenderDecoder) :
    Weighted PqxdhRecordLiftChainBills.coinCost
      (PqxdhRecordLiftProtocol.schedule (RegistrationNativeWire.ledgerCodec wire).frameRead route
        (RegistrationNativeRecordPackage.client (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
          selectedOwner selectedAccept bounds mode adversary)) PqxdhRecordLiftProtocol.initialControl)
      (programCoins budget bounds allowance constructorCoins mlCoins) := by
  have combined := weighted_add _ _ _ _ _
    (program_categories setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode
      adversary budget bounded allowance framed constructorCoins mlCoins constructorBound mlBound route .uniform)
    (PqxdhRecordLiftChainBills.weighted_scale _ 64 _ _
      (program_categories setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode
        adversary budget bounded allowance framed constructorCoins mlCoins constructorBound mlBound route .hash))
  exact PqxdhRecordLiftChainBills.weighted_cost_mono _ _ _ _ combined
    (fun query => (PqxdhRecordLiftChainBills.coinCost_categories query).le)

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.hash_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.hash_bill

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.raw_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.raw_bill

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.record_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.record_bounded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.world_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.world_categories

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.program_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.program_categories

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.chain_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills.chain_coins
