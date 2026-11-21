-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution
import BeaconcryptCore.Computational.RegistrationNativeEntropyFrame
import BeaconcryptCore.Computational.RegistrationNativeLedgerCaps
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills

/-! Resource transport for the actual selective native interpreter. The restricted callback frame is the existing native entropy Frame, uniformly over actual ML credentials. Direct coins, shared hashes and all ongoing record branches retain their literal World routes. This frame supplies resource bounds only. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFrame
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects EffectKind effectKind effectLift)
open PqxdhRecordLiftBudget (WorldEffect nativeCost)
open RegistrationNativeSelectiveEntropyEnvironment (State environment)
open RegistrationNativeSelectiveEntropyNative (handler)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeLedgerCaps (coreKind)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
  (selectedOwner selectedAccept : Nat)

def Frame (allowance : Fin 14 → EffectKind → Nat) : Prop :=
  ∀ credential : RegistrationNativeMldsa.Credential source,
    RegistrationNativeEntropyFrame.Frame
      (environment (n := n) setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept (pure none))
      0 allowance

variable (allowance : Fin 14 → EffectKind → Nat)
  (framed : Frame (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance)

include framed in
theorem environment_bound (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeEntropyInterface.EnvQuery) (before : State n KemSK ProviderState source) (kind : EffectKind) :
    ((handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept (.inr query.val)).run before).IsQueryBoundP
      (WorldEffect kind) (allowance (RegistrationNativeInterface.queryClass (.inl (.inr query.val))) kind) := by
  rw [RegistrationNativeSelectiveEntropyNative.environment_source]
  apply ((framed credential).2 query before kind).simulateQ_of_step
  all_goals simp [effectLift, WorldEffect, isQueryBoundP_query_iff]

include framed in
/-- Every actual native command has its existing classwise restricted-effect bill, including absent physical Beacon handles. -/
theorem native_bound (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeInterface.Spec.Domain) (before : State n KemSK ProviderState source) (kind : EffectKind) :
    ((handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept query).run before).IsQueryBoundP
      (WorldEffect kind) (nativeCost allowance kind (coreKind query)) := by
  rcases query with coin | command
  · rw [RegistrationNativeSelectiveEntropyNative.coin_source]
    cases kind <;> simp [WorldEffect, PqxdhRecordLiftInterface.coinLift, nativeCost, coreKind,
      RegistrationNativeInterface.eraseCore, PqxdhDeploymentCompileBudget.commandKind, effectKind, isQueryBoundP_query_iff]
  · cases command with
    | create edPin mlPin keyId =>
        exact environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance framed credential
          ⟨.create edPin mlPin keyId, trivial⟩ before kind
    | bundle owner =>
        exact environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance framed credential
          ⟨.bundle owner, trivial⟩ before kind
    | accept raw =>
        exact environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance framed credential
          ⟨.accept raw, trivial⟩ before kind
    | build session payload =>
        exact environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance framed credential
          ⟨.build session payload, trivial⟩ before kind
    | finish owner raw =>
        exact environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance framed credential
          ⟨.finish owner raw, trivial⟩ before kind
    | hmac key bytes =>
        exact environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance framed credential
          ⟨.hmac key bytes, trivial⟩ before kind
    | hash bytes =>
        rw [RegistrationNativeSelectiveEntropyNative.hash_source]
        cases kind <;> simp [WorldEffect, effectLift, nativeCost, coreKind, RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind, effectKind, isQueryBoundP_query_iff]
    | serverSend keyId plaintext =>
        rw [RegistrationNativeSelectiveEntropyNative.server_send_source]
        simp [WorldEffect, nativeCost, coreKind, RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]
    | serverRaw raw =>
        rw [RegistrationNativeSelectiveEntropyNative.server_raw_source]
        simp [WorldEffect, nativeCost, coreKind, RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]
    | beaconSend index plaintext =>
        simp only [handler, RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query]
        change ((RegistrationNativeSelectiveEntropyEffects.close setup wire (RegistrationNativeMldsa.owned source credential)
          seed scalar candidate provider (RegistrationNativePublicFrontend.record (.inr (index, .inl plaintext)))).run before).IsQueryBoundP _ _
        cases found : before.1.beacons[index]? with
        | none => rw [RegistrationNativeSelectiveEntropyRecords.beacon_send_absent _ _ _ _ _ _ _ _ _ _ found]; trivial
        | some owner =>
            rw [RegistrationNativeSelectiveEntropyRecords.beacon_send_present _ _ _ _ _ _ _ _ _ _ _ found]
            simp [WorldEffect, nativeCost, coreKind, RegistrationNativeInterface.eraseCore,
              RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]
    | beaconRaw index raw =>
        simp only [handler, RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query]
        change ((RegistrationNativeSelectiveEntropyEffects.close setup wire (RegistrationNativeMldsa.owned source credential)
          seed scalar candidate provider (RegistrationNativePublicFrontend.record (.inr (index, .inr raw)))).run before).IsQueryBoundP _ _
        cases found : before.1.beacons[index]? with
        | none => rw [RegistrationNativeSelectiveEntropyRecords.beacon_raw_absent _ _ _ _ _ _ _ _ _ _ found]; trivial
        | some owner =>
            rw [RegistrationNativeSelectiveEntropyRecords.beacon_raw_present _ _ _ _ _ _ _ _ _ _ _ found]
            simp [WorldEffect, nativeCost, coreKind, RegistrationNativeInterface.eraseCore,
              RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]

include framed in
/-- The literal native full ledger keeps the original classwise budget, including original test and fresh-byte draws. -/
theorem wrapped_bound (credential : RegistrationNativeMldsa.Credential source)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (budget : PqxdhDeploymentInterface.Budget) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : State n KemSK ProviderState source) (kind : EffectKind) :
    ((simulateQ (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept)
      (RegistrationNativeLedger.wrap setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds
        (RegistrationNativeInterface.asModeO mode work))).run before).IsQueryBoundP (WorldEffect kind)
      (PqxdhRecordLiftBudget.directCost budget bounds kind + (PqxdhRecordLiftInterface.Caps.mk budget 0).envTotal allowance kind) := by
  exact (FinitePartitionQueryBounds.weighted_bound coreKind (nativeCost allowance kind)
    (fun core => ∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds core full * budget.cap full)
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept) (WorldEffect kind)
    (RegistrationNativeLedger.wrap setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds
      (RegistrationNativeInterface.asModeO mode work))
    (fun core => RegistrationNativeLedgerCaps.wrap_bound setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId bounds mode work budget bounded core)
    (fun query current => native_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance
      framed credential query current kind) before).mono (PqxdhRecordLiftBudget.cost_sum ⟨budget, 0⟩ bounds allowance kind)

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFrame.environment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFrame.environment_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFrame.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFrame.native_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFrame.wrapped_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFrame.wrapped_bound
