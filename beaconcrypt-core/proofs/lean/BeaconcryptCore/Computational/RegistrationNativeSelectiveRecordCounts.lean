-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFrame
import BeaconcryptCore.Computational.RegistrationNativeLedgerRecordBounds

/-! The actual selective native backend preserves the original joint send/raw budget. Restricted registration callbacks are record-free by type, and physical Beacon routing forwards at most one literal request. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec effectLift)
open PqxdhRecordLiftBudget (RecordKind WorldRecord NativeRecord recordBudget)
open RegistrationNativeLedgerRecordBounds (IsRecord)
open RegistrationNativeSelectiveEntropyEnvironment (State)
open RegistrationNativeSelectiveEntropyNative (handler)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
  (selectedOwner selectedAccept : Nat)

theorem environment_bound (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeEntropyInterface.EnvQuery) (before : State n KemSK ProviderState source) (kind : RecordKind) :
    ((handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept (.inr query.val)).run before).IsQueryBoundP
      (WorldRecord kind) 0 := by
  rw [RegistrationNativeSelectiveEntropyNative.environment_source]
  apply (isQueryBoundP_false _ 0).simulateQ_of_step
  all_goals simp [effectLift, WorldRecord, isQueryBoundP_query_iff]

/-- Native registration commands issue no ongoing record request; literal record commands forward at most one. -/
theorem native_bound (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeInterface.Spec.Domain) (before : State n KemSK ProviderState source) (kind : RecordKind) :
    ((handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept query).run before).IsQueryBoundP
      (WorldRecord kind) (if IsRecord kind query then 1 else 0) := by
  rcases query with coin | command
  · rw [RegistrationNativeSelectiveEntropyNative.coin_source]
    cases kind <;> simp [WorldRecord, IsRecord, NativeRecord, PqxdhRecordLiftInterface.coinLift,
      RegistrationNativeInterface.eraseCore, PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]
  · cases command with
    | create edPin mlPin keyId =>
        have free := environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept credential
          ⟨.create edPin mlPin keyId, trivial⟩ before kind
        cases kind <;> simpa [IsRecord, NativeRecord, RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind] using free
    | bundle owner =>
        have free := environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept credential
          ⟨.bundle owner, trivial⟩ before kind
        cases kind <;> simpa [IsRecord, NativeRecord, RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind] using free
    | accept raw =>
        have free := environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept credential
          ⟨.accept raw, trivial⟩ before kind
        cases kind <;> simpa [IsRecord, NativeRecord, RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind] using free
    | build session payload =>
        have free := environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept credential
          ⟨.build session payload, trivial⟩ before kind
        cases kind <;> simpa [IsRecord, NativeRecord, RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind] using free
    | finish owner raw =>
        have free := environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept credential
          ⟨.finish owner raw, trivial⟩ before kind
        cases kind <;> simpa [IsRecord, NativeRecord, RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind] using free
    | hmac key bytes =>
        have free := environment_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept credential
          ⟨.hmac key bytes, trivial⟩ before kind
        cases kind <;> simpa [IsRecord, NativeRecord, RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind] using free
    | hash bytes =>
        rw [RegistrationNativeSelectiveEntropyNative.hash_source]
        cases kind <;> simp [WorldRecord, IsRecord, NativeRecord, effectLift,  RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]
    | serverSend keyId plaintext =>
        rw [RegistrationNativeSelectiveEntropyNative.server_send_source]
        cases kind <;> simp [WorldRecord, IsRecord, NativeRecord, PqxdhRecordLiftBudget.recordKind,  RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]
    | serverRaw raw =>
        rw [RegistrationNativeSelectiveEntropyNative.server_raw_source]
        cases kind <;> simp [WorldRecord, IsRecord, NativeRecord, PqxdhRecordLiftBudget.recordKind,  RegistrationNativeInterface.eraseCore,
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
            cases kind <;> simp [WorldRecord, IsRecord, NativeRecord, PqxdhRecordLiftBudget.recordKind,  RegistrationNativeInterface.eraseCore,
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
            cases kind <;> simp [WorldRecord, IsRecord, NativeRecord, PqxdhRecordLiftBudget.recordKind,  RegistrationNativeInterface.eraseCore,
              RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]

/-- The complete actual native ledger retains the same joint send/raw caps after closing the concrete frontend and backend. -/
theorem wrapped_bound (credential : RegistrationNativeMldsa.Credential source)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (budget : PqxdhDeploymentInterface.Budget) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : State n KemSK ProviderState source) (kind : RecordKind) :
    ((simulateQ (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept)
      (RegistrationNativeLedger.wrap setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds
        (RegistrationNativeInterface.asModeO mode work))).run before).IsQueryBoundP (WorldRecord kind) (recordBudget budget kind) := by
  apply (RegistrationNativeLedgerRecordBounds.wrap_bound setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId bounds mode budget work bounded kind).simulateQ_run_of_step
  · intro query counted current
    simpa only [counted, ite_true] using native_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
      credential query current kind
  · intro query free current
    simpa only [free, ite_false] using native_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
      credential query current kind

/-- The original concrete native frontend run has the same bound before its result reassociation. -/
theorem run_bound (credential : RegistrationNativeMldsa.Credential source)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (budget : PqxdhDeploymentInterface.Budget) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (bounded : RegistrationNativeInterface.Respects budget work) (frontend : RegistrationNativePublicFrontend.State source)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (kind : RecordKind) :
    (RegistrationNativeSelectiveHiddenInterpreter.run setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
      serverKeyId bounds mode work frontend before).IsQueryBoundP (WorldRecord kind) (recordBudget budget kind) := by
  have counted := wrapped_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept credential serverKeyId
    bounds mode budget work bounded (frontend, before) kind
  rw [← RegistrationNativeSelectiveEntropyExecution.run_source, isQueryBoundP_map_iff] at counted
  exact counted

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts.environment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts.environment_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts.native_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts.wrapped_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts.wrapped_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts.run_bound
