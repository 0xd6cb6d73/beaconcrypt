-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupLedgerTails
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginRawBudget
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftBudget (RecordKind WorldRecord recordBudget)
variable {n : Nat} {I KemSK Platform Failure Reader Response Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (env : RegistrationNativeHiddenStartup.Started source → RegistrationNativeEntropyInterface.Environment n Platform)
    (reserve : RegistrationNativeHiddenStartup.Started source → Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : RegistrationNativeHiddenStartup.Started source → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (initial : RegistrationNativeHiddenStartup.Started source → Platform)
local notation "world" => RegistrationNativePlatformOriginStartupLedgerTails.world setup source ensureInit identityIndex serverKeyId identity env reserve codec bounds mode work initial

/-- The actual constructor/ML/pin-hash prefix contributes no record calls and every later born-dependent native client keeps its original record allowance. -/
theorem world_record (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀born,RegistrationNativeInterface.Respects budget (work born)) (kind : RecordKind) :
    (world).IsQueryBoundP (WorldRecord kind) (recordBudget budget kind) := by
  unfold RegistrationNativePlatformOriginStartupLedgerTails.world
  refine (isQueryBoundP_bind (m:=recordBudget budget kind)
    (RegistrationNativeSelectiveRecordStartup.start_record setup source ensureInit identityIndex serverKeyId identity kind) ?_).mono (by omega)
  intro born _
  cases born with
  | none=>trivial
  | some born=>
    exact RegistrationNativePlatformGatedNativeRecordBounds.program (env born) (reserve born) setup.source.crypto codec serverKeyId bounds mode budget
      (work born) (bounded born) born.created (initial born) kind

private theorem raw_bill : (PqxdhRecordLiftCtxBills.worldBill .raw : (PqxdhRecordLiftInterface.WorldSpec n).Domain → Nat)=
    fun query=>if WorldRecord .raw query then 1 else 0 := by
  funext query
  rcases query with created|(effect|record)
  · rfl
  · cases effect <;>rfl
  · rcases record with (send|raw)|⟨owner,plaintext|raw⟩ <;>rfl

/-- The whole actual initialized source, including all refused sends and the dynamic writer, has exactly its original raw-receive allowance; metadata and startup add no selected raw attempt. -/
theorem raw (route : RawCtxServerRouting.SenderDecoder) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀born,RegistrationNativeInterface.Respects budget (work born)) :
    (RegistrationNativeRecordOriginProgram.program codec route world).IsQueryBoundP
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) (recordBudget budget .raw) := by
  have original:=world_record setup source ensureInit identityIndex serverKeyId identity env reserve codec bounds mode work initial budget bounded .raw
  have cursor:=CborRecordWorldClient.client_bound (RegistrationNativeRecordPackage.encode <$>world) (WorldRecord .raw)
    (recordBudget budget .raw) ((isQueryBoundP_map_iff _ _ _).mpr original) CborRecordWorldClient.initial
  simp only [CborRecordWorldClient.client,isQueryBoundP_map_iff] at cursor
  have weight:=PqxdhRecordLiftCtxProgramBounds.weighted_indicator (WorldRecord .raw) 1 _ _ cursor
  simp only [Nat.one_mul] at weight
  rw [←raw_bill] at weight
  have compiled:=PqxdhRecordLiftCtxProgramBounds.weighted_run (PqxdhRecordLiftCtxBills.worldBill .raw)
    (PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw) (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    _ _ PqxdhRecordLiftProtocol.initialControl weight
    (fun query before=>PqxdhRecordLiftCtxBills.handler_categories .raw codec.frameRead route query before)
  apply PqxdhRecordFactsOriginRawBounds.raw_queries
  simpa only [RegistrationNativeRecordOriginProgram.program,RegistrationNativeRecordPackage.client,PqxdhRecordLiftProtocol.schedule,
    CborRecordWorldClient.client,simulateQ_map,StateT.run_map,PqxdhRecordLiftCtxProgramBounds.Weighted,isQueryBound_map_iff] using compiled
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginRawBudget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginRawBudget.world_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginRawBudget.world_record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginRawBudget.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginRawBudget.raw
