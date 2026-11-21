-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedPathFacts
open RegistrationNativeStageTrace (Call Path Executed)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Spec FullSpec Handle FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response E Failure A : Type} {base : OracleSpec I}
variable (modes : Label n→KeyMode) (replace : Pqxdh.Bytes→Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat→StateT E ProbComp (core.result.Result Unit Failure))
local notation "Runtime"=>CborRawRecordFlat.NativeState n E
local notation "Whole"=>PqxdhDeploymentSecrecy.Ledger×Runtime
local notation "service"=>PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
local notation "native"=>RegistrationNativePlatformGatedRecordFlat.native service env reserve codec route
private theorem native_known (work : OracleComp Spec A) (before : Runtime) (handle : Handle)
    (known : PqxdhRecordLiftFlat.KnownAt before.1.2 handle) (result : A×Runtime)
    (supported : result∈support ((simulateQ native work).run before)) :
    PqxdhRecordLiftFlat.KnownAt result.2.1.2 handle := by
  rw [RegistrationNativePlatformGatedRecordFlat.native_program,support_map] at supported
  obtain ⟨inner,called,rfl⟩:=supported
  exact PqxdhRecordLiftFlat.support_keep_oracle (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    (fun control=>PqxdhRecordLiftFlat.KnownAt control handle) (PqxdhRecordLiftFlat.handler_known codec.frameRead route handle)
    _ before.1.2 known inner.1 (PqxdhRecordLiftFlat.support_run_fst service _ before.2 inner called)
variable (serverKeyId : U64) (bounds : FreshBounds)
local notation "full"=>RegistrationNativePlatformGatedRecordFlat.full service env reserve setup.source.crypto codec route serverKeyId bounds
/-- A supplied erased full source path preserves every already caller-known handle; reaching a hidden final handle cannot silently switch its earlier classification. -/
theorem known {before after : Whole} {calls : List (Call FullSpec Whole)} (actual : Path full before calls after)
    (handle : Handle) (prior : PqxdhRecordLiftFlat.KnownAt before.2.1.2 handle) :
    PqxdhRecordLiftFlat.KnownAt after.2.1.2 handle := by
  induction actual with
  | nil state=>exact prior
  | cons current called rest last following ih=>
    change (current.reply,current.after)∈support ((fun value=>(value.1.1,(value.1.2,value.2))) <$>
      (simulateQ native ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds current.query).run current.before.1)).run current.before.2) at called
    rw [support_map] at called
    obtain ⟨inner,reached,same⟩:=called
    have advanced:=native_known modes replace setup codec route env reserve _ current.before.2 handle prior inner reached
    apply ih
    have equalControl:=congrArg (fun value : FullSpec.Range current.query×Whole=>value.2.2.1.2) same
    rw [←equalControl]
    exact advanced
private theorem native_seal (ideal : ∀label,modes label≠.real) (work : OracleComp Spec A) (before : Runtime)
    (label : Label n) (entry : CtxRomAuth.CtxSuccessfulSeal) (member : entry∈(before.2.keys label).1.successfulSeals)
    (result : A×Runtime) (supported : result∈support ((simulateQ native work).run before)) :
    entry∈(result.2.2.keys label).1.successfulSeals := by
  rw [RegistrationNativePlatformGatedRecordFlat.native_program,support_map] at supported
  obtain ⟨inner,called,rfl⟩:=supported
  exact PqxdhRecordLiftFlat.support_keep_oracle service (fun secret=>entry∈(secret.keys label).1.successfulSeals)
    (fun query state prior result reached=>PqxdhRecordFactsOriginSealFacts.erased_service_mono modes ideal replace setup codec query state result reached label entry prior)
    _ before.2 member inner called
/-- The same actual erased full source future retains a concrete already-generated seal through every failed or successful callback. -/
theorem seals (ideal : ∀label,modes label≠.real) {before after : Whole} {calls : List (Call FullSpec Whole)}
    (actual : Path full before calls after) (label : Label n) (entry : CtxRomAuth.CtxSuccessfulSeal)
    (member : entry∈(before.2.2.keys label).1.successfulSeals) : entry∈(after.2.2.keys label).1.successfulSeals := by
  induction actual with
  | nil state=>exact member
  | cons current called rest last following ih=>
    change (current.reply,current.after)∈support ((fun value=>(value.1.1,(value.1.2,value.2))) <$>
      (simulateQ native ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds current.query).run current.before.1)).run current.before.2) at called
    rw [support_map] at called
    obtain ⟨inner,reached,same⟩:=called
    have advanced:=native_seal modes replace setup codec route env reserve ideal _ current.before.2 label entry member inner reached
    apply ih
    have equalPrivate:=congrArg (fun value : FullSpec.Range current.query×Whole=>value.2.2.2) same
    rw [←equalPrivate]
    exact advanced
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedPathFacts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedPathFacts.known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedPathFacts.known
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedPathFacts.seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedPathFacts.seals
