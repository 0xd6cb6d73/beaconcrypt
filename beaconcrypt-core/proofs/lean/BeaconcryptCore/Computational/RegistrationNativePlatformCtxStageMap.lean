-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService
import BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret
/-! Actual supplied-material record, publication and known installation stages commute with an arbitrary lawful monad interpretation. These structural laws expose the literal source continuation without changing kernels, failures or callback order. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageMap
variable {left right : Type → Type} [Monad left] [LawfulMonad left] [Monad right] [LawfulMonad right]
variable {Encoded : Type} {F : {X : Type} → left X → right X}
variable (hom : Cslib.IsMonadHom left right F)
include hom
variable (sealing : record_effects.AeadSealRequest → left (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
variable (hash : commitment.CommitmentTranscript → left RegistrationNativePlatformCommitment.HashReply)
variable (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
variable (sign : QueryImpl RegistrationSigningShared.Spec left)
variable (encode : registration.SignedResponseView → left (RustM (core.option.Option Encoded)))

omit [LawfulMonad left] [LawfulMonad right] in
private theorem continueRecord {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → left (RustM RegistrationServerRecordExecutor.Result)) :
    F (RegistrationNativePlatformServerRecord.continueResult action next) =
      RegistrationNativePlatformServerRecord.continueResult action (fun value => F (next value)) := by
  cases action with
  | fail error | div => exact hom.map_pure _
  | ok answer => cases answer with
    | Err prior => exact hom.map_pure _
    | Ok value => rfl

omit [LawfulMonad left] [LawfulMonad right] in
theorem record (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    F (RegistrationNativePlatformBoundPublication.record sealing hash write initial output) =
      RegistrationNativePlatformBoundPublication.record (fun query => F (sealing query))
        (fun query => F (hash query)) (fun query => F (write query)) initial output := by
  unfold RegistrationNativePlatformBoundPublication.record
  rw [continueRecord hom]
  congr 1
  funext pending
  exact RegistrationNativePlatformSourceRecord.fromAeadWithHash_map hom sealing hash write pending

omit [LawfulMonad left] [LawfulMonad right] in
private theorem after (completed : RustM RegistrationServerRecordExecutor.Result) :
    F (RegistrationNativePlatformBoundPublication.after sign encode completed) =
      RegistrationNativePlatformBoundPublication.after (fun query => F (sign query)) (fun view => F (encode view)) completed := by
  cases completed with
  | fail error | div => exact hom.map_pure _
  | ok answer => cases answer with
    | Err prior => exact hom.map_pure _
    | Ok pending => exact RegistrationNativePlatformBuildInterpret.Publication.program hom sign encode pending

omit [LawfulMonad left] [LawfulMonad right] in
theorem publication (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    F (RegistrationNativePlatformBoundPublication.program sealing hash write sign encode initial output) =
      RegistrationNativePlatformBoundPublication.program (fun query => F (sealing query))
        (fun query => F (hash query)) (fun query => F (write query))
        (fun query => F (sign query)) (fun view => F (encode view)) initial output := by
  unfold RegistrationNativePlatformBoundPublication.program
  rw [hom.map_bind, record hom]
  apply bind_congr
  intro completed
  exact after hom sign encode completed

omit sealing hash write sign encode in
private theorem program {I X : Type} {queries : OracleSpec I}
    (handler : QueryImpl queries left) (work : OracleComp queries X) :
    F (simulateQ handler work) = simulateQ (fun query => F (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using hom.map_pure value
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, hom.map_bind, ih]

theorem known {n : Nat} (effects : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) left)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) :
    F (RegistrationNativePlatformPairedServerService.knownStage sealing hash write sign encode effects control initial output) =
      RegistrationNativePlatformPairedServerService.knownStage (fun query => F (sealing query))
        (fun query => F (hash query)) (fun query => F (write query)) (fun query => F (sign query))
        (fun view => F (encode view)) (fun query => F (effects query)) control initial output := by
  unfold RegistrationNativePlatformPairedServerService.knownStage
  rw [hom.map_bind, publication hom]
  apply bind_congr
  intro published
  exact program hom effects _
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageMap.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageMap.record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageMap.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageMap.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageMap.known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageMap.known
