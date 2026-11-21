-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic
/-! The complete actual source first-record computation has a private two-KDF prefix and a suffix with a fixed placeholder advanced kernel. The real generated whole kernel is retained only by the private interpretation and restored in a successful result. The source KDF requests and complete common poststates stay literal; no KDF output or whole-source law is supplied as a premise. Root-bearing earlier session references remain a separate private frontend component. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordSplit
variable {m : Type → Type} [Monad m] [LawfulMonad m]

private noncomputable def placeholder : ConcreteRatchetKernel := PqxdhRecordLiftWorld.kernel .server
  (RegistrationBoundKeySchedule.zero, RegistrationBoundKeySchedule.zero)

noncomputable def erased (stage : RustM (core.result.Result registration.ServerRecordAead pqxdh.ServerState)) :
    RustM (core.result.Result registration.ServerRecordAead pqxdh.ServerState) :=
  RegistrationPublicationKernelErasure.mapOk (RegistrationKernelErasure.selected placeholder) <$> stage

def restore (stage : RustM (core.result.Result registration.ServerRecordAead pqxdh.ServerState))
    (result : RustM RegistrationServerRecordExecutor.Result) : RustM RegistrationServerRecordExecutor.Result :=
  match stage with
  | .ok (.Ok pending) => RegistrationKernelErasure.mapResult pending.pending.seal.advanced result
  | _ => result

private theorem rust_map_fail {A B : Type} (f : A → B) (error : Error) :
    f <$> (RustM.fail error : RustM A) = RustM.fail error := rfl

private theorem rust_map_div {A B : Type} (f : A → B) :
    f <$> (RustM.div : RustM A) = RustM.div := rfl

private theorem selected_restore (pending : registration.ServerRecordAead) :
    RegistrationKernelErasure.selected pending.pending.seal.advanced (RegistrationKernelErasure.selected placeholder pending) = pending := rfl

/-- Erasing the retained advanced kernel changes no actual source seal/hash/write effect or failure, before the private interpretation restores that kernel. -/
theorem suffix
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (stage : RustM (core.result.Result registration.ServerRecordAead pqxdh.ServerState)) :
    RegistrationNativePlatformServerRecord.continueResult stage (RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write) =
      restore stage <$> RegistrationNativePlatformServerRecord.continueResult (erased stage)
        (RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write) := by
  cases stage with
  | fail error => simp only [erased, rust_map_fail, RegistrationNativePlatformServerRecord.continueResult, map_pure]; rfl
  | div => simp only [erased, rust_map_div, RegistrationNativePlatformServerRecord.continueResult, map_pure]; rfl
  | ok answer => cases answer with
    | Err previous =>
      simp only [erased, RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk,
        RegistrationNativePlatformServerRecord.continueResult, map_pure]
      rfl
    | Ok pending =>
      change RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write pending =
        RegistrationKernelErasure.mapResult pending.pending.seal.advanced <$>
          RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write (RegistrationKernelErasure.selected placeholder pending)
      have same := RegistrationNativePlatformSeedPublic.fromAead pending.pending.seal.advanced sealing hash write
        (RegistrationKernelErasure.selected placeholder pending)
      rw [selected_restore] at same
      exact same

/-- The entire actual source initial/ratchet-KDF and first-record path factors through a private prefix without exposing its generated whole kernel to the public suffix. -/
theorem source (record : QueryImpl RegistrationRecordPrimitives.Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (initial : registration.ServerInitialKdf) :
    RegistrationNativePlatformSourceRecord.fromInitialWithHash record sealing hash write initial = (do
      let stage ← RegistrationNativePlatformPrivateRecordPrefix.privatePrefix record initial
      restore stage <$> RegistrationNativePlatformServerRecord.continueResult (erased stage)
        (RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write)) := by
  rw [RegistrationNativePlatformPrivateRecordPrefix.source]
  apply bind_congr
  intro stage
  exact suffix sealing hash write stage

end BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordSplit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordSplit.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordSplit.suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordSplit.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordSplit.source
