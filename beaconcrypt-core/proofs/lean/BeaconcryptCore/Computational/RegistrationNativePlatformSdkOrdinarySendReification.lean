-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification
/-! Actual source send callback programs commute with administrative-bill erasure. Primitive replies, source Rust outcomes, writer receipts and common platform state remain exact. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySendReification
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinaryDriver (State M)
open RegistrationNativePlatformSdkOrdinaryReification (journal)
variable {Platform E I KemSK Reader Response A B : Type} {base : OracleSpec I}

def Compatible (work : M Platform A) : Prop :=
  ∀before,Prod.map id journal <$>work.run before=work.run (journal before)

private theorem pure_compatible (value : A) : Compatible (pure value : M Platform A) := by
  intro before
  simp only [StateT.run_pure,map_pure]
  rfl

private theorem bind_compatible (work : M Platform A) (next : A →M Platform B)
    (first : Compatible work) (rest : ∀value,Compatible (next value)) : Compatible (work >>=next) := by
  intro before
  rw [StateT.run_bind,StateT.run_bind,map_bind,←first before,bind_map_left]
  apply bind_congr
  intro result
  exact rest result.1 result.2

private theorem map_compatible (observe : A →B) (work : M Platform A) (law : Compatible work) :
    Compatible (observe <$>work) := by
  intro before
  rw [StateT.run_map,StateT.run_map,←law before,Functor.map_map,Functor.map_map]
  rfl

private theorem program_compatible {J : Type} {spec : OracleSpec J}
    (implementation : QueryImpl spec (M Platform)) (laws : ∀query,Compatible (implementation query))
    (work : OracleComp spec A) : Compatible (simulateQ implementation work) := by
  intro before
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq implementation implementation journal laws work before

private theorem native_compatible (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (query : RawCtxMixedOwner.NativeSpec.Domain) :
    Compatible (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve query) := by
  intro before
  funext previous
  change (Prod.map id journal <$> (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve query).run before).run previous=_
  rw [StateT.run_map]
  exact RegistrationNativePlatformSdkOrdinaryReification.journal_query setup codec reserve query before previous

private theorem reserve_compatible (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E)) (size : Nat) :
    Compatible (RegistrationNativePlatformOrdinarySourceJournal.reserveNative reserve size) := by
  intro before
  change Prod.map id journal <$>
      (StateT.lift (reserve size) : M Platform _).run before=
    (StateT.lift (reserve size) : M Platform _).run (journal before)
  simp only [StateT.run_lift,bind_pure_comp,Functor.map_map]
  rfl

private theorem receipt_compatible (frame : RawCtxReceive.DecodedFrame) :
    Compatible (RegistrationNativePlatformOrdinarySourceJournal.receipt (Platform:=Platform) frame) := by
  intro before
  change Prod.map id journal <$>pure ((),(RegistrationNativePlatformOrdinaryWorld.chargeWriter before.1,before.2++[frame]))=
    pure ((),(RegistrationNativePlatformOrdinaryWorld.chargeWriter (journal before).1,(journal before).2++[frame]))
  simp only [map_pure,journal,RegistrationNativePlatformSdkOrdinaryReification.primitive,
    RegistrationNativePlatformOrdinaryWorld.chargeWriter]
  rfl

variable (setup : Setup base KemSK) (codec : Codec Reader Response)
variable (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))

private theorem kdf_compatible (request : ratchet.SymmetricRatchetKdfRequest) :
    Compatible (RegistrationNativePlatformOrdinarySourceJournal.kdf setup codec reserve request) :=
  native_compatible setup codec reserve (.inl request)

private theorem aead_compatible (input : RawCtxSourceSeal.AeadInput) :
    Compatible (RegistrationNativePlatformOrdinarySourceJournal.aead setup codec reserve input) := by
  apply map_compatible
  simpa only [RegistrationNativePlatformOrdinarySourceJournal.implementation,QueryImpl.apply_compose,
    RegistrationNativePlatformOrdinaryWorldSeal.inject,simulateQ_spec_query] using
    native_compatible setup codec reserve (.inr (.inl input))

private theorem hash_compatible (bytes : Pqxdh.Bytes) :
    Compatible (RegistrationNativePlatformOrdinarySourceJournal.hash setup codec reserve bytes) := by
  apply map_compatible
  simpa only [RegistrationNativePlatformOrdinarySourceJournal.implementation,QueryImpl.apply_compose,
    RegistrationNativePlatformOrdinaryWorldSeal.inject,simulateQ_spec_query] using
    native_compatible setup codec reserve (.inr (.inr (.inr (.inl bytes))))

variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)

omit [FrameDispatchFallback.Operations] in
private theorem seal_query_compatible (query : (AdapterSealNative.Spec E).Domain) :
    Compatible (RegistrationNativePlatformOrdinarySourceNative.sealHandler view failure
      (RegistrationNativePlatformOrdinarySourceJournal.reserveNative reserve)
      (RegistrationNativePlatformOrdinarySourceJournal.aead setup codec reserve) query) := by
  cases query with
  | reserve before capacity => exact map_compatible _ _ (reserve_compatible reserve capacity.val)
  | aead plaintext associated nonce key =>
      exact map_compatible _ _ (aead_compatible setup codec reserve _)

omit primitives in
private theorem helper_query_compatible (query : (AdapterRecordHelperRequestMonad.Spec E).Domain) :
    Compatible (AdapterRecordRawBytes.helper
      (fun _ size =>.ok <$>RegistrationNativePlatformOrdinarySourceJournal.reserveNative reserve size.val)
      (AdapterRecordFrameBytes.serializer (m:=M Platform)) query) := by
  cases query with
  | reserve before capacity => exact map_compatible _ _ (map_compatible _ _ (reserve_compatible reserve capacity.val))
  | encodeFrame sequence sender parts output => exact pure_compatible _

omit primitives in
private theorem writing_compatible (request : record_effects.RecordWriteRequest) :
    Compatible (RegistrationNativePlatformOrdinarySourceReceipt.writing
      (RegistrationNativePlatformOrdinarySourceJournal.reserveNative reserve) request
      RegistrationNativePlatformOrdinarySourceJournal.receipt) := by
  unfold RegistrationNativePlatformOrdinarySourceReceipt.writing
    RegistrationNativePlatformOrdinarySourceNative.writing RegistrationNativePlatformOrdinarySourceNative.afterAttempt
  apply bind_compatible
  · exact program_compatible _ (helper_query_compatible reserve) _
  · intro written
    apply bind_compatible
    · cases RegistrationNativePlatformOrdinarySourceReceipt.frameOfRequest request with
      | none => exact pure_compatible _
      | some frame => exact receipt_compatible frame
    · intro _receipt
      exact pure_compatible _

theorem callbacks (erased : commitment.CommitmentTranscript) (query : AdapterRecordSendRequestMonad.Spec.Domain) :
    Compatible (RegistrationNativePlatformExtractedSdkOrdinaryDriver.callbacks setup codec reserve view failure erased query) := by
  cases query with
  | kdf request => exact map_compatible _ _ (kdf_compatible setup codec reserve request)
  | sealing request => exact program_compatible _ (seal_query_compatible setup codec reserve view failure) _
  | hash transcript => exact map_compatible _ _ (hash_compatible setup codec reserve _)
  | writer request => exact writing_compatible reserve request

theorem program (erased : commitment.CommitmentTranscript) (work : OracleComp AdapterRecordSendRequestMonad.Spec A) :
    Compatible (simulateQ (RegistrationNativePlatformExtractedSdkOrdinaryDriver.callbacks setup codec reserve view failure erased) work) :=
  program_compatible _ (callbacks setup codec reserve view failure erased) work

theorem send (erased : commitment.CommitmentTranscript) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (context : record_effects.SealFrameContext) :
    Compatible (RegistrationNativePlatformExtractedSdkOrdinaryDriver.send setup codec reserve view failure erased kernel context) := by
  unfold RegistrationNativePlatformExtractedSdkOrdinaryDriver.send
  rw [←AdapterRecordStatefulSend.interpreted]
  exact program setup codec reserve view failure erased _

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySendReification
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySendReification.callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySendReification.callbacks
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySendReification.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySendReification.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySendReification.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySendReification.send
