-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView
/-! Every literal first-record/signing/publication source leaf ignores earlier raw ML receipt payloads. The complete supplied-pending completion retains all other state and the same persistent platform transition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
open RegistrationNativePlatformCtxRunner (M privateWork)
open RegistrationNativePlatformCtxReceiptView (Stable private_stable public_stable marker_stable records_stable pure_stable bind_stable program_stable)
variable {n : Nat} {I KemSK Reader Response Auxiliary Platform E A : Type} {base : OracleSpec I}
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

variable [primitive : AdapterSealPrimitive.Operations]

/-- Actual source AEAD uses the same request and primitive reply after erasing only the prior receipt log. -/
theorem aead_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8)) (nonce : primitive.Nonce) (key : primitive.Key) :
    Stable (privateWork (RegistrationNativePlatformCtxSeal.aead setup codec view failure plaintext associated nonce key) : M (State n Auxiliary) Platform _) := by
  apply private_stable
  have same := RegistrationNativePlatformViewStable.map_stable RegistrationNativePlatformIdentityReceiptView.view (fun _ => rfl)
    (RegistrationNativePlatformCtxLocal.record (n := n) (Auxiliary := Auxiliary) setup codec
      (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key))))
    (fun reply => (.ok (RegistrationNativePlatformSourceSeal.detached failure reply) : AdapterSealNative.NativeReply))
    (RegistrationNativePlatformIdentityReceiptView.record setup codec _)
  simpa only [RegistrationNativePlatformCtxSeal.aead, RegistrationNativePlatformViewStable.Stable,
    RegistrationNativePlatformIdentityReceiptView.Stable, StateT.run, state_map_apply,
    Functor.map_map, Prod.map_def, id_eq] using same

/-- Each literal allocation/AEAD leaf retains the full same projected native/platform state. -/
theorem seal_query_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (query : (AdapterSealNative.Spec E).Domain) :
    Stable (RegistrationNativePlatformCtxSeal.handler (n := n) (Auxiliary := Auxiliary) setup codec view failure allocation query) := by
  cases query with
  | reserve buffer capacity => exact public_stable _
  | aead plaintext associated nonce key => exact aead_stable setup codec view failure plaintext associated nonce key

/-- The actual seal controller, marker and every failure use no earlier raw receipt bytes. -/
theorem sealing_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (request : record_effects.AeadSealRequest) :
    Stable (RegistrationNativePlatformCtxSeal.sealing (n := n) (Auxiliary := Auxiliary) setup codec view failure allocation request) := by
  unfold RegistrationNativePlatformCtxSeal.sealing
  apply bind_stable
  · exact program_stable _ (seal_query_stable setup codec view failure allocation) _
  · intro result
    apply bind_stable
    · exact marker_stable (.seal request)
    · intro _
      exact pure_stable result

omit primitive in
/-- The exact mutable commitment hash retains its reply and erased transcript without reading old signing receipts. -/
theorem hash_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased transcript : commitment.CommitmentTranscript) :
    Stable (RegistrationNativePlatformCtxSeal.hash (n := n) (Auxiliary := Auxiliary) (Platform := Platform) setup codec erased transcript) := by
  unfold RegistrationNativePlatformCtxSeal.hash
  apply private_stable
  apply RegistrationNativePlatformViewStable.bind_stable
  · exact records_stable setup codec (.hash transcript)
  · intro reply
    exact RegistrationNativePlatformViewStable.pure_stable RegistrationNativePlatformIdentityReceiptView.view (fun _ => rfl) _

omit primitive in
/-- The source record writer reads only its literal public request and persistent platform state. -/
theorem write_stable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : record_effects.RecordWriteRequest) :
    Stable (RegistrationNativePlatformCtxWriters.write (n := n) (Auxiliary := Auxiliary) helper request) := by
  rintro ⟨before, previous⟩
  simp only [RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformCtxWriters.write,
    StateT.run, Functor.map_map, RegistrationNativePlatformCtxReceiptView.view,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]

omit primitive in
/-- Response encoding keeps exactly the same public platform effects and poststate. -/
theorem encode_stable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (current : registration.SignedResponseView) :
    Stable (RegistrationNativePlatformCtxWriters.encode (n := n) (Auxiliary := Auxiliary) writer current) :=
  public_stable _

theorem query_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformCtxCompletionProgram.Spec n).Domain) :
    Stable (RegistrationNativePlatformCtxCompletion.free setup codec view failure allocation erased sign helper writer query) := by
  cases query with
  | records query => exact private_stable _ (records_stable setup codec query)
  | «seal» query => exact sealing_stable setup codec view failure allocation query
  | hash query => exact hash_stable setup codec erased query
  | write query => exact write_stable helper query
  | signing query => exact private_stable _ (RegistrationNativePlatformIdentityReceiptView.outgoing sign query)
  | encode current => exact encode_stable writer current
  | effect query => exact private_stable _ (RegistrationNativePlatformIdentityReceiptView.effects query)

/-- The complete actual supplied-pending source completion has no prior-raw-receipt dependency, with every other World/cache/counter and P field retained. -/
theorem completion_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Stable (RegistrationNativePlatformCtxCompletion.completion (n := n) setup codec view failure allocation erased sign helper writer control pending) :=
  program_stable _ (query_stable setup codec view failure allocation erased sign helper writer) _
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.aead_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.aead_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.seal_query_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.seal_query_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.sealing_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.sealing_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.hash_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.hash_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.write_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.write_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.encode_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.encode_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.query_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.query_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.completion_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView.completion_stable
