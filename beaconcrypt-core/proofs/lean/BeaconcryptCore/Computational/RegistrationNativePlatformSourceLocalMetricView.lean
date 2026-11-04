-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionProgram
import BeaconcryptCore.Computational.RegistrationNativeSigningView
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService
/-! The literal source Local completion ignores only native-call, forwarding-coin and record-marker instrumentation. Allocation, raw serialization and signing remain shared effectful callbacks; true uniforms, cache and all protocol state stay in the comparison. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRecordWorldSource (project)
open RegistrationStateView (Stable pure_stable bind_stable program_stable)
variable {n : Nat} {I KemSK Reader Response A B E Auxiliary : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem closed (coins : QueryImpl unifSpec m)
    (work : StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp A) (stable : Stable project work) :
    Stable project (RegistrationNativePlatformServerCompletion.liftNative coins work) := by
  intro before
  have actual := congrArg (simulateQ coins) (stable before)
  simpa only [RegistrationNativePlatformServerCompletion.liftNative, StateT.run, simulateQ_map] using actual

private theorem external (work : m A) : Stable (project (n := n) (Auxiliary := Auxiliary)) (StateT.lift work) := by
  intro before
  simp only [StateT.run_lift, map_bind, map_pure, Prod.map_def, id_eq, RegistrationNativeLocalView.project_idempotent]

private theorem mapped (f : A → B) (work : StateT (RegistrationWorldAgreement.State n Auxiliary) m A)
    (stable : Stable project work) : Stable project (f <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact bind_stable _ _ _ stable (fun _ => pure_stable _ RegistrationNativeLocalView.project_idempotent _)

/-- Original Local primitive callbacks keep their real uniform draws and shared cache through the common monad. -/
theorem records (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) :
    Stable (project (n := n) (Auxiliary := Auxiliary))
      (RegistrationNativePlatformServerCompletion.records coins setup codec query) :=
  closed coins _ (RegistrationNativeLocalView.handler_input setup codec query)

private theorem marker (request : RegistrationWorldAgreement.RecordCall) :
    Stable (project (n := n) (Auxiliary := Auxiliary))
      (modify fun before : RegistrationWorldAgreement.State n Auxiliary =>
        {before with recordRequests := before.recordRequests ++ [request]} : StateT _ m Unit) := by
  intro before
  simp only [StateT.run_modify, map_pure, project, Prod.map_def, id_eq, RegistrationNativeWorldView.project_idempotent]

private theorem map_apply {S X Y : Type} (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

variable [primitive : AdapterSealPrimitive.Operations]

private theorem aead (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
    (nonce : primitive.Nonce) (key : primitive.Key) :
    Stable (project (n := n) (Auxiliary := Auxiliary))
      (RegistrationNativePlatformSourceSeal.aead coins setup codec view failure plaintext associated nonce key) := by
  have actual := mapped (n := n) (Auxiliary := Auxiliary) (fun reply : Option (Pqxdh.Bytes × Pqxdh.Bytes) =>
    (.ok (RegistrationNativePlatformSourceSeal.detached failure reply) : AdapterSealNative.NativeReply))
    _ (closed coins _ (RegistrationNativeLocalView.record_input setup codec
      (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key)))))
  intro before
  have compared := actual before
  simp only [map_apply, RegistrationNativePlatformSourceSeal.aead,
    RegistrationNativePlatformServerCompletion.liftNative, StateT.run, Functor.map_map, Prod.map_def, id_eq] at compared ⊢
  convert compared using 1 <;> rfl

/-- The actual source seal preserves every allocation outcome and actual detached AEAD call under the narrow instrumentation view. -/
theorem sealing (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m) (request : record_effects.AeadSealRequest) :
    Stable (project (n := n) (Auxiliary := Auxiliary))
      (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request) := by
  unfold RegistrationNativePlatformSourceSeal.sealing
  apply bind_stable _ _ _
  · apply program_stable _ RegistrationNativeLocalView.project_idempotent
    intro query
    cases query with
    | reserve before capacity => exact external _
    | aead plaintext associated nonce key => exact aead coins setup codec view failure plaintext associated nonce key
  · intro result
    apply bind_stable _ _ _ (marker _)
    intro changed
    exact pure_stable _ RegistrationNativeLocalView.project_idempotent result

omit primitive in
/-- The mutable source commitment reply retains its reached shared hash and literal returned transcript replacement. -/
theorem hash (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased transcript : commitment.CommitmentTranscript) :
    Stable (project (n := n) (Auxiliary := Auxiliary))
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript) := by
  unfold RegistrationNativePlatformSourceSeal.hash
  exact bind_stable _ _ _ (records coins setup codec _) (fun _ => pure_stable _ RegistrationNativeLocalView.project_idempotent _)


omit primitive in
private theorem write (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (request : record_effects.RecordWriteRequest) :
    Stable (project (n := n)) (RegistrationNativePlatformSourceBuild.write helper request) := by
  intro before
  simp only [RegistrationNativePlatformSourceBuild.write_run, Functor.map_map, project,
    Prod.map_def, id_eq, RegistrationNativeWorldView.project_idempotent]

omit primitive in
private theorem encode (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (view : registration.SignedResponseView) :
    Stable (project (n := n)) (RegistrationNativePlatformSourceBuild.encode writer view) := external _

omit primitive in
private theorem outgoing (coins : QueryImpl unifSpec m)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) :
    Stable (project (n := n) (Auxiliary := Auxiliary)) (RegistrationNativePlatformServerCompletion.outgoing coins sign query) := by
  apply closed
  intro before
  have compared := congrArg (fun action => (fun result => (result.1,
    {project before with world := result.2})) <$> action)
    (RegistrationNativeSigningView.outgoing_input sign query before.world)
  simpa only [RegistrationNativePlatformServerCompletion.nativeOutgoing, StateT.run, Functor.map_map,
    project, RegistrationNativeSigningView.project, Prod.map_def, id_eq, Function.comp_def] using compared

omit primitive in
private theorem capability (coins : QueryImpl unifSpec m) (query : PqxdhRecordLiftInterface.Capability n) :
    Stable (project (n := n) (Auxiliary := Auxiliary)) (RegistrationNativePlatformServerCompletion.capability coins query) :=
  closed coins _ (RegistrationNativeLocalView.capability_input query)

omit primitive in
private theorem effects (coins : QueryImpl unifSpec m) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Stable (project (n := n) (Auxiliary := Auxiliary))
      (RegistrationNativePlatformPairedServerService.nativeEffects coins query) := by
  apply closed
  intro before
  have actual := congrArg (fun action => (fun result => (result.1,
    {project before with world := (result.2, before.world.2)})) <$> action)
    (RegistrationNativeWorldViewEffects.effects_input query before.world.1)
  simpa only [RegistrationServerPublicationWorldCompiler.effect, StateT.run, Functor.map_map,
    project, Prod.map_def, id_eq, Function.comp_def] using actual

private noncomputable def implementation (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m) (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) :
    QueryImpl (RegistrationNativePlatformCtxCompletionProgram.Spec n) (StateT (RegistrationServerRootCompiler.Local n) m)
  | .records query => RegistrationNativePlatformServerCompletion.records coins setup codec query
  | .seal query => RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation query
  | .hash query => RegistrationNativePlatformSourceSeal.hash coins setup codec erased query
  | .write query => RegistrationNativePlatformSourceBuild.write helper query
  | .signing query => RegistrationNativePlatformServerCompletion.outgoing coins sign query
  | .encode view => RegistrationNativePlatformSourceBuild.encode writer view
  | .effect query => RegistrationNativePlatformPairedServerService.nativeEffects coins query

/-- The complete actual source first-record/publication/install body obeys the narrow view on every reached state and failure. -/
theorem finish (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m) (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Stable (project (n := n))
      (RegistrationNativePlatformSourceBuild.finishSource coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control pending) := by
  have body : simulateQ (implementation coins setup codec view failure allocation erased sign helper writer)
      (RegistrationNativePlatformCtxCompletionProgram.program (n := n) control pending) =
      RegistrationNativePlatformSourceBuild.finishSource coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control pending := by
    rw [RegistrationNativePlatformCtxCompletionProgram.interpret]
    rfl
  rw [← body]
  apply program_stable _ RegistrationNativeLocalView.project_idempotent
  intro query
  cases query with
  | records query => exact records coins setup codec query
  | «seal» query => exact sealing coins setup codec view failure allocation query
  | hash query => exact hash coins setup codec erased query
  | write query => exact write helper query
  | signing query => exact outgoing coins sign query
  | encode view => exact encode writer view
  | effect query => exact effects coins query

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView.records

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView.sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView.sealing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView.finish
