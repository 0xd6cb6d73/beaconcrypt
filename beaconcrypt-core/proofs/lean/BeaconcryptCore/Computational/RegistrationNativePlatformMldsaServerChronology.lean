-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames

/-! Actual response completion retains every chronological private attempt and its native unsigned-payload receipt through source first-record allocation, optional signature failure, dynamic writer failure and installation. Complete request alignment is derived from the actual source response hash controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerChronology
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaChronology (Aligned)
open RegistrationNativeMldsaRequestAlignment (SharedQuery)
open RegistrationNativePlatformMldsaPublicationChronology (Keeps pure_keeps bind_keeps closed)
open RegistrationNativePlatformMldsaTableProgram (runState)
open RegistrationNativePlatformMldsaProgram (M lift coins)
variable {n : Nat} {E Platform Value ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
variable (credential : RegistrationNativeMldsa.Credential (handleSource source))

def receipts (before : RegistrationServerRootCompiler.Local n) := before.world.2

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Actual Server outgoing callbacks preserve the exact same-position request/payload relation under arbitrary private replies and true counts. -/
theorem outgoing (query : RegistrationSigningShared.Spec.Domain) (correct : SharedQuery query) :
    Keeps (Platform := Platform) source (receipts (n := n)) (RegistrationNativePlatformMldsaServer.outgoing (handleSource source) credential query) := by
  intro before previous pool result aligned supported
  simp only [RegistrationNativePlatformMldsaServer.outgoing, RegistrationNativePlatformMldsaTableProgram.run_inject,
    RegistrationNativeMldsaTableProgram.runState, RegistrationNativeMldsaTableProgram.evaluate,
    StateT.run, simulateQ_map, map_apply, Functor.map_map, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact RegistrationNativeMldsaChronology.Server.outgoing source credential query correct before.world pool inner aligned called

private theorem encoder_keeps
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) :
    Keeps source (receipts (n := n)) (lift (RegistrationNativePlatformSourceBuild.encode writer view)) := by
  apply closed
  intro before previous result supported
  simp only [RegistrationNativePlatformSourceBuild.encode, StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact (congrArg (fun value => receipts value.1.2) same).symm

private theorem continue_keeps {Input Encoded : Type} (action : RustM Input)
    (next : Input → StateT (RegistrationServerRootCompiler.Local n) (M (handleSource source) Platform)
      (RustM (RegistrationWorldServerCompletion.Result Encoded)))
    (law : ∀ value, Keeps source (receipts (n := n)) (next value)) :
    Keeps source (receipts (n := n)) (RegistrationNativePlatformServerCompletion.continueWith action next) := by
  cases action with
  | ok value => exact law value
  | fail error | div => exact pure_keeps source (receipts (n := n)) _

private theorem result_keeps {Input Encoded : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT (RegistrationServerRootCompiler.Local n) (M (handleSource source) Platform)
      (RustM (RegistrationWorldServerCompletion.Result Encoded)))
    (law : ∀ value, Keeps source (receipts (n := n)) (next value)) :
    Keeps source (receipts (n := n)) (RegistrationNativePlatformServerCompletion.continueResult action next) := by
  cases action with
  | ok answer => cases answer with
    | Ok value => exact law value
    | Err previous => exact pure_keeps source (receipts (n := n)) _
  | fail error | div => exact pure_keeps source (receipts (n := n)) _

private theorem capability_keeps (query : PqxdhRecordLiftInterface.Capability n) :
    Keeps (Platform := Platform) source (receipts (n := n))
      (lift (RegistrationNativePlatformServerCompletion.capability coins query)) := by
  apply closed
  intro before previous result supported
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at actual
  obtain ⟨inner, _called, same⟩ := actual
  exact (congrArg (fun value => receipts value.2) same).symm

private theorem lift_bind {S A B : Type} (work : StateT S (StateT Platform ProbComp) A)
    (next : A → StateT S (StateT Platform ProbComp) B) :
    lift (source := handleSource source) (work >>= next) = (RegistrationNativePlatformMldsaProgram.lift (source := handleSource source) work >>= fun value => RegistrationNativePlatformMldsaProgram.lift (next value)) := by
  funext before previous
  simp only [RegistrationNativePlatformMldsaProgram.lift, RegistrationNativeMldsaProgram.liftState,
    RegistrationNativeMldsaProgram.lift, StateT.run_bind, simulateQ_bind]
  rfl

private theorem lift_pure {S A : Type} (value : A) :
    lift (source := handleSource source) (pure value : StateT S (StateT Platform ProbComp) A) = pure value := by
  funext before previous
  rfl

private theorem install_keeps (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse (alloc.vec.Vec U8)) :
    Keeps (Platform := Platform) source (receipts (n := n))
      (lift (RegistrationNativePlatformServerCompletion.installWith
        (RegistrationNativePlatformServerCompletion.capability coins) control published)) := by
  unfold RegistrationNativePlatformServerCompletion.installWith
  cases moved : peer.begin_peer_insert control published with
  | fail error | div => exact pure_keeps source (receipts (n := n)) _
  | ok answer => cases answer with
    | Err previous => exact pure_keeps source (receipts (n := n)) _
    | Ok pending =>
      dsimp only [RegistrationNativePlatformServerCompletion.continueResult]
      cases requested : pending.request with
      | fail error | div => exact pure_keeps source (receipts (n := n)) _
      | ok keyId =>
        dsimp only [RegistrationNativePlatformServerCompletion.continueWith]
        cases unpacked : pending.into_parts with
        | fail error | div => exact pure_keeps source (receipts (n := n)) _
        | ok parts =>
          dsimp only [RegistrationNativePlatformServerCompletion.continueWith]
          rw [lift_bind]
          exact bind_keeps source (receipts (n := n)) _ _ (capability_keeps source _) (fun _ => by
            rw [lift_pure]
            exact pure_keeps source (receipts (n := n)) _)

/-- The literal source hash/sign/write/install suffix retains both full histories on every outcome. -/
theorem afterRecord
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) :
    Keeps (Platform := Platform) source (receipts (n := n)) (RegistrationNativePlatformMldsaServer.afterRecord (handleSource source) credential writer control hashed) := by
  unfold RegistrationNativePlatformMldsaServer.afterRecord
  apply bind_keeps source (receipts (n := n)) _ _
    (RegistrationNativePlatformMldsaPublicationChronology.Server.program_keeps source (receipts (n := n)) _ _
      (outgoing source credential) (encoder_keeps source writer) hashed)
  intro published
  exact result_keeps source _ _ (install_keeps source control)

variable [primitive : AdapterSealPrimitive.Operations]

/-- Actual first-record source effects preserve existing logs; the reached response publication supplies the only new matching attempt/receipt append. -/
theorem finish (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Keeps (Platform := Platform) source (receipts (n := n))
      (RegistrationNativePlatformMldsaServer.finish (handleSource source) credential setup codec view failure allocation erased helper writer control initial) := by
  unfold RegistrationNativePlatformMldsaServer.finish
  apply bind_keeps source (receipts (n := n)) _ _ ?_
  · intro recorded
    exact result_keeps source _ _ (afterRecord source credential writer control)
  · apply closed
    intro before previous result supported
    exact (RegistrationNativePlatformSourceFrames.record_frame coins setup codec view failure allocation erased helper initial before previous result.1 result.2 supported).2

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerChronology.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerChronology.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerChronology.afterRecord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerChronology.afterRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerChronology.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerChronology.finish
