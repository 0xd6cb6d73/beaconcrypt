-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBeaconChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBuildChronology
import BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation

/-! The actual corrected adaptive handler retains same-position private complete-request attempts and native unsigned-payload receipts. Creation counts and failure prefixes, stateful source Init writing, source first-record allocation and corrected finish remain in the same run. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaRunChronology
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaChronology (Aligned)
open RegistrationNativePlatformMldsaPublicationChronology (Keeps pure_keeps bind_keeps closed)
open RegistrationNativePlatformMldsaProgram (M inject coins)
open RegistrationNativePlatformMldsaTableProgram (runState)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

def receipts (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) := before.server.world.world.2

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Keeps (Platform := Platform) source (receipts (n := n) (KemSK := KemSK) source)
      (inject (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId)) := by
  intro before previous pool result aligned supported
  rw [RegistrationNativePlatformMldsaTableProgram.run_inject, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact RegistrationNativeMldsaRunChronology.create source setup checks representation created edPin mlPin keyId before pool inner aligned called

private theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) Value)
    (law : Keeps source RegistrationNativePlatformMldsaSdkPrefixChronology.receipts work) :
    Keeps source (receipts (KemSK := KemSK) source) (RegistrationNativePlatformExperiment.server work) := by
  intro before previous pool result aligned supported
  simp only [runState, RegistrationNativePlatformExperiment.server, StateT.run, map_apply,
    RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact law before.server previous pool inner aligned called

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential (handleSource source))
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformMldsaProfile.handler (n := n) setup checks wire route representation created credential
  view failure allocation reserveRegistration reservePeer erased helper writer

/-- Every complete actual corrected typed callback retains positionwise raw signing attempts and native unsigned-payload receipts, with no history-validity or source-security premise. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Keeps source (receipts (n := n) (KemSK := KemSK) source) (callback query) := by
  have ordinary (allowed : RegistrationNativeMldsaReceiptPreservation.NonSigning query) :
      Keeps source (receipts (n := n) (KemSK := KemSK) source) (callback query) := by
    intro before previous pool result aligned supported
    obtain ⟨samePool, sameReceipts⟩ := RegistrationNativePlatformReceiptPreservation.handler source setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer erased helper writer query allowed before previous pool result supported
    change Aligned result.2.signing (RegistrationNativeMldsaReceiptPreservation.receipts result.1.1.2)
    rw [samePool, sameReceipts]
    exact aligned
  cases query with
  | inl coin => exact ordinary trivial
  | inr command => cases command with
    | create edPin mlPin keyId => exact create source setup checks representation created edPin mlPin keyId
    | bundle index => exact RegistrationNativePlatformMldsaBeaconChronology.sourceBundle source setup checks representation created writer index
    | build index application =>
      simp only [RegistrationNativePlatformMldsaProfile.handler]
      exact bind_keeps source (receipts source) _ _
        (server source _ (RegistrationNativePlatformMldsaBuildChronology.build source credential setup (RegistrationNativeWire.ledgerCodec wire)
          view failure allocation erased reservePeer helper writer index application))
        (fun _ => pure_keeps source (receipts source) _)
    | _ => exact ordinary trivial

/-- Arbitrary adaptive typed source programs retain all same-run private/native chronological signing information. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) :
    Keeps source (receipts (n := n) (KemSK := KemSK) source) (simulateQ callback work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps source (receipts source) value
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact bind_keeps source (receipts source) _ _ (handler source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query) ih

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaRunChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaRunChronology.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaRunChronology.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaRunChronology.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaRunChronology.program
