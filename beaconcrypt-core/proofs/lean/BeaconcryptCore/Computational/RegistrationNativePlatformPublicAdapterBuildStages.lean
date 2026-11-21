-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace
/-! The response source log is generated at its actual first-record, hash and signing calls. The same first-record reply and signing reply remain in the log when a later writer or installer refuses. The joint source law removes only native bookkeeping and never reconstructs a stage from a final native history. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStages
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage recorded)
abbrev Spec := RegistrationNativePlatformPublicAdapterBuildPublication.Spec
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK E P A : Type} {base : OracleSpec I} {Reader Response : Type}
variable {mlSource : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Base" => StateT P ProbComp

def observation : (query : Spec.Domain) → Spec.Range query → List Stage
  | .inl initial, reply => [.firstRecord initial reply]
  | .inr (.inl query), reply => RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation query reply
  | .inr (.inr _), _ => []

noncomputable def code (initial : registration.ServerInitialKdf) :
    OracleComp Spec (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) := do
  let first ← Spec.query (.inl initial)
  RegistrationNativePlatformServerPublication.continueResult first
    (RegistrationNativePlatformServerPublication.program
      (fun query => Spec.query (.inr (.inl query))) (fun signed => Spec.query (.inr (.inr signed))))

omit primitive in
theorem interpret {m : Type → Type} [Monad m] [LawfulMonad m]
    (implementation : QueryImpl Spec m) (initial : registration.ServerInitialKdf) :
    simulateQ implementation (code initial) = (do
      let first ← implementation (.inl initial)
      RegistrationNativePlatformServerPublication.continueResult first
        (RegistrationNativePlatformServerPublication.program
          (fun query => implementation (.inr (.inl query))) (fun signed => implementation (.inr (.inr signed))))) := by
  unfold code
  rw [simulateQ_bind, simulateQ_spec_query]
  apply bind_congr
  intro first
  cases first with
  | fail error | div => rfl
  | ok first => cases first with
    | Err previous => rfl
    | Ok pending =>
      simp only [RegistrationNativePlatformServerPublication.continueResult]
      rw [RegistrationNativePlatformServerPublication.program_interpret]
      simp only [simulateQ_spec_query]

noncomputable def native : QueryImpl Spec (StateT Native Base)
  | .inl initial => AdapterPublicServerLocalLens.localState
      (RegistrationNativePlatformSourceRecord.fromInitialWithHash
        (RegistrationNativePlatformServerCompletion.records coins setup codec)
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper) initial)
  | .inr (.inl query) => AdapterPublicServerCompletionNative.outgoing coins sign query
  | .inr (.inr signed) => AdapterPublicServerSigningNative.encoder (AdapterPublicServerCompletionNative.writer writer) signed

noncomputable def physical (initial : registration.ServerInitialKdf) :=
  simulateQ (recorded
    (RegistrationNativePlatformPublicAdapterBuildPublication.handler (n:=n) coins setup codec view failure allocation helper erased sign writer)
    observation) (code initial)

/-- The logged source runner executes the actual source request tree and retains its actual replies jointly with every physical poststate. -/
theorem source (initial : registration.ServerInitialKdf) (before : Native × List Stage) :
    Prod.map id (Prod.map backend id) <$>
      (simulateQ (recorded (native coins setup codec view failure allocation helper erased sign writer) observation) (code initial)).run before =
      (physical coins setup codec view failure allocation helper erased sign writer initial).run (backend before.1, before.2) := by
  apply RegistrationNativePlatformPublicAdapterSourceTrace.source
  intro query current
  exact RegistrationNativePlatformPublicAdapterBuildPublication.query_source coins setup codec view failure allocation helper erased sign writer query current

/-- Removing the source stage log gives the same independent source first-record/publication runner. -/
theorem erase (initial : registration.ServerInitialKdf) (before : Backend n KemSK × List Stage) :
    Prod.map id Prod.fst <$> (physical coins setup codec view failure allocation helper erased sign writer initial).run before =
      (RegistrationNativePlatformPublicAdapterBuildPublication.beforeInstall coins setup codec view failure allocation helper erased sign writer initial).run before.1 := by
  rw [physical, RegistrationNativePlatformPublicAdapterSourceTrace.erase, interpret]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStages

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStages.interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStages.interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStages.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStages.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStages.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStages.erase
