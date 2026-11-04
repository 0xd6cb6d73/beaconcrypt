-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer
import BeaconcryptCore.Computational.RegistrationNativeMldsaCreation

/-! The complete corrected stateful platform profile reifies actual startup/create/Init-sign/Server-sign ML leaves in the existing capability language. All shared public allocation state, trusted source serialization, repeated Server pin hashing, corrected assigned sender ID, adaptive native ledger and every failure prefix are retained. This is exact evaluation of this new profile; no equality to the legacy native profile is claimed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformMldsaProgram (M evaluate lift inject coins)
open RegistrationNativeExperiment (State Public)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]

omit primitive in
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := bind_pure_comp _ _

omit primitive in
private theorem evaluate_server {A : Type}
    (work : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) A) :
    evaluate (RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := source) work) =
      RegistrationNativePlatformExperiment.server (evaluate work) := by
  funext before previous
  simp only [evaluate, RegistrationNativePlatformExperiment.server,
    RegistrationNativeMldsaProgram.evalState, RegistrationNativeMldsaProgram.evaluate,
    StateT.run, state_map_apply, simulateQ_map]

omit primitive in
private theorem evaluate_simulate {I A : Type} {spec : OracleSpec I}
    (handler : QueryImpl spec (StateT (State n KemSK source) (M source Platform))) (work : OracleComp spec A) :
    evaluate (simulateQ handler work) = simulateQ (fun query => evaluate (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, RegistrationNativePlatformMldsaProgram.evaluate_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query,
      RegistrationNativePlatformMldsaProgram.evaluate_bind, ih]

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State n KemSK source) (M source Platform))
  | .inr (.create edPin mlPin keyId) =>
      inject (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId)
  | .inr (.bundle owner) => RegistrationNativePlatformMldsaBundle.sourceBundle setup checks representation created writer owner
  | .inr (.build session application) => do
      let result : RustM (Option (U64 × alloc.vec.Vec U8)) ← RegistrationNativePlatformExperiment.server (n := n) (KemSK := KemSK) (source := source)
        (RegistrationNativePlatformMldsaServer.build source credential setup (RegistrationNativeWire.ledgerCodec wire)
          view failure allocation erased reservePeer helper writer session application)
      pure (do let optional ← result
               .ok (optional.map fun value => (value.1, TranscriptAuthParts.absSlice value.2)))
  | query => lift (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer erased helper writer query)

/-- Every corrected platform callback, including its actual source allocation/writer failures, is recovered by named ML capability evaluation. -/
theorem evaluate_handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    evaluate (handler (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query) =
      RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential
        view failure allocation reserveRegistration reservePeer erased helper writer query := by
  cases query with
  | inl coin => exact RegistrationNativePlatformMldsaProgram.evaluate_lift _
  | inr query => cases query with
    | create edPin mlPin keyId =>
        rw [handler, RegistrationNativePlatformMldsaProgram.evaluate_inject, RegistrationNativeMldsaCreation.eval_create]
        funext before
        exact (RegistrationNativePlatformMldsaProgram.lift_coins
          ((RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before)).symm
    | bundle owner => exact RegistrationNativePlatformMldsaBundle.evaluate_sourceBundle setup checks representation created writer owner
    | build session application =>
        unfold handler RegistrationNativePlatformExperiment.handler
        rw [RegistrationNativePlatformMldsaProgram.evaluate_bind, evaluate_server,
          RegistrationNativePlatformMldsaServer.evaluate_build]
        apply bind_congr
        intro result
        exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
    | _ => exact RegistrationNativePlatformMldsaProgram.evaluate_lift _

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    M source Platform ((Value × RegistrationNativeLedger.State) × State n KemSK source) :=
  (simulateQ (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)).run before

/-- Arbitrary adaptive raw/secrecy programs retain their literal original ledger, return value, corrected native state and external state. -/
theorem evaluate_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    RegistrationNativeMldsaProgram.evalState
      (run setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
        bounds mode work before) =
      RegistrationNativePlatformExperiment.run coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer bounds mode work before := by
  have law := evaluate_simulate
    (handler (n := n) setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)
  have callbacks : (fun query => evaluate (handler (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query)) =
      RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer :=
    funext (evaluate_handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer)
  rw [callbacks] at law
  exact congrFun law before

noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) : M source Platform Bool := do
  let initialized ← StateT.lift (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure false
  | some initial =>
      (fun result => event (result.1.1, (result.1.2, result.2))) <$>
        run setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer erased
          helper writer bounds mode (adversary initial.public) initial.state

omit primitive in
private theorem evaluate_base_lift {A : Type} (work : OracleComp (RegistrationNativeMldsaProgram.Spec source) A) :
    RegistrationNativeMldsaProgram.evalState (StateT.lift work : M source Platform A) =
      StateT.lift (RegistrationNativeMldsaProgram.evaluate work) := by
  funext before
  change simulateQ RegistrationNativeMldsaProgram.actual (do let value ← work; pure (value, before)) = _
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

omit primitive in
private theorem evaluate_base_map {A B : Type} (f : A → B) (work : M source Platform A) :
    RegistrationNativeMldsaProgram.evalState (f <$> work) = f <$> RegistrationNativeMldsaProgram.evalState work := by
  funext before
  simp only [RegistrationNativeMldsaProgram.evalState, RegistrationNativeMldsaProgram.evaluate,
    StateT.run, state_map_apply, simulateQ_map]

/-- Actual ML capability evaluation recovers the complete corrected initialized platform profile and its arbitrary literal final event. -/
theorem evaluate_profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) :
    RegistrationNativeMldsaProgram.evalState
      (profile setup checks wire route representation ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer
        erased helper writer bounds mode adversary event) =
      RegistrationNativePlatformExperiment.profile coins setup checks wire route representation source ensureInit identityIndex serverKeyId
        view failure allocation reserveRegistration reservePeer erased helper writer bounds mode adversary event := by
  unfold profile RegistrationNativePlatformExperiment.profile
  rw [RegistrationNativeMldsaProgram.eval_bind, evaluate_base_lift, RegistrationNativeMldsaCreation.eval_start,
    RegistrationNativePlatformMldsaProgram.lift_coins]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => exact RegistrationNativeMldsaProgram.eval_pure _
  | some initial => rw [evaluate_base_map, evaluate_run]

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile.evaluate_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile.evaluate_handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile.evaluate_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile.evaluate_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile.evaluate_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile.evaluate_profile
