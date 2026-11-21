-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment

/-! The final runtime profile reifies the four actual ML capability sites while retaining its dynamic ordinary frame allocation and the common platform state. Evaluation recovers this exact runtime profile, including failed writers and the original ledger continuation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProfile
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
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State n KemSK source) (M source Platform))
  | .inr (.serverSend keyId plaintext) => lift
      (RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route (.inl (.inl (plaintext, keyId))) source)
  | .inr (.serverRaw raw) => lift
      (RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route (.inl (.inr raw)) source)
  | .inr (.beaconSend owner plaintext) => lift
      (RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route (.inr (owner, .inl plaintext)) source)
  | .inr (.beaconRaw owner raw) => lift
      (RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route (.inr (owner, .inr raw)) source)
  | query => RegistrationNativePlatformMldsaProfile.handler setup checks
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential
      view failure allocation reserveRegistration reservePeer erased helper writer query

/-- Every runtime callback retains its actual registration or ordinary writer effects under ML capability evaluation. -/
theorem evaluate_handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    evaluate (handler (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query) =
      RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query := by
  have original := RegistrationNativePlatformMldsaProfile.evaluate_handler (n := n) setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential
    view failure allocation reserveRegistration reservePeer erased helper writer query
  cases query with
  | inl coin => exact original
  | inr query => cases query with
    | serverSend keyId plaintext => exact RegistrationNativePlatformMldsaProgram.evaluate_lift _
    | serverRaw raw => exact RegistrationNativePlatformMldsaProgram.evaluate_lift _
    | beaconSend owner plaintext => exact RegistrationNativePlatformMldsaProgram.evaluate_lift _
    | beaconRaw owner raw => exact RegistrationNativePlatformMldsaProgram.evaluate_lift _
    | _ => exact original

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    M source Platform ((Value × RegistrationNativeLedger.State) × State n KemSK source) :=
  (simulateQ (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) created.server.server.metadata.sender bounds mode work)).run before

/-- Arbitrary adaptive raw/secrecy programs retain their literal original ledger, return value, corrected native state and external state. -/
theorem evaluate_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    RegistrationNativeMldsaProgram.evalState
      (run setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        bounds mode work before) =
      RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before := by
  have law := evaluate_simulate
    (handler (n := n) setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) created.server.server.metadata.sender bounds mode work)
  have callbacks : (fun query => evaluate (handler (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query)) =
      RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer :=
    funext (evaluate_handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer)
  rw [callbacks] at law
  exact congrFun law before

noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
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
        run setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased
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

/-- Actual ML capability evaluation recovers the complete initialized runtime profile and its arbitrary literal final event. -/
theorem evaluate_profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) :
    RegistrationNativeMldsaProgram.evalState
      (profile setup checks wire route representation ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary event) =
      RegistrationNativePlatformOrdinaryExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary event := by
  unfold profile RegistrationNativePlatformOrdinaryExperiment.profile
  rw [RegistrationNativeMldsaProgram.eval_bind, evaluate_base_lift, RegistrationNativeMldsaCreation.eval_start]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => exact RegistrationNativeMldsaProgram.eval_pure _
  | some initial => rw [evaluate_base_map, evaluate_run]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProfile.evaluate_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProfile.evaluate_handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProfile.evaluate_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProfile.evaluate_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProfile.evaluate_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProfile.evaluate_profile
