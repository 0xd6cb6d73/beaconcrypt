-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! Adaptive native registration runs the checked source Init/response writers, pre-AEAD prefix allocation, repeated Server pin hash and stateful reservations on one persistent outer platform state. Finish copies the application before installing the actual assigned sender identifier. The original private native World, generated KEM pool, Beacon owners and full histories remain together. Other typed operations retain their existing native bodies; their explicit wire/primitive boundaries are unchanged. Complete public-wrapper/container correspondence is proved separately. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeExperiment (State Initial Public)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {E Value ι KemSK : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m]

abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) (m : Type → Type) :=
  StateT (State n KemSK source) m

def liftNative (coins : QueryImpl unifSpec m) {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativeExperiment.M n KemSK source Value) : M n KemSK source m Value :=
  fun before => simulateQ coins (work.run before)

def server {source : RegistrationNativeMldsa.Source}
    (work : StateT (RegistrationServerFrontendCompiler.State n) m Value) : M n KemSK source m Value :=
  fun before => (fun result => (result.1, { before with server := result.2 })) <$> work.run before.server

noncomputable def trusted (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (M n KemSK source m) :=
  fun query => liftNative coins (RegistrationNativeExperiment.trusted setup checks representation created source query)

def writer {source : RegistrationNativeMldsa.Source}
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) :
    QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source m) :=
  fun query => StateT.lift (implementation query)

noncomputable def bundleHandler (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) :
    QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (M n KemSK source m)
  | .inl query => trusted coins setup checks representation created source query
  | .inr query => writer implementation query

noncomputable def bundle (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) (index : Nat) :
    M n KemSK source m (RustM (Option Pqxdh.Bytes)) := fun before => do
  let result ← (simulateQ (bundleHandler coins setup checks representation created source implementation)
    (((RegistrationNativePlatformGenericBundle.program E setup source index).run before.beacons).run
      (RegistrationWorldAgreementCompiler.erase before.server.world))).run before
  pure ((do let optional ← result.1.1.1
            .ok (optional.map TranscriptAuthParts.absSlice)),
    { result.2 with
      beacons := result.1.1.2
      server := { result.2.server with world :=
        RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })

noncomputable def handler (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (reserveRegistration reservePeer : m Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) :
    QueryImpl TypedSpec (M n KemSK source m)
  | .inr (.bundle owner) => bundle coins setup checks representation created source implementation owner
  | .inr (.accept packet) => do
      modify fun before => { before with parsedAccepts := before.parsedAccepts + 1 }
      server (RegistrationNativePlatformSourceAccept.accept coins setup (ledgerCodec wire) checks reserveRegistration
        route source.verify representation created packet)
  | .inr (.build session application) => do
      let result ← server (RegistrationNativePlatformSourceSeal.build coins setup (ledgerCodec wire) view failure allocation
        erased reservePeer (RegistrationNativeMldsa.owned source credential) helper implementation session application)
      pure (do let optional ← result
               .ok (optional.map fun value => (value.1, TranscriptAuthParts.absSlice value.2)))
  | .inr (.finish owner packet) => liftNative coins
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire owner packet))
  | query => liftNative coins (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query)

noncomputable def run (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (reserveRegistration reservePeer : m Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    m ((Value × RegistrationNativeLedger.State) × State n KemSK source) :=
  (simulateQ (handler coins setup checks wire route representation created source credential view failure allocation
    reserveRegistration reservePeer erased helper implementation)
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)).run before

noncomputable def profile (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (reserveRegistration reservePeer : m Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) : m Bool := do
  let initialized ← simulateQ coins (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure false
  | some initial =>
      (fun result => event (result.1.1, (result.1.2, result.2))) <$>
        run coins setup checks wire route representation initial.created source initial.credential view failure allocation
          reserveRegistration reservePeer erased helper implementation bounds mode (adversary initial.public) initial.state

variable [LawfulMonad m]

section Interpret
open RegistrationNativePlatformInterpret (state state_bind state_pure state_simulate)
variable {κ : Type} {spec : OracleSpec.{0, 0} κ}

omit primitives in
private theorem lift_interpret (implementation : QueryImpl spec m) {S A : Type} (work : OracleComp spec A) :
    state implementation (StateT.lift work : StateT S (OracleComp spec) A) = StateT.lift (simulateQ implementation work) := by
  funext before
  change simulateQ implementation ((StateT.lift work : StateT S (OracleComp spec) A).run before) =
    (StateT.lift (simulateQ implementation work) : StateT S m A).run before
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure]

omit primitives in
private theorem liftNative_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    {source : RegistrationNativeMldsa.Source} (work : RegistrationNativeExperiment.M n KemSK source Value) :
    state implementation (liftNative coins work) =
      liftNative (fun query => simulateQ implementation (coins query)) work := by
  funext before
  exact (QueryImpl.simulateQ_compose implementation coins (work.run before)).symm

omit primitives in
private theorem server_interpret (implementation : QueryImpl spec m) {source : RegistrationNativeMldsa.Source}
    (work : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp spec) Value) :
    state implementation (server (KemSK := KemSK) (source := source) work) = server (state implementation work) := by
  funext before
  simp only [state, server, StateT.run, simulateQ_map]

omit primitives in
private theorem bundleHandler_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (query : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain) :
    state implementation (bundleHandler coins setup checks representation created source writer query) =
      bundleHandler (fun query => simulateQ implementation (coins query)) setup checks representation created source
        (fun query => simulateQ implementation (writer query)) query := by
  cases query with
  | inl query => exact liftNative_interpret implementation coins _
  | inr query => exact lift_interpret implementation _

omit primitives in
theorem bundle_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec)) (index : Nat) :
    state implementation (bundle (n := n) coins setup checks representation created source writer index) =
      bundle (fun query => simulateQ implementation (coins query)) setup checks representation created source
        (fun query => simulateQ implementation (writer query)) index := by
  funext before
  unfold state bundle StateT.run
  rw [simulateQ_bind]
  have interpreted := congrFun (state_simulate implementation
    (bundleHandler coins setup checks representation created source writer)
    (((RegistrationNativePlatformGenericBundle.program E setup source index).run before.beacons).run
      (RegistrationWorldAgreementCompiler.erase before.server.world))) before
  simp only [state, StateT.run] at interpreted
  simp only [StateT.run]
  rw [interpreted]
  simp only [bundleHandler_interpret]
  apply bind_congr
  intro result
  exact simulateQ_pure implementation _

theorem handler_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (OracleComp spec))
    (reserveRegistration reservePeer : OracleComp spec Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (query : TypedSpec.Domain) :
    state implementation (handler (n := n) coins setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer erased helper writer query) =
      handler (fun query => simulateQ implementation (coins query)) setup checks wire route representation created source credential view failure
        (fun before capacity => simulateQ implementation (allocation before capacity))
        (simulateQ implementation reserveRegistration) (simulateQ implementation reservePeer) erased
        (fun query => simulateQ implementation (helper query)) (fun query => simulateQ implementation (writer query)) query := by
  cases query with
  | inl query => exact liftNative_interpret implementation coins _
  | inr command =>
      cases command with
      | bundle owner => exact bundle_interpret implementation coins setup checks representation created source writer owner
      | accept packet =>
          unfold handler
          rw [state_bind]
          have update : state implementation
              (modify fun before : State n KemSK source => { before with parsedAccepts := before.parsedAccepts + 1 }) =
              (modify fun before : State n KemSK source => { before with parsedAccepts := before.parsedAccepts + 1 } :
                M n KemSK source m Unit) := rfl
          rw [update]
          apply bind_congr
          intro unused
          rw [server_interpret, RegistrationNativePlatformSourceAccept.accept_interpret]
      | build session application =>
          unfold handler
          rw [state_bind, server_interpret, RegistrationNativePlatformSourceSeal.build_interpret]
          apply bind_congr
          intro result
          exact state_pure implementation _
      | _ => exact liftNative_interpret implementation coins _

theorem program_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (OracleComp spec))
    (reserveRegistration reservePeer : OracleComp spec Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (work : OracleComp TypedSpec Value) :
    state implementation (simulateQ (handler (n := n) coins setup checks wire route representation created source credential view failure
      allocation reserveRegistration reservePeer erased helper writer) work) =
      simulateQ (handler (fun query => simulateQ implementation (coins query)) setup checks wire route representation created source credential
        view failure (fun before capacity => simulateQ implementation (allocation before capacity))
        (simulateQ implementation reserveRegistration) (simulateQ implementation reservePeer) erased
        (fun query => simulateQ implementation (helper query)) (fun query => simulateQ implementation (writer query))) work := by
  rw [state_simulate]
  simp only [handler_interpret]

theorem run_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (OracleComp spec))
    (reserveRegistration reservePeer : OracleComp spec Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    simulateQ implementation (run coins setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode work before) =
      run (fun query => simulateQ implementation (coins query)) setup checks wire route representation created source credential view failure
        (fun before capacity => simulateQ implementation (allocation before capacity))
        (simulateQ implementation reserveRegistration) (simulateQ implementation reservePeer) erased
        (fun query => simulateQ implementation (helper query)) (fun query => simulateQ implementation (writer query)) bounds mode work before :=
  congrFun (program_interpret implementation coins setup checks wire route representation created source credential view failure allocation
    reserveRegistration reservePeer erased helper writer
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)) before

theorem profile_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (OracleComp spec))
    (reserveRegistration reservePeer : OracleComp spec Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) :
    simulateQ implementation (profile coins setup checks wire route representation source ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer erased helper writer bounds mode adversary event) =
      profile (fun query => simulateQ implementation (coins query)) setup checks wire route representation source ensureInit identityIndex serverKeyId
        view failure (fun before capacity => simulateQ implementation (allocation before capacity))
        (simulateQ implementation reserveRegistration) (simulateQ implementation reservePeer) erased
        (fun query => simulateQ implementation (helper query)) (fun query => simulateQ implementation (writer query)) bounds mode adversary event := by
  unfold profile
  rw [simulateQ_bind]
  have initialized := (QueryImpl.simulateQ_compose implementation coins
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)).symm
  rw [initialized]
  apply bind_congr
  intro initial
  cases initial with
  | none => exact simulateQ_pure implementation false
  | some initial => rw [simulateQ_map, run_interpret]

end Interpret

end BeaconcryptCore.Computational.RegistrationNativePlatformExperiment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExperiment.bundle_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExperiment.bundle_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExperiment.handler_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExperiment.handler_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExperiment.program_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExperiment.program_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExperiment.run_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExperiment.run_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExperiment.profile_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExperiment.profile_interpret
