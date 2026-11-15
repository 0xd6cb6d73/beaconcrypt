-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProfile
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile

/-! The complete current dynamic-writer native profile is interpreted by one executable ordinary joint-Ed client. Startup constructs the independent Server/ML/KEM auxiliary state internally; the challenged Beacon Ed seed is supplied only by its generated indexed service. Every constructor/API failure and full shared P poststate is retained. This is source correspondence, not yet a publication-security reduction or restricted-root confidentiality client. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginObserved
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project liftMain)
open RegistrationNativePlatformIdentityMainOwned (Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

abbrev Observed (n : Nat) (KemSK Platform Value : Type) (source : RegistrationNativeMldsa.Source) :=
  (Value × RegistrationNativeLedger.State) × (State n KemSK source × Platform)

noncomputable def client (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform) :
    OracleComp PqxdhJointPhase1Reports.ProtocolSpec (Option (Observed n KemSK Platform Value source)) := do
  let initialized ← simulateQ RegistrationNativeIdentityMain.coins
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure none
  | some initial =>
    let result ← (RegistrationNativePlatformIdentityMainFull.run setup checks wire route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public)).run
        (RegistrationNativePlatformIdentityMainProfile.fromInitial initial previous)
    let _ ← RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityFinalReports.reports
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) result.1.2.transcript result.2.1.beacons)
    pure (some result)

omit primitives in
def sourceProject (result : Option (Observed n KemSK Platform Value source) × SourceState) :
    Option (RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) × Platform) :=
  result.1.map fun observed => ((observed.1.1,(observed.1.2,(project (observed.2,result.2)).1)),observed.2.2)

noncomputable def native (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform) :
    ProbComp (Option (RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) × Platform)) := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure none
  | some initial =>
    (fun result => some ((result.1.1.1,(result.1.1.2,result.1.2)),result.2)) <$>
      (RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation initial.created source initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public) initial.state).run previous

/-- The actual ordinary monitor client keeps the same complete retained execution and changes only its final ledger observer. -/
theorem client_map (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (previous : Platform) :
    RegistrationNativePlatformIdentityMainProfile.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary event previous =
    (fun result : Option (Observed n KemSK Platform Value source) => match result with
      | none => (false,previous)
      | some observed => (event (observed.1.1,(observed.1.2,())),observed.2.2)) <$>
      client setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous := by
  unfold RegistrationNativePlatformIdentityMainProfile.client client
  simp only [map_bind]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some initial => simp only [map_bind,map_pure]

omit primitives in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
omit primitives in
private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
omit primitives in
private theorem emit_apply (joint : PqxdhJointIdentity.Primitives)
    (reports : List PqxdhJointPhase1Reports.CandidateReport) (before : SourceState) :
    (simulateQ (RegistrationNativeIdentityMainSource.implementation joint) (RegistrationNativeIdentityMain.emit reports)) before =
      pure ((),before) := RegistrationNativeIdentityMainSource.emit_source joint reports before

/-- Source realization restores the actual complete initialized native and platform result before any event is selected. -/
theorem client_source (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (previous : Platform) (before : SourceState) :
    sourceProject <$> (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
      (client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous)).run before =
      native (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous := by
  unfold client native
  simp only [simulateQ_bind,StateT.run_bind,map_bind]
  conv_rhs => rw [←RegistrationNativeIdentityMainProfile.coins_value setup.joint
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) before]
  rw [bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨initialized,privatePool⟩ reached
  have actual : initialized ∈ support (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) := by
    rw [←RegistrationNativeIdentityMainProfile.coins_value setup.joint
      (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) before,support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  cases initialized with
  | none => simp only [simulateQ_pure,StateT.run_pure,map_pure,sourceProject,Option.map_none]
  | some initial =>
    have empty := RegistrationNativeScalarRun.start_empty setup source ensureInit identityIndex serverKeyId initial actual
    have same := RegistrationNativePlatformIdentityMainFull.run_source setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds mode (adversary initial.public) (RegistrationNativePlatformIdentityMainProfile.fromInitial initial previous,privatePool)
      (RegistrationNativePlatformIdentityMainProfile.initial_owned setup.joint initial previous privatePool)
    rw [RegistrationNativePlatformIdentityMainProfile.initial_project initial empty previous privatePool] at same
    have optional := congrArg (fun distribution =>
      (fun result : (Value × RegistrationNativeLedger.State) × (RegistrationNativeExperiment.State n KemSK source × Platform) =>
        some ((result.1.1,(result.1.2,result.2.1)),result.2.2)) <$> distribution) same
    simpa only [interpret,StateT.run,simulateQ_bind,bind_apply,map_apply,simulateQ_map,emit_apply,
      map_pure,pure_bind,bind_pure_comp,Functor.map_map,map_bind,sourceProject,Option.map_some,Prod.map,id_eq,project] using optional

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginObserved
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginObserved.client_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginObserved.client_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginObserved.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginObserved.client_source
