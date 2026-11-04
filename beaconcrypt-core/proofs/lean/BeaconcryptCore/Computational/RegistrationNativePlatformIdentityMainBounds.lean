-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealBeacon
import BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps
import BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps
import BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps

/-! The complete actual current-runtime joint-Ed client has a structural no-reveal property and the original qCreate identity bill. Every native/platform/oracle reply is quantified, including failed writers and nonwinning adaptive continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBounds
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M liftMain)
open RegistrationNativeIdentityMainNoRevealCore (Allowed mapped)
open RegistrationNativeIdentityMainCreateCapsCore (Creates)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value Next : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

def Safe (work : M n KemSK Platform source Value) (cap : Nat) : Prop :=
  ∀ before, AllQueriesSatisfy (work.run before) Allowed ∧ (work.run before).IsQueryBoundP Creates cap

omit primitives in
private theorem quiet_safe (work : M n KemSK Platform source Value)
    (prior : ∀ before, AllQueriesSatisfy (work.run before) RegistrationNativePlatformIdentityMainQuiet.Quiet) :
    Safe work 0 := fun before =>
  ⟨RegistrationNativePlatformIdentityMainQuiet.quiet_no_reveal _ (prior before),
    RegistrationNativePlatformIdentityMainQuiet.quiet_zero _ (prior before)⟩

omit primitives in
private theorem lift_safe (work : RegistrationNativeIdentityMain.M n KemSK source Value) (cap : Nat)
    (prior : ∀ before, AllQueriesSatisfy (work.run before) Allowed ∧ (work.run before).IsQueryBoundP Creates cap) :
    Safe (liftMain (Platform := Platform) work) cap := by
  intro before
  simp only [liftMain, StateT.run]
  exact ⟨mapped _ _ Allowed (prior before.1).1, (isQueryBoundP_map_iff _ _ cap).mpr (prior before.1).2⟩

omit primitives in
private theorem map_safe (work : M n KemSK Platform source Value) (change : Value → Next) (cap : Nat)
    (prior : Safe work cap) : Safe (change <$> work) cap := by
  intro before
  rw [StateT.run_map]
  exact ⟨mapped _ _ Allowed (prior before).1, (isQueryBoundP_map_iff _ _ cap).mpr (prior before).2⟩

omit primitives in
private theorem bind_safe (work : M n KemSK Platform source Value) (next : Value → M n KemSK Platform source Next)
    (first later : Nat) (prior : Safe work first) (after : ∀ value, Safe (next value) later) :
    Safe (work >>= next) (first + later) := by
  intro before
  rw [StateT.run_bind]
  exact ⟨allQueriesSatisfy_bind (prior before).1 (fun result => (after result.1 result.2).1),
    isQueryBoundP_bind (prior before).2 (fun result _ => (after result.1 result.2).2)⟩

omit primitives in
private theorem create_safe (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Safe (RegistrationNativePlatformIdentityMainLifecycle.create (n := n) (source := source) (Platform := Platform)
      setup edPin mlPin keyId checks representation created) 1 := by
  unfold RegistrationNativePlatformIdentityMainLifecycle.create
  rw [RegistrationNativePlatformIdentityMain.beacon_native]
  apply lift_safe _ 1
  intro before
  exact ⟨RegistrationNativeIdentityMainNoRevealBeacon.beacon_safe setup checks representation created _
      (RegistrationNativeIdentityNoReveal.create_safe setup edPin mlPin keyId) before,
    RegistrationNativeIdentityCreateCompilerCaps.beacon_bound setup checks representation created _ 1
      (RegistrationNativeIdentityCreateCaps.create_one setup edPin mlPin keyId) before⟩

omit primitives in
private theorem bundle_safe (index : Nat) :
    Safe (RegistrationNativePlatformIdentityMainBundle.bundle (n := n) (source := source)
      setup checks representation created writer index) 0 := by
  unfold RegistrationNativePlatformIdentityMainBundle.bundle
  apply map_safe _ _ 0
  apply quiet_safe
  exact RegistrationNativePlatformIdentityMainQuiet.beacon_quiet setup checks representation created _
    (RegistrationNativePlatformIdentityQuiet.bundle_quiet setup index writer)

omit primitives in
private theorem finish_safe (index : Nat) (packet : Option registration.ResponsePacket) :
    Safe (RegistrationNativePlatformIdentityMainLifecycle.finish (n := n) (source := source) (Platform := Platform)
      setup checks representation created (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet) 0 := by
  unfold RegistrationNativePlatformIdentityMainLifecycle.finish
  apply quiet_safe
  exact RegistrationNativePlatformIdentityMainQuiet.beacon_quiet setup checks representation created _
    (RegistrationNativePlatformIdentityQuiet.native_quiet _
      (RegistrationNativePlatformIdentityQuiet.finish_quiet setup _ index packet))

private theorem ambient_safe (query : TypedSpec.Domain) :
    Safe (RegistrationNativePlatformIdentityMainAmbient.step (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query) 0 := by
  apply quiet_safe
  intro before
  exact RegistrationNativePlatformIdentityMainQuiet.ordinary_quiet _ before

omit primitives in
private theorem report_safe (packet : registration.InitPacket) :
    Safe (liftMain (n := n) (KemSK := KemSK) (source := source) (Platform := Platform)
      (RegistrationNativeIdentityMain.report packet)) 0 :=
  lift_safe _ 0 (fun before => ⟨RegistrationNativeIdentityMainNoRevealCore.report_safe packet before,
    RegistrationNativeIdentityMainCreateCapsCore.report_zero packet before⟩)

attribute [local irreducible] RegistrationNativePlatformIdentityMainAmbient.step RegistrationNativePlatformIdentityMainAmbient.command

/-- The actual typed dispatcher creates at most one identity precisely in create and never reveals any generated seed. -/
theorem handler_safe (query : TypedSpec.Domain) :
    Safe (RegistrationNativePlatformIdentityMainTyped.handler (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query)
      (if RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  cases query with
  | inl coin => exact ambient_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inl coin)
  | inr query => cases query with
    | create edPin mlPin keyId => exact create_safe setup checks representation created edPin mlPin keyId
    | bundle index => exact bundle_safe setup checks representation created writer index
    | finish index packet => exact finish_safe setup checks wire representation created index packet
    | accept packet =>
      unfold RegistrationNativePlatformIdentityMainTyped.handler
      exact bind_safe _ _ 0 0 (report_safe packet) (fun _ => ambient_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet)))
    | build session application => exact ambient_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build session application))
    | hmac key message => exact ambient_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hmac key message))
    | hash bytes => exact ambient_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hash bytes))
    | serverSend keyId plaintext => exact ambient_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverSend keyId plaintext))
    | serverRaw raw => exact ambient_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverRaw raw))
    | beaconSend index plaintext => exact ambient_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconSend index plaintext))
    | beaconRaw index raw => exact ambient_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconRaw index raw))

private theorem program_no_reveal (work : OracleComp TypedSpec Value) (before : State n KemSK source × Platform) :
    AllQueriesSatisfy ((simulateQ (RegistrationNativePlatformIdentityMainTyped.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run before) Allowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind ((handler_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before).1) (fun result => ih result.1 result.2)

private theorem program_creates (work : OracleComp TypedSpec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) cap)
    (before : State n KemSK source × Platform) :
    ((simulateQ (RegistrationNativePlatformIdentityMainTyped.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run before).IsQueryBoundP Creates cap :=
  OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded
    (fun query current => (handler_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current).2) before

private theorem run_no_reveal (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source × Platform) :
    AllQueriesSatisfy ((RegistrationNativePlatformIdentityMainFull.run setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work).run before) Allowed := by
  unfold RegistrationNativePlatformIdentityMainFull.run
  exact program_no_reveal setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before

private theorem run_creates (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityMainFull.run setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work).run before).IsQueryBoundP Creates budget.create := by
  unfold RegistrationNativePlatformIdentityMainFull.run
  apply program_creates setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ budget.create _ before
  simpa only [RegistrationNativeIdentityProfileCreateCaps.wrap_create_sum] using RegistrationNativeFullCompiler.compile_bound setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) created.server.server.metadata.sender bounds mode work budget bounded (1 : Fin 12)

/-- The complete initialized actual client has no reveal query, for every raw mode and every adversarial/primitive reply. -/
theorem client_no_reveal (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (previous : Platform) :
    AllQueriesSatisfy (RegistrationNativePlatformIdentityMainProfile.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary event previous) Allowed := by
  unfold RegistrationNativePlatformIdentityMainProfile.client
  apply allQueriesSatisfy_bind (RegistrationNativeIdentityMainNoRevealCore.coins_safe _)
  intro initialized
  cases initialized with
  | none => trivial
  | some initial =>
    apply allQueriesSatisfy_bind (run_no_reveal setup checks wire route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode _ _)
    intro result
    apply allQueriesSatisfy_bind (RegistrationNativeIdentityMainNoRevealCore.emit_safe _)
    intro _
    trivial

/-- The original admitted raw qCreate bound is the literal complete initialized indexed-Ed creation bill; startup adds no Beacon identity. -/
theorem client_creates (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (previous : Platform) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput)) :
    (RegistrationNativePlatformIdentityMainProfile.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary event previous).IsQueryBoundP Creates budget.create := by
  unfold RegistrationNativePlatformIdentityMainProfile.client
  rw [← Nat.zero_add budget.create]
  apply isQueryBoundP_bind (n := 0) (m := budget.create) (RegistrationNativeIdentityMainCreateCapsCore.coins_zero _)
  intro initialized _
  cases initialized with
  | none => exact isQueryBoundP_pure Creates _ budget.create
  | some initial =>
    apply isQueryBoundP_bind (n := budget.create) (m := 0)
      (run_creates setup checks wire route representation initial.created initial.credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode
          (adversary initial.public) budget (bounded initial.public) (RegistrationNativePlatformIdentityMainProfile.fromInitial initial previous))
    intro result _
    apply isQueryBoundP_bind (n := 0) (m := 0) (RegistrationNativeIdentityMainCreateCapsCore.emit_zero _)
    intro _ _
    exact isQueryBoundP_pure Creates _ 0

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBounds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBounds.handler_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBounds.handler_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBounds.client_no_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBounds.client_no_reveal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBounds.client_creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBounds.client_creates
