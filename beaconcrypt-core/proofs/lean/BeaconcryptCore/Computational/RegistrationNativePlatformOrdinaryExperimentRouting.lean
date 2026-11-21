-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
/-! Runtime writer failure is a terminal public gate after the exact advanced private Native/World execution. These operational laws retain owner lookup, missing/inactive paths, full produced-frame analysis state and the single platform poststate; they do not identify complete old and new profiles. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeExperiment (State)
open RegistrationNativePlatformOrdinaryExperiment (M world record replaceWorld canonicalWire)
open RegistrationNativePlatformOrdinaryGate (gate)
variable {n : Nat} {Platform E Value ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem ledger_canonical (wire : Wire) :
    ledgerCodec (canonicalWire wire) = CborRawCanonicalBuild.canonical (ledgerCodec wire) := rfl

private theorem lift_map {A B : Type} (f : A → B) (work : ProbComp A) :
    (StateT.lift (f <$> work) : StateT Platform ProbComp B) = f <$> StateT.lift work := by
  funext previous
  change (StateT.lift (f <$> work) : StateT Platform ProbComp B).run previous =
    (f <$> (StateT.lift work : StateT Platform ProbComp A)).run previous
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]

private theorem world_lift (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) :
    world (source := source) (KemSK := KemSK) (RegistrationNativePlatformOrdinaryWorld.liftWorld (Platform := Platform) work) =
      RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeExperiment.world work) := by
  funext before
  simp only [world, RegistrationNativePlatformOrdinaryWorld.liftWorld, RegistrationNativePlatformExperiment.liftNative,
    RegistrationNativePlatformMldsaProgram.lift_coins, RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server, StateT.run, Functor.map_map]
  rw [← lift_map]
  rfl

private theorem bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem world_bind {Next : Type}
    (work : RegistrationNativePlatformOrdinaryWorld.M n Platform Value)
    (next : Value → RegistrationNativePlatformOrdinaryWorld.M n Platform Next) :
    world (source := source) (KemSK := KemSK) (work >>= next) = (world work >>= fun value => world (next value)) := by
  funext before
  unfold RegistrationNativePlatformOrdinaryExperiment.world
  dsimp only [StateT.run]
  simp only [bind_apply, map_bind, bind_map_left]
  apply bind_congr
  intro result
  rfl

private theorem world_platform (work : StateT Platform ProbComp Value) :
    world (source := source) (KemSK := KemSK) (StateT.lift work : RegistrationNativePlatformOrdinaryWorld.M n Platform Value) =
      (StateT.lift work : M n KemSK source Platform Value) := by
  funext before
  simp only [world, StateT.run_lift, map_bind, map_pure]
  rfl

def after (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : M n KemSK source Platform (Option RawCtxSourceSend.Encrypted)) :
    M n KemSK source Platform (Option RawCtxSourceSend.Encrypted) := do
  let output ← work
  StateT.lift (gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) output)

private theorem world_after (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option RawCtxSourceSend.Encrypted)) :
    world (source := source) (KemSK := KemSK) (RegistrationNativePlatformOrdinaryWorldRouting.after reserve work) =
      after reserve (RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeExperiment.world work)) := by
  unfold RegistrationNativePlatformOrdinaryWorldRouting.after after
  rw [world_bind, world_lift]
  apply bind_congr
  intro output
  exact world_platform _

/-- Actual Server source writing may refuse publication only after the same complete canonical Native poststate has been retained. -/
theorem server_send (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (keyId : U64) (plaintext : Pqxdh.Bytes) :
    record (n := n) setup wire reserve route (.inl (.inl (plaintext, keyId))) source =
      after reserve (RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeExperiment.record setup (canonicalWire wire) route (.inl (.inl (plaintext, keyId))) source)) := by
  unfold record RegistrationNativeExperiment.record
  dsimp only
  rw [RegistrationNativePlatformOrdinaryWorldGuarded.server, world_after, ledger_canonical]

/-- Actual raw Server receive has no writer request and retains its full canonical Native execution and platform state. -/
theorem server_raw (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (raw : Pqxdh.Bytes) :
    record (n := n) setup wire reserve route (.inl (.inr raw)) source =
      RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeExperiment.record setup (canonicalWire wire) route (.inl (.inr raw)) source) := by
  unfold record RegistrationNativeExperiment.record
  dsimp only
  rw [RegistrationNativePlatformOrdinaryLower.actual_query]
  simp only [RegistrationNativePlatformOrdinaryLower.terminal]
  rw [world_lift, ledger_canonical]

private theorem after_apply (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : M n KemSK source Platform (Option RawCtxSourceSend.Encrypted)) (before : State n KemSK source) :
    after reserve work before = (do
      let result ← work before
      let output ← gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result.1
      pure (output, result.2)) := rfl

private theorem platform_lift_pure {A : Type} (value : A) :
    (StateT.lift (pure value : ProbComp A) : StateT Platform ProbComp A) = pure value := by
  funext previous
  change (pure value >>= fun result => pure (result, previous) : ProbComp _) = pure (value, previous)
  exact pure_bind _ _

/-- The actual Beacon owner lookup and source writer retain every native field before the terminal public publication decision. -/
theorem beacon_send (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owner : Nat) (plaintext : Pqxdh.Bytes) :
    record (n := n) setup wire reserve route (.inr (owner, .inl plaintext)) source =
      after reserve (RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeExperiment.record setup (canonicalWire wire) route (.inr (owner, .inl plaintext)) source)) := by
  funext before
  cases selected : before.beacons[owner]? with
  | none =>
      simp only [record, RegistrationNativeExperiment.record, RegistrationNativePlatformExperiment.liftNative,
        StateT.run, selected, RegistrationNativePlatformMldsaProgram.lift_coins, after_apply, gate,
        platform_lift_pure, pure_bind]
  | some beacon =>
      let original : StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option RawCtxSourceSend.Encrypted) :=
        CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical (ledgerCodec wire)) route
          (.inr (.inr (.inr (beacon.worldOwner, .inl plaintext))))
      have moved := congrFun ((congrArg (world (source := source) (KemSK := KemSK))
        (RegistrationNativePlatformOrdinaryWorldGuarded.beacon setup (ledgerCodec wire) reserve route beacon.worldOwner plaintext)).trans
        (world_after reserve original)) before
      simpa only [record, RegistrationNativeExperiment.record, RegistrationNativePlatformExperiment.liftNative,
        StateT.run, selected, after_apply, ledger_canonical, original] using moved

/-- Raw Beacon receive performs the literal original complete Native operation and leaves the runtime allocator state untouched. -/
theorem beacon_raw (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owner : Nat) (raw : Pqxdh.Bytes) :
    record (n := n) setup wire reserve route (.inr (owner, .inr raw)) source =
      RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeExperiment.record setup (canonicalWire wire) route (.inr (owner, .inr raw)) source) := by
  funext before
  cases selected : before.beacons[owner]? with
  | none =>
      simp only [record, RegistrationNativeExperiment.record, RegistrationNativePlatformExperiment.liftNative,
        StateT.run, selected, RegistrationNativePlatformMldsaProgram.lift_coins, platform_lift_pure]
  | some beacon =>
      let original : StateT (PqxdhRecordLiftWorld.State n) ProbComp (core.option.Option RawCtxWholeOwner.Decrypted) :=
        CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical (ledgerCodec wire)) route
          (.inr (.inr (.inr (beacon.worldOwner, .inr raw))))
      have moved : world (source := source) (KemSK := KemSK)
          (RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserve route
            (.inr (.inr (.inr (beacon.worldOwner, .inr raw))))) =
          world (RegistrationNativePlatformOrdinaryWorld.liftWorld original) := by
        simpa only [RegistrationNativePlatformOrdinaryLower.terminal, original] using
          congrArg (world (source := source) (KemSK := KemSK))
            (RegistrationNativePlatformOrdinaryLower.actual_query setup (ledgerCodec wire) reserve route
              (.inr (.inr (.inr (beacon.worldOwner, .inr raw)))))
      have full := congrFun (moved.trans (world_lift original)) before
      simpa only [record, RegistrationNativeExperiment.record, RegistrationNativePlatformExperiment.liftNative,
        StateT.run, selected, ledger_canonical, original] using full

def terminal (native : QueryImpl RegistrationNativeRawAdapter.TypedSpec (M n KemSK source Platform))
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (M n KemSK source Platform)
  | .inr (.serverSend keyId plaintext) => after reserve (native (.inr (.serverSend keyId plaintext)))
  | .inr (.beaconSend owner plaintext) => after reserve (native (.inr (.beaconSend owner plaintext)))
  | query => native query

/-- The final runtime callback is the exact corrected registration callback with its derived ordinary public publication gates. No callback or private poststate is replaced by a security premise. -/
theorem handler_terminal [primitives : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer =
    terminal (RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks (canonicalWire wire)
      route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer) reserveFrame := by
  funext query
  cases query with
  | inl coin => rfl
  | inr query => cases query with
    | serverSend keyId plaintext =>
        exact server_send setup wire reserveFrame route keyId plaintext
    | beaconSend owner plaintext =>
        exact beacon_send setup wire reserveFrame route owner plaintext
    | serverRaw raw =>
        exact server_raw setup wire reserveFrame route raw
    | beaconRaw owner raw =>
        exact beacon_raw setup wire reserveFrame route owner raw
    | _ => rfl

/-- The original hidden-bit/fresh-message ledger continues only after the actual runtime writer gate, retaining the same whole Native state and persistent platform state. -/
theorem run_terminal [primitives : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before =
      (simulateQ (terminal (RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks
        (canonicalWire wire) route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer) reserveFrame)
        (RegistrationNativeFullCompiler.compile setup.source.crypto (canonicalWire wire) created.server.server.metadata.sender bounds mode work)).run before := by
  unfold RegistrationNativePlatformOrdinaryExperiment.run
  rw [handler_terminal]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.server_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.server_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.server_raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.beacon_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.beacon_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.beacon_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.beacon_raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.run_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting.run_terminal
