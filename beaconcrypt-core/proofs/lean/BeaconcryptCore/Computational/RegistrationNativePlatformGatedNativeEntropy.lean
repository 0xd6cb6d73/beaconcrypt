-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyWorld
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy
open RegistrationNativeEntropyInterface (Environment)
open PqxdhRecordLiftInterface (WorldSpec coinLift)
variable {n : Nat} {E Failure A Value Reader Response : Type}

def reserveLift (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (amount : Nat) :
    StateT (RegistrationNativeEntropyPort.State E) ProbComp (core.result.Result Unit Failure) := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$> (reserve amount).run before.2

def post (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (query : RegistrationNativeInterface.Spec.Domain) (reply : RegistrationNativeInterface.Spec.Range query) :
    StateT E (OracleComp (WorldSpec n)) (RegistrationNativeInterface.Spec.Range query) :=
  match query with
  | .inr (.serverSend _ _) => RegistrationNativePlatformGatedRecordInterface.closed
      (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) reply)
  | .inr (.beaconSend _ _) => RegistrationNativePlatformGatedRecordInterface.closed
      (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) reply)
  | _ => pure reply

def native (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) :
    QueryImpl RegistrationNativeInterface.Spec (StateT E (OracleComp (WorldSpec n))) := fun query => do
  let reply ← RegistrationNativeEntropyWorld.native env query
  post reserve query reply

def implementation (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) :
    QueryImpl RegistrationNativeInterface.Spec
      (StateT (RegistrationNativeEntropyPort.State E) (OracleComp (WorldSpec n))) :=
  RegistrationNativePlatformGatedRecordInterface.native (RegistrationNativeEntropyPort.environment env) (reserveLift reserve) ∘ₛ
    RegistrationNativeEntropyCore.compiler

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = work before >>= fun result => next result.1 result.2 := rfl
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem gate_drop {Output : Type} (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (size : Output → Nat) (reply : Option Output) (before : RegistrationNativeEntropyPort.State E) :
    Prod.map id Prod.snd <$>
      (RegistrationNativePlatformOrdinaryGate.gate (reserveLift reserve) size reply).run before =
      (RegistrationNativePlatformOrdinaryGate.gate reserve size reply).run before.2 := by
  cases reply with
  | none => rfl
  | some value =>
      simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run, bind_apply, reserveLift,
        bind_map_left, map_bind]
      apply bind_congr
      intro result
      cases result.1 <;> simp only [pure_apply, map_pure] <;> rfl

/-- Dropping only the public ML-pin mailbox preserves the actual post-send gate and all reached environment state. -/
theorem query_drop (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (query : RegistrationNativeInterface.Spec.Domain) (before : RegistrationNativeEntropyPort.State E) :
    Prod.map id Prod.snd <$> (implementation env reserve query).run before =
      (native env reserve query).run before.2 := by
  cases query with
  | inl coin => simp [implementation, QueryImpl.compose, RegistrationNativeEntropyCore.compiler,
      RegistrationNativePlatformGatedRecordInterface.native, RegistrationNativePlatformGatedRecordInterface.post,
      native, post, PqxdhRecordLiftInterface.native, RegistrationNativeEntropyWorld.native,
      StateT.run, StateT.lift, Functor.map_map, Prod.map]
  | inr command =>
      have underlying := RegistrationNativeEntropyCore.query_drop env (.inr command) before
      cases command
      case serverSend keyId plaintext =>
        simp only [implementation, QueryImpl.compose, RegistrationNativeEntropyCore.compiler,
          simulateQ_spec_query, RegistrationNativePlatformGatedRecordInterface.native,
          native, StateT.run_bind]
        simp only [PqxdhRecordLiftInterface.native, RegistrationNativeEntropyWorld.native,
          StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
        apply bind_congr
        intro reply
        simp only [RegistrationNativePlatformGatedRecordInterface.post, post,
          RegistrationNativePlatformGatedRecordInterface.closed, StateT.run]
        simpa only [simulateQ_map, StateT.run] using congrArg (simulateQ coinLift) (gate_drop reserve (fun value => value.ciphertext.length) reply before)
      case beaconSend owner plaintext =>
        simp only [implementation, QueryImpl.compose, RegistrationNativeEntropyCore.compiler,
          simulateQ_spec_query, RegistrationNativePlatformGatedRecordInterface.native,
          native, StateT.run_bind]
        simp only [PqxdhRecordLiftInterface.native, RegistrationNativeEntropyWorld.native,
          StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
        apply bind_congr
        intro reply
        simp only [RegistrationNativePlatformGatedRecordInterface.post, post,
          RegistrationNativePlatformGatedRecordInterface.closed, StateT.run]
        simpa only [simulateQ_map, StateT.run] using congrArg (simulateQ coinLift) (gate_drop reserve (fun value => value.ciphertext.length) reply before)
      all_goals
        simpa only [implementation, QueryImpl.compose, RegistrationNativeEntropyCore.compiler, RegistrationNativeEntropyCore.implementation,
          simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformGatedRecordInterface.native,
          RegistrationNativePlatformGatedRecordInterface.post, native, post, bind_pure_comp,
          bind_assoc, pure_bind, bind_pure, StateT.run_bind, StateT.run_pure, Functor.map_map] using underlying

/-- Arbitrary adaptive native programs retain their exact World trace and full state after public mailbox erasure. -/
theorem program_drop (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (work : OracleComp RegistrationNativeInterface.Spec Value) (before : RegistrationNativeEntropyPort.State E) :
    Prod.map id Prod.snd <$> (simulateQ (implementation env reserve) work).run before =
      (simulateQ (native env reserve) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd (query_drop env reserve) work before

open RegistrationNativeEntropyExecution (result)
/-- The complete native ledger is retained around the actual stateful post-send gate. -/
theorem wrapped (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (work : OracleComp RegistrationNativeInterface.FullSpec Value)
    (before : RegistrationNativeEntropyPort.State E) :
    result <$> (simulateQ (RegistrationNativePlatformGatedRecordInterface.native
        (RegistrationNativeEntropyPort.environment env) (reserveLift reserve))
      (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds
        (RegistrationNativeEntropyCompile.compile .O work))).run before =
      (simulateQ (native env reserve) (RegistrationNativeLedger.wrap crypto codec serverKid bounds work)).run before.2 := by
  calc
    _ = Prod.map id Prod.snd <$>
        (simulateQ (RegistrationNativePlatformGatedRecordInterface.native
            (RegistrationNativeEntropyPort.environment env) (reserveLift reserve))
          (Prod.map id RegistrationNativeEntropyRestore.ledger <$>
            PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds
              (RegistrationNativeEntropyCompile.compile .O work))).run before := by
      simp only [simulateQ_map, StateT.run_map, Functor.map_map]
      rfl
    _ = Prod.map id Prod.snd <$>
        (simulateQ (RegistrationNativePlatformGatedRecordInterface.native
            (RegistrationNativeEntropyPort.environment env) (reserveLift reserve))
          (simulateQ RegistrationNativeEntropyCore.compiler
            (RegistrationNativeLedger.wrap crypto codec serverKid bounds work))).run before := by
      rw [RegistrationNativeEntropyLedger.wrap]
    _ = _ := by
      rw [← QueryImpl.simulateQ_compose]
      exact program_drop env reserve _ before

/-- Mode P retains the original test bit and full private ledger through the ML-aware post-send bridge. -/
theorem wrapped_mode (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeEntropyPort.State E) :
    result <$> (simulateQ (RegistrationNativePlatformGatedRecordInterface.native
        (RegistrationNativeEntropyPort.environment env) (reserveLift reserve))
      (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds
        (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work)))).run before =
      (simulateQ (native env reserve) (RegistrationNativeLedger.wrap crypto codec serverKid bounds
        (RegistrationNativeInterface.asModeO mode work))).run before.2 := by
  cases mode with
  | O => exact wrapped env reserve crypto codec serverKid bounds work before
  | P =>
      rw [← RegistrationNativeEntropyCompile.observation_program]
      exact wrapped env reserve crypto codec serverKid bounds (RegistrationNativeInterface.asModeO .P work) before

open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftIdeal (KeyMode CtxPrivate ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
variable {I KemSK : Type} {baseSpec : OracleSpec I}
noncomputable def program (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E) :
    OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value) :=
  (fun result => some (PqxdhRegistrationJointServerBirth.encode created, result)) <$>
    (simulateQ (native env reserve) (RegistrationNativeLedger.wrap crypto codec serverKid bounds
      (RegistrationNativeInterface.asModeO mode work))).run initial

/-- The exact initialized gated program restores native ML creation metadata without changing any callback or ledger outcome. -/
theorem program_transport (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E) :
    RegistrationNativeEntropyProgram.outcome <$>
      RegistrationNativePlatformGatedEntropyWorld.program (RegistrationNativeEntropyPort.environment env)
        (reserveLift reserve) crypto codec serverKid bounds mode
        (RegistrationNativeEntropyCompile.compile mode work) created ([], initial) =
      program env reserve crypto codec serverKid bounds mode work created initial := by
  have executed := wrapped_mode env reserve crypto codec serverKid bounds mode work ([], initial)
  have observed := congrArg (fun distribution => (fun result =>
    some (PqxdhRegistrationJointServerBirth.encode created, result)) <$> distribution) executed
  simpa only [program, RegistrationNativePlatformGatedEntropyWorld.program, RegistrationNativeEntropyProgram.outcome,
    map_bind, map_pure, bind_pure_comp, Functor.map_map, Option.map_some] using observed

noncomputable def run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) :
    ProbComp (RegistrationNativeEntropyRun.Result n E Value) :=
  (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
    CborRawRecordOriginFlatten.interpret (ctxInterpreter modes replace setup codec) codec route
      (program env reserve setup.source.crypto codec serverKid bounds mode work created initial) shell control secret

/-- The warmed full World run retains native ML pins, the original private ledger and stateful post-send failures. -/
theorem run_transport (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) :
    RegistrationNativeEntropyRun.project <$>
      RegistrationNativePlatformGatedEntropyInitial.run modes replace setup codec route
        (RegistrationNativeEntropyPort.environment env) (reserveLift reserve) serverKid bounds mode
        (RegistrationNativeEntropyCompile.compile mode work) created (((([], initial), shell), control), secret) =
      run modes replace setup codec route env reserve serverKid bounds mode work created initial shell control secret := by
  rw [RegistrationNativePlatformGatedEntropyWorld.run_flat]
  unfold run
  rw [← program_transport env reserve setup.source.crypto codec serverKid bounds mode work created initial]
  simp only [RegistrationNativeEntropyRun.project, CborRawRecordOriginFlatten.interpret,
    simulateQ_map, StateT.run_map, Functor.map_map]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.query_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.query_drop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.program_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.program_drop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.wrapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.wrapped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.wrapped_mode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.wrapped_mode

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.program_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.program_transport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.run_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy.run_transport
