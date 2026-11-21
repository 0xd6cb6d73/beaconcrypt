-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyCompile
import BeaconcryptCore.Computational.RegistrationNativeLedger

/-! The native ML-pin-aware environment uses the same private record World oracle. Coins, hash and ordinary record traffic bypass the environment; registration and public HMAC use its restricted callback. The complete original secrecy ledger remains outside it. No callback receives a ledger, seed or record-state lens. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyWorld
open RegistrationNativeEntropyInterface (Environment)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
variable {n : Nat} {E Value Reader Response : Type}

def environmentStep (env : Environment n E) (query : RegistrationNativeEntropyInterface.EnvQuery) :
    StateT E (OracleComp (WorldSpec n)) (RegistrationNativeEntropyInterface.EnvSpec.Range query) :=
  fun before => simulateQ effectLift ((env.step query).run before)

def native (env : Environment n E) :
    QueryImpl RegistrationNativeInterface.Spec (StateT E (OracleComp (WorldSpec n)))
  | .inl coin => StateT.lift (coinLift coin)
  | .inr (.serverSend keyId plaintext) =>
      StateT.lift ((WorldSpec n).query (.inr (.inr (.inl (.inl (plaintext, keyId))))) : OracleComp (WorldSpec n) _)
  | .inr (.serverRaw raw) =>
      StateT.lift ((WorldSpec n).query (.inr (.inr (.inl (.inr raw)))) : OracleComp (WorldSpec n) _)
  | .inr (.beaconSend owner plaintext) =>
      StateT.lift ((WorldSpec n).query (.inr (.inr (.inr (owner, .inl plaintext)))) : OracleComp (WorldSpec n) _)
  | .inr (.beaconRaw owner raw) =>
      StateT.lift ((WorldSpec n).query (.inr (.inr (.inr (owner, .inr raw)))) : OracleComp (WorldSpec n) _)
  | .inr (.create edPin mlPin keyId) => environmentStep env ⟨.create edPin mlPin keyId, trivial⟩
  | .inr (.bundle owner) => environmentStep env ⟨.bundle owner, trivial⟩
  | .inr (.accept raw) => environmentStep env ⟨.accept raw, trivial⟩
  | .inr (.build session payload) => environmentStep env ⟨.build session payload, trivial⟩
  | .inr (.finish owner raw) => environmentStep env ⟨.finish owner raw, trivial⟩
  | .inr (.hmac key message) => environmentStep env ⟨.hmac key message, trivial⟩
  | .inr (.hash bytes) => StateT.lift (effectLift (.inr (.hash bytes)))

noncomputable def full (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) :
    QueryImpl RegistrationNativeInterface.FullSpec
      (StateT (RegistrationNativeLedger.State × E) (OracleComp (WorldSpec n))) :=
  ((native env).mapStateTBase (RegistrationNativeLedger.handler crypto codec serverKid bounds)).flattenStateT

noncomputable def program (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    OracleComp (WorldSpec n) (Option (PqxdhRegistrationJointServerBirth.ClientCreated (Std.Array Std.U8 151#usize) ×
      (Value × RegistrationNativeLedger.State) × E)) := do
  let born ← simulateQ coinLift env.start
  match born with
  | none => pure none
  | some (created, initial) => do
      let _ ← (WorldSpec n).query (.inl created)
      let result ← (simulateQ (native env)
        (RegistrationNativeLedger.wrap crypto codec serverKid bounds
          (RegistrationNativeInterface.asModeO mode work))).run initial
      pure (some (PqxdhRegistrationJointServerBirth.encode created, result))

/-- The complete native world program executes the literal wrapped native client, preserving startup failure. -/
theorem program_start (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    program env crypto codec serverKid bounds mode work = (do
      let born ← simulateQ coinLift env.start
      match born with
      | none => pure none
      | some (created, initial) => do
          let _ ← (WorldSpec n).query (.inl created)
          let result ← (simulateQ (native env)
            (RegistrationNativeLedger.wrap crypto codec serverKid bounds
              (RegistrationNativeInterface.asModeO mode work))).run initial
          pure (some (PqxdhRegistrationJointServerBirth.encode created, result))) := rfl

/-- Every native ordinary command and its full reply is recorded outside the restricted environment. -/
theorem core_run (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.Spec.Domain)
    (before : RegistrationNativeLedger.State × E) :
    (full env crypto codec serverKid bounds (.inl query)).run before =
      (fun result => (result.1, (RegistrationNativeLedger.record before.1 ⟨.inl query, result.1⟩,
        result.2))) <$> (native env query).run before.2 := by
  rcases before with ⟨ledger, before⟩
  simp only [full, QueryImpl.flattenStateT_mapStateTBase_apply_run,
    RegistrationNativeLedger.query_forward, simulateQ_map, simulateQ_spec_query,
    StateT.run_map, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeEntropyWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyWorld.program_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyWorld.program_start
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyWorld.core_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyWorld.core_run
