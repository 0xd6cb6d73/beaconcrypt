-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyInterface

/-! The old record environment executes the actual native registration callback. The mailbox stores only public ML pin bytes and is overwritten by every native creation marker. All user HMAC requests are tagged separately; malformed old transport messages have a harmless total interpretation outside the compiler image. No metadata operation invokes a cryptographic HMAC or a record capability. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyPort
open RegistrationNativeEntropyInterface (Environment decode metadata userHmac)
open PqxdhRecordLiftInterface (EnvEffects)
open PqxdhSecretInputKdf (HmacBlock zeroSalt)
variable {n : Nat} {E : Type}

abbrev State (E : Type) := Pqxdh.Bytes × E

def native (env : Environment n E) (query : RegistrationNativeEntropyInterface.EnvQuery) :
    StateT (State E) (OracleComp (EnvEffects n)) (RegistrationNativeEntropyInterface.EnvSpec.Range query) :=
  fun before => (fun result => (result.1, (before.1, result.2))) <$> (env.step query).run before.2

def step (env : Environment n E) : QueryImpl PqxdhRecordLiftInterface.EnvSpec
    (StateT (State E) (OracleComp (EnvEffects n)))
  | ⟨.create edPin keyId, _⟩ => fun before =>
      (fun result => (result.1, (before.1, result.2))) <$>
        (env.step ⟨.create edPin before.1 keyId, trivial⟩).run before.2
  | ⟨.bundle owner, _⟩ => native env ⟨.bundle owner, trivial⟩
  | ⟨.accept raw, _⟩ => native env ⟨.accept raw, trivial⟩
  | ⟨.build session payload, _⟩ => native env ⟨.build session payload, trivial⟩
  | ⟨.finish owner raw, _⟩ => native env ⟨.finish owner raw, trivial⟩
  | ⟨.hmac key message, _⟩ => match decode message with
      | some (.metadata mlPin) => fun before => pure (zeroSalt, (mlPin, before.2))
      | some (.hmac original) => native env ⟨.hmac key original, trivial⟩
      | none => pure zeroSalt
  | ⟨.hash _, impossible⟩ => False.elim impossible
  | ⟨.serverSend _ _, impossible⟩ => False.elim impossible
  | ⟨.serverRaw _, impossible⟩ => False.elim impossible
  | ⟨.beaconSend _ _, impossible⟩ => False.elim impossible
  | ⟨.beaconRaw _ _, impossible⟩ => False.elim impossible

def environment (env : Environment n E) : PqxdhRecordLiftInterface.Environment n (State E) :=
  ⟨(fun born => born.map fun result => (result.1, ([], result.2))) <$> env.start, step env⟩

/-- Metadata transport only overwrites public mailbox bytes; it has no primitive or World effects. -/
theorem metadata_run (env : Environment n E) (key : HmacBlock) (mlPin : Pqxdh.Bytes) (before : State E) :
    (step env ⟨.hmac key (metadata mlPin), trivial⟩).run before = pure (zeroSalt, (mlPin, before.2)) := by
  simp only [step, RegistrationNativeEntropyInterface.decode_metadata, StateT.run]

/-- A tagged native HMAC invokes the unchanged actual native callback with its original key/message. -/
theorem hmac_run (env : Environment n E) (key : HmacBlock) (message : Pqxdh.Bytes) (before : State E) :
    (step env ⟨.hmac key (userHmac message), trivial⟩).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        (env.step ⟨.hmac key message, trivial⟩).run before.2 := by
  simp only [step, RegistrationNativeEntropyInterface.decode_userHmac, native, StateT.run]

/-- The subsequent create forwards both literal pins and the current native state, retaining every failed callback's poststate. -/
theorem create_run (env : Environment n E) (edPin mlPin : Pqxdh.Bytes) (keyId : U64) (before : E) :
    (step env ⟨.create edPin keyId, trivial⟩).run (mlPin, before) =
      (fun result => (result.1, (mlPin, result.2))) <$>
        (env.step ⟨.create edPin mlPin keyId, trivial⟩).run before := rfl

/-- Two consecutive creation markers use the latest value, so a rejected create cannot leave a stale queued pin for the next one. -/
theorem metadata_overwrite (env : Environment n E) (first second : Pqxdh.Bytes) (before : State E) :
    (do
      let _ ← step env ⟨.hmac zeroSalt (metadata first), trivial⟩
      step env ⟨.hmac zeroSalt (metadata second), trivial⟩).run before =
        pure (zeroSalt, (second, before.2)) := by
  simp only [StateT.run_bind, metadata_run, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativeEntropyPort

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyPort.metadata_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyPort.metadata_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyPort.hmac_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyPort.hmac_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyPort.create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyPort.create_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyPort.metadata_overwrite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyPort.metadata_overwrite
