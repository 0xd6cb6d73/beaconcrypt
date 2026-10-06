-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule
import BeaconcryptCore.Computational.RawCtxServerMixed
import BeaconcryptCore.Computational.RawCtxBeaconLifecycle

/-! Adversary interface of the common deployment experiment (CE-1, the subset used by the CE-3 trial). One generated Server and dynamically created Beacons answer raw registration commands, the two restricted random oracles of route R1, and record send and raw receive on every installed Server peer and every Beacon owner. `create` takes raw pin bytes; a pin of the wrong width is rejected before any draw. There is no reveal command, no public getter, no snapshot API and no secrecy command in this subset; `test` and `fresh` are later send wrappers. Raw receive replies carry the actual optional plaintext (observation mode O); mode P is the success-bit wrapper `observe`. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentInterface
open PqxdhServerAuthExperiment
open PqxdhBeaconPhase2Preparation (Word32)

/-- Public commands: Beacon construction from raw pin bytes, the Beacon bundle, Server accept and build, Beacon finish, the public HMAC and BLAKE2b oracles, and record send and raw receive on a Server peer key ID or a Beacon owner handle. -/
inductive Command where
  | create (pin : Pqxdh.Bytes) (keyId : Std.U64)
  | bundle (owner : Nat)
  | accept (raw : Pqxdh.Bytes)
  | build (session : Nat) (payload : Option Pqxdh.Bytes)
  | finish (owner : Nat) (raw : Pqxdh.Bytes)
  | hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
  | hash (bytes : Pqxdh.Bytes)
  | serverSend (keyId : Std.U64) (plaintext : Pqxdh.Bytes)
  | serverRaw (raw : Pqxdh.Bytes)
  | beaconSend (owner : Nat) (plaintext : Pqxdh.Bytes)
  | beaconRaw (owner : Nat) (raw : Pqxdh.Bytes)

/-- Replies in observation mode O: an optional owner handle, the optional bundle, the optional session handle, the optional Phase 2 response, the optional application payload, an HMAC block, a BLAKE2b digest, optional record ciphertexts and the actual optional decrypted record. -/
abbrev CommandSpec : OracleSpec Command
  | .create _ _ => Option Nat
  | .bundle _ => Option Pqxdh.Bytes
  | .accept _ => Option Nat
  | .build _ _ => Option PqxdhServerRegistrationPublication.Response
  | .finish _ _ => Option Pqxdh.Bytes
  | .hmac _ _ => PqxdhSecretInputKdf.HmacBlock
  | .hash _ => CtxRomAuth.CtxDigest
  | .serverSend _ _ => Option RawCtxSourceSend.Encrypted
  | .serverRaw _ => core.option.Option RawCtxWholeOwner.Decrypted
  | .beaconSend _ _ => Option RawCtxSourceSend.Encrypted
  | .beaconRaw _ _ => core.option.Option RawCtxWholeOwner.Decrypted

/-- The adversary's oracle interface in mode O: uniform coins and the commands above. -/
abbrev Spec := unifSpec + CommandSpec

/-- Replies in observation mode P: identical to mode O except that a raw receive returns only its success bit. -/
abbrev SuccessSpec : OracleSpec Command
  | .serverRaw _ => Bool
  | .beaconRaw _ _ => Bool
  | command => CommandSpec command

/-- The success bit of a raw receive reply. -/
def succeeded (reply : core.option.Option RawCtxWholeOwner.Decrypted) : Bool :=
  match reply with
  | .Some _ => true
  | .None => false

/-- Mode P is mode O behind this wrapper: every command is forwarded unchanged and a raw receive reply is reduced to its success bit. A mode P adversary therefore runs as the mode O adversary `simulateQ observe adversary`. -/
def observe : QueryImpl (unifSpec + SuccessSpec) (OracleComp Spec)
  | .inl coin => (Spec.query (.inl coin) : OracleComp Spec _)
  | .inr (.create pin keyId) => (Spec.query (.inr (.create pin keyId)) : OracleComp Spec _)
  | .inr (.bundle owner) => (Spec.query (.inr (.bundle owner)) : OracleComp Spec _)
  | .inr (.accept raw) => (Spec.query (.inr (.accept raw)) : OracleComp Spec _)
  | .inr (.build session payload) => (Spec.query (.inr (.build session payload)) : OracleComp Spec _)
  | .inr (.finish owner raw) => (Spec.query (.inr (.finish owner raw)) : OracleComp Spec _)
  | .inr (.hmac key message) => (Spec.query (.inr (.hmac key message)) : OracleComp Spec _)
  | .inr (.hash bytes) => (Spec.query (.inr (.hash bytes)) : OracleComp Spec _)
  | .inr (.serverSend keyId plaintext) => (Spec.query (.inr (.serverSend keyId plaintext)) : OracleComp Spec _)
  | .inr (.serverRaw raw) => succeeded <$> (Spec.query (.inr (.serverRaw raw)) : OracleComp Spec _)
  | .inr (.beaconSend owner plaintext) => (Spec.query (.inr (.beaconSend owner plaintext)) : OracleComp Spec _)
  | .inr (.beaconRaw owner raw) => succeeded <$> (Spec.query (.inr (.beaconRaw owner raw)) : OracleComp Spec _)

/-- The public pin parse of `create` is the 32-byte width parse of `Beacon::try_new`; it accepts exactly the 32-byte strings. -/
def parsePin (bytes : Pqxdh.Bytes) : Option Word32 :=
  toWord32 bytes

/-- A pin parses exactly when it has 32 bytes; no point check is made. -/
theorem parsePin_isSome (bytes : Pqxdh.Bytes) : (parsePin bytes).isSome = decide (bytes.length = 32) := by
  unfold parsePin toWord32
  by_cases width : bytes.length = 32 <;> simp [width]

/-- A mode P raw receive is answered by exactly one mode O raw receive, reduced to its success bit. -/
theorem observe_serverRaw (raw : Pqxdh.Bytes) :
    observe (.inr (.serverRaw raw)) = succeeded <$> (Spec.query (.inr (.serverRaw raw)) : OracleComp Spec _) := rfl

/-- The Beacon raw receive of mode P is likewise the success bit of one mode O raw receive. -/
theorem observe_beaconRaw (owner : Nat) (raw : Pqxdh.Bytes) :
    observe (.inr (.beaconRaw owner raw)) =
      succeeded <$> (Spec.query (.inr (.beaconRaw owner raw)) : OracleComp Spec _) := rfl

end BeaconcryptCore.Computational.PqxdhDeploymentInterface

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentInterface.parsePin_isSome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentInterface.parsePin_isSome

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentInterface.observe_serverRaw' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentInterface.observe_serverRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentInterface.observe_beaconRaw' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentInterface.observe_beaconRaw
