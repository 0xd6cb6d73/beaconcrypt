-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInterface
import BeaconcryptCore.Computational.PqxdhRecordLiftInterface

/-! The native registration environment has the existing record-world capability boundary and an ML-pin-aware creation command. It receives no hidden seed, record-state lens or secrecy-ledger read. A tagged public metadata mailbox transports its extra creation pin through the old environment interface so the existing fresh-message symmetry theorem can be reused. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyInterface
open RegistrationNativeInterface (Command eraseCommand)
open PqxdhRecordLiftInterface (EnvEffects)

def IsEnvironment (command : Command) : Prop :=
  PqxdhRecordLiftInterface.IsEnvironment (eraseCommand command)

abbrev EnvQuery := { query : Command // IsEnvironment query }
abbrev EnvSpec : OracleSpec EnvQuery := fun query => RegistrationNativeInterface.CommandSpec query.val

structure Environment (n : Nat) (E : Type) where
  start : ProbComp (Option (PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize) × E))
  step : QueryImpl EnvSpec (StateT E (OracleComp (EnvEffects n)))

inductive Transport where
  | metadata (mlPin : Pqxdh.Bytes)
  | hmac (message : Pqxdh.Bytes)
  deriving DecidableEq

def metadata (mlPin : Pqxdh.Bytes) : Pqxdh.Bytes := 0 :: mlPin
def userHmac (message : Pqxdh.Bytes) : Pqxdh.Bytes := 1 :: message

def decode : Pqxdh.Bytes → Option Transport
  | [] => none
  | tag :: rest => if tag = 0 then some (.metadata rest) else
      if tag = 1 then some (.hmac rest) else none

/-- Every native creation replaces the mailbox, including malformed pins later rejected by the native controller. -/
theorem decode_metadata (mlPin : Pqxdh.Bytes) : decode (metadata mlPin) = some (.metadata mlPin) := by
  simp [metadata, decode]

/-- Native public HMAC calls always carry a different transport tag, for arbitrary attacker-chosen message bytes. -/
theorem decode_userHmac (message : Pqxdh.Bytes) : decode (userHmac message) = some (.hmac message) := by
  simp [userHmac, decode]

/-- User HMAC inputs cannot invoke the creation metadata transport. -/
theorem tags_distinct (mlPin message : Pqxdh.Bytes) : metadata mlPin ≠ userHmac message := by
  simp [metadata, userHmac]

/-- Metadata transport retains all literal ML pin bytes. -/
theorem metadata_injective : Function.Injective metadata := by
  intro first second same
  exact (List.cons.inj same).2

/-- Public HMAC transport retains the entire original message. -/
theorem userHmac_injective : Function.Injective userHmac := by
  intro first second same
  exact (List.cons.inj same).2

end BeaconcryptCore.Computational.RegistrationNativeEntropyInterface

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyInterface.decode_metadata' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyInterface.decode_metadata
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyInterface.decode_userHmac' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyInterface.decode_userHmac
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyInterface.tags_distinct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyInterface.tags_distinct
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyInterface.metadata_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyInterface.metadata_injective
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyInterface.userHmac_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyInterface.userHmac_injective
