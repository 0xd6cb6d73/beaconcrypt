-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule
import BeaconcryptCore.Computational.RawCtxServerMixed
import BeaconcryptCore.Computational.RawCtxBeaconLifecycle

/-! Adversary interface of the common deployment experiment (CE-1). One generated Server and dynamically created Beacons answer raw registration commands, the two restricted random oracles of route R1, and record send and raw receive on every installed Server peer and every Beacon owner. `create` takes raw pin bytes; a pin of the wrong width is rejected before any draw. The secrecy commands `test` (send of one of two equal-length messages under a hidden bit) and `fresh` (send of an experiment-sampled uniform message of an adversary-chosen length) name a record handle. There is no reveal command, no public getter and no snapshot API; a post-run reveal phase would be added after the run, not as a command. Raw receive replies carry the actual optional plaintext (observation mode O); mode P is the success-bit wrapper `observe`, extended to the secrecy commands by `observeFull`. The module also fixes the transcript entries and their mode projection, the record logs `Logs` (the transcript and the produced frames, with publication and receipt read from the transcript), the final output `Output`, the fourteen query classes and the budgets with the fresh-message byte budget. No security claim is made here. -/
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

/-- Observation modes: `O` returns the actual optional plaintext of a raw receive (authentication claims); `P` returns only its success bit (secrecy claims). The mode is a parameter of the game, not an adversary choice. -/
inductive Mode where
  | O
  | P
  deriving DecidableEq

/-- A record handle: a Server peer by key ID, or a Beacon by owner handle. -/
inductive Handle where
  | peer (keyId : Std.U64)
  | owner (index : Nat)
  deriving DecidableEq

/-- Secrecy commands. `test handle left right` sends `left` or `right` on the handle according to a hidden bit drawn at the first admitted test; `fresh handle length` sends an experiment-sampled uniform message of `length` bytes that the adversary never sees. -/
inductive Secrecy where
  | test (handle : Handle) (left right : Pqxdh.Bytes)
  | fresh (handle : Handle) (length : Nat)

/-- Both secrecy commands reply like a send: the optional record ciphertext. -/
abbrev SecrecySpec : OracleSpec Secrecy := fun _ => Option RawCtxSourceSend.Encrypted

/-- The complete adversary interface in mode O: coins, the commands and the secrecy commands. -/
abbrev FullSpec := Spec + SecrecySpec

/-- The complete adversary interface in mode P. -/
abbrev FullSuccessSpec := (unifSpec + SuccessSpec) + SecrecySpec

/-- The query domain shared by both modes. -/
abbrev Query := FullSpec.Domain

/-- The adversary interface of a mode. -/
abbrev ModeSpec : Mode → OracleSpec Query
  | .O => FullSpec
  | .P => FullSuccessSpec

/-- Mode P on the complete interface: `observe` on coins and commands, the secrecy commands unchanged. -/
def observeFull : QueryImpl FullSuccessSpec (OracleComp FullSpec)
  | .inl (.inl coin) => (FullSpec.query (.inl (.inl coin)) : OracleComp FullSpec _)
  | .inl (.inr (.create pin keyId)) => (FullSpec.query (.inl (.inr (.create pin keyId))) : OracleComp FullSpec _)
  | .inl (.inr (.bundle owner)) => (FullSpec.query (.inl (.inr (.bundle owner))) : OracleComp FullSpec _)
  | .inl (.inr (.accept raw)) => (FullSpec.query (.inl (.inr (.accept raw))) : OracleComp FullSpec _)
  | .inl (.inr (.build session payload)) =>
      (FullSpec.query (.inl (.inr (.build session payload))) : OracleComp FullSpec _)
  | .inl (.inr (.finish owner raw)) => (FullSpec.query (.inl (.inr (.finish owner raw))) : OracleComp FullSpec _)
  | .inl (.inr (.hmac key message)) => (FullSpec.query (.inl (.inr (.hmac key message))) : OracleComp FullSpec _)
  | .inl (.inr (.hash bytes)) => (FullSpec.query (.inl (.inr (.hash bytes))) : OracleComp FullSpec _)
  | .inl (.inr (.serverSend keyId plaintext)) =>
      (FullSpec.query (.inl (.inr (.serverSend keyId plaintext))) : OracleComp FullSpec _)
  | .inl (.inr (.serverRaw raw)) =>
      succeeded <$> (FullSpec.query (.inl (.inr (.serverRaw raw))) : OracleComp FullSpec _)
  | .inl (.inr (.beaconSend owner plaintext)) =>
      (FullSpec.query (.inl (.inr (.beaconSend owner plaintext))) : OracleComp FullSpec _)
  | .inl (.inr (.beaconRaw owner raw)) =>
      succeeded <$> (FullSpec.query (.inl (.inr (.beaconRaw owner raw))) : OracleComp FullSpec _)
  | .inr secrecy => (FullSpec.query (.inr secrecy) : OracleComp FullSpec _)

/-- A mode P adversary as the mode O adversary that runs it behind `observeFull`. -/
def asModeO {X : Type} : (mode : Mode) → OracleComp (ModeSpec mode) X → OracleComp FullSpec X
  | .O, adversary => adversary
  | .P, adversary => simulateQ observeFull adversary

/-- One transcript entry: an adversary query with its mode O reply. -/
structure Entry where
  query : Query
  reply : FullSpec.Range query

/-- The public view of a reply in a mode: mode O keeps it; mode P reduces a raw receive to its success bit. -/
def project : (mode : Mode) → (query : Query) → FullSpec.Range query → (ModeSpec mode).Range query
  | .O, _, reply => reply
  | .P, .inl (.inl _), reply => reply
  | .P, .inl (.inr (.create _ _)), reply => reply
  | .P, .inl (.inr (.bundle _)), reply => reply
  | .P, .inl (.inr (.accept _)), reply => reply
  | .P, .inl (.inr (.build _ _)), reply => reply
  | .P, .inl (.inr (.finish _ _)), reply => reply
  | .P, .inl (.inr (.hmac _ _)), reply => reply
  | .P, .inl (.inr (.hash _)), reply => reply
  | .P, .inl (.inr (.serverSend _ _)), reply => reply
  | .P, .inl (.inr (.serverRaw _)), reply => succeeded reply
  | .P, .inl (.inr (.beaconSend _ _)), reply => reply
  | .P, .inl (.inr (.beaconRaw _ _)), reply => succeeded reply
  | .P, .inr _, reply => reply

/-- A public transcript entry of a mode: the query and its projected reply. -/
structure PublicEntry (mode : Mode) where
  query : Query
  reply : (ModeSpec mode).Range query

/-- The public view of an entry. -/
def Entry.view (mode : Mode) (entry : Entry) : PublicEntry mode :=
  ⟨entry.query, project mode entry.query entry.reply⟩

/-- The receiver of a raw record attempt: the Server (which routes by the claimed sender) or a Beacon owner. -/
inductive Receiver where
  | server
  | owner (index : Nat)
  deriving DecidableEq

/-- Record logs. `transcript` holds every adversary query with its mode O reply, oldest first; `produced` holds every frame a record seal handed to the frame writer, including frames whose writer then failed, with the command that produced it. -/
structure Logs where
  transcript : List Entry
  produced : List (Command × RawCtxReceive.DecodedFrame)

/-- The ciphertext of a successfully returned record of one entry, with its handle. -/
def Entry.published (entry : Entry) : Option (Handle × RawCtxSourceSend.Encrypted) :=
  match entry with
  | ⟨.inl (.inr (.serverSend keyId _)), some encrypted⟩ => some (.peer keyId, encrypted)
  | ⟨.inl (.inr (.beaconSend owner _)), some encrypted⟩ => some (.owner owner, encrypted)
  | ⟨.inr (.test handle _ _), some encrypted⟩ => some (handle, encrypted)
  | ⟨.inr (.fresh handle _), some encrypted⟩ => some (handle, encrypted)
  | _ => none

/-- The raw record attempt of one entry with its actual optional decryption. -/
def Entry.received (entry : Entry) :
    Option (Receiver × Pqxdh.Bytes × core.option.Option RawCtxWholeOwner.Decrypted) :=
  match entry with
  | ⟨.inl (.inr (.serverRaw raw)), reply⟩ => some (.server, raw, reply)
  | ⟨.inl (.inr (.beaconRaw owner raw)), reply⟩ => some (.owner owner, raw, reply)
  | _ => none

/-- Every successfully returned record ciphertext, oldest first, from sends, tests and fresh messages. -/
def Logs.published (logs : Logs) : List (Handle × RawCtxSourceSend.Encrypted) :=
  logs.transcript.filterMap Entry.published

/-- Every raw record attempt, oldest first, with its actual optional decryption. -/
def Logs.received (logs : Logs) :
    List (Receiver × Pqxdh.Bytes × core.option.Option RawCtxWholeOwner.Decrypted) :=
  logs.transcript.filterMap Entry.received

/-- A claim of the final output. `fresh index guess` claims that `guess` is the message of the `index`-th admitted `fresh` command. -/
inductive Claim where
  | fresh (index : Nat) (guess : Pqxdh.Bytes)

/-- The adversary's final output: an optional claim and a bit (the left-or-right guess or a key-transfer decision). -/
abbrev Output := Option Claim × Bool

/-- The fourteen query classes: coin 0, create 1, bundle 2, accept 3, build 4, finish 5, HMAC 6 and BLAKE2b 7 keep source14's numbering; Server send 8, Server raw receive 9, Beacon send 10, Beacon raw receive 11, test 12 and fresh 13. -/
def queryClass : Query → Fin 14
  | .inl (.inl _) => 0
  | .inl (.inr (.create _ _)) => 1
  | .inl (.inr (.bundle _)) => 2
  | .inl (.inr (.accept _)) => 3
  | .inl (.inr (.build _ _)) => 4
  | .inl (.inr (.finish _ _)) => 5
  | .inl (.inr (.hmac _ _)) => 6
  | .inl (.inr (.hash _)) => 7
  | .inl (.inr (.serverSend _ _)) => 8
  | .inl (.inr (.serverRaw _)) => 9
  | .inl (.inr (.beaconSend _ _)) => 10
  | .inl (.inr (.beaconRaw _ _)) => 11
  | .inr (.test _ _ _) => 12
  | .inr (.fresh _ _) => 13

/-- The admitted lengths of `fresh` messages, `min ≤ length ≤ max`. -/
structure FreshBounds where
  min : Nat
  max : Nat

/-- Per-class caps on every attempt, rejected ones included. -/
structure Budget where
  coin : Nat
  create : Nat
  bundle : Nat
  accept : Nat
  build : Nat
  finish : Nat
  hmac : Nat
  hash : Nat
  serverSend : Nat
  serverRaw : Nat
  beaconSend : Nat
  beaconRaw : Nat
  test : Nat
  fresh : Nat

/-- The cap of each query class. -/
def Budget.cap (budget : Budget) : Fin 14 → Nat :=
  ![budget.coin, budget.create, budget.bundle, budget.accept, budget.build, budget.finish, budget.hmac, budget.hash,
    budget.serverSend, budget.serverRaw, budget.beaconSend, budget.beaconRaw, budget.test, budget.fresh]

/-- An adversary respects a budget when every class stays within its cap on every execution path. -/
def Budget.Respects {mode : Mode} {X : Type} (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) : Prop :=
  ∀ kind, adversary.IsQueryBoundP (fun query => queryClass query = kind) (budget.cap kind)

/-- The fresh-message byte budget: every admitted fresh message has at most `bounds.max` bytes. -/
def Budget.freshBytes (budget : Budget) (bounds : FreshBounds) : Nat := bounds.max * budget.fresh

/-- `S`: record sends, including those made by `test` and `fresh`. -/
def Budget.sends (budget : Budget) : Nat := budget.serverSend + budget.beaconSend + budget.test + budget.fresh

/-- `R`: raw record receives. -/
def Budget.receives (budget : Budget) : Nat := budget.serverRaw + budget.beaconRaw

/-- `count + 1` for the generated-seed Server: one more than the create cap (T5's `capacity` with `supplied = none`). -/
def Budget.capacity (budget : Budget) : Nat := budget.create + 1

/-- `N = qAccept · (count + 1)`: the number of designations `(session, KEM creation index)`. -/
def Budget.targets (budget : Budget) : Nat := budget.accept * budget.capacity

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


/-- Mode P observes a Server raw receive as one mode O raw receive reduced to its success bit. -/
theorem observeFull_serverRaw (raw : Pqxdh.Bytes) :
    observeFull (.inl (.inr (.serverRaw raw))) =
      succeeded <$> (FullSpec.query (.inl (.inr (.serverRaw raw))) : OracleComp FullSpec _) := rfl

/-- Mode P observes a Beacon raw receive as one mode O raw receive reduced to its success bit. -/
theorem observeFull_beaconRaw (owner : Nat) (raw : Pqxdh.Bytes) :
    observeFull (.inl (.inr (.beaconRaw owner raw))) =
      succeeded <$> (FullSpec.query (.inl (.inr (.beaconRaw owner raw))) : OracleComp FullSpec _) := rfl

/-- Mode P forwards both secrecy commands unchanged. -/
theorem observeFull_secrecy (secrecy : Secrecy) :
    observeFull (.inr secrecy) = (FullSpec.query (.inr secrecy) : OracleComp FullSpec _) := rfl

/-- Mode P projects exactly the raw receives: every other reply is public unchanged. -/
theorem project_raw (query : Query) (reply : FullSpec.Range query)
    (notRaw : ∀ raw, query ≠ .inl (.inr (.serverRaw raw)))
    (notOwnerRaw : ∀ owner raw, query ≠ .inl (.inr (.beaconRaw owner raw))) :
    HEq (project .P query reply) reply := by
  rcases query with (coin | command) | secrecy
  · rfl
  · cases command with
    | serverRaw raw => exact absurd rfl (notRaw raw)
    | beaconRaw owner raw => exact absurd rfl (notOwnerRaw owner raw)
    | _ => rfl
  · rfl

/-- The record sends of the budget are the plain sends plus the tests and fresh messages. -/
theorem sends_eq (budget : Budget) :
    budget.sends = budget.cap 8 + budget.cap 10 + budget.cap 12 + budget.cap 13 := rfl

/-- The designation count is the accept cap times the creation capacity. -/
theorem targets_eq (budget : Budget) : budget.targets = budget.cap 3 * (budget.cap 1 + 1) := rfl

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

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentInterface.observeFull_serverRaw' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentInterface.observeFull_serverRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentInterface.observeFull_beaconRaw' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentInterface.observeFull_beaconRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentInterface.observeFull_secrecy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentInterface.observeFull_secrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentInterface.project_raw' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentInterface.project_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentInterface.sends_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentInterface.sends_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentInterface.targets_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentInterface.targets_eq
