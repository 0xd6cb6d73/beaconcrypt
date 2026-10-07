-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSecrecy

/-! The proposed record-lift capability boundary. This module fixes the request and reply types and an open program, not an interpreter or a security theorem. Registration programs cannot read the world's kernels, hidden samples, cache or secrecy ledger. The exact CE secrecy wrapper runs outside those programs. A later interpreter must execute every capability, including transient registration receives, before this program is a probabilistic record-lift game. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftInterface
open PqxdhDeploymentInterface
open PqxdhServerAuthExperiment (Codec)

abbrev Slot (n : Nat) := Fin n

/-- The role determines which half of a hidden seed supplies each direction. -/
inductive Role where
  | server
  | beacon
  deriving DecidableEq

/-- Installation accepts a caller-known kernel or a reference, never returns hidden material. -/
inductive KernelRef (n : Nat) where
  | known (kernel : ConcreteRatchetKernel)
  | hidden (slot : Slot n) (role : Role)

/-- Existing source record query domains, with a dynamic owner address. -/
abbrev RecordQuery := RawCtxServerMixed.SourceSpec.Domain ⊕
  (Nat × RawCtxMixedOwner.SourceSpec.Domain)

/-- Embed a record query in the existing CE transcript without changing any bytes. -/
def recordQuery : RecordQuery → Query
  | .inl (.inl (plaintext, keyId)) => .inl (.inr (.serverSend keyId plaintext))
  | .inl (.inr raw) => .inl (.inr (.serverRaw raw))
  | .inr (owner, .inl plaintext) => .inl (.inr (.beaconSend owner plaintext))
  | .inr (owner, .inr raw) => .inl (.inr (.beaconRaw owner raw))

/-- Reply types are precisely the CE reply types of the chosen observation mode. -/
abbrev RecordSpec (mode : Mode) : OracleSpec RecordQuery :=
  fun query => (ModeSpec mode).Range (recordQuery query)

/-- Restrict the environment to registration and the public primitive interfaces. -/
def IsEnvironment : Command → Prop
  | .serverSend _ _ | .serverRaw _ | .beaconSend _ _ | .beaconRaw _ _ | .hash _ => False
  | _ => True

abbrev EnvQuery := { query : Command // IsEnvironment query }
abbrev EnvSpec : OracleSpec EnvQuery := fun query => CommandSpec query.val

/-- Public installation metadata, with the actual control's assigned ID kept separate. -/
structure BeaconShell where
  identityKeyId : Std.U64
  control : pqxdh.BeaconEstablished
  associatedData : Std.Array Std.U8 153#usize

/-- The first registration record's material belongs to the registration lane. -/
structure FirstMaterial where
  key : CtxRomAuth.CtxKey
  nonce : CtxRomAuth.CtxNonce

/-- A candidate reference has no kernel, seed, key, nonce or private opening argument. -/
structure Ticket where
  index : Nat
  deriving DecidableEq

/-- Successful transient opening replies contain only the sequence-one plaintext and a ticket. The interpreter must enforce the sequence gate before constructing this reply. -/
structure CandidateReply where
  ticket : Ticket
  plaintext : Pqxdh.Bytes

/-- Inactive phase metadata may be updated without supplying an established kernel. -/
inductive InactivePhase where
  | fresh
  | freshWithCoins
  | initSent
  | aborted
  deriving DecidableEq

/-- Environment capabilities. The interpreter owns occupancy, role-use and ticket checks. Every hash shares the record cache, and candidate rejection preserves primitive effects. No capability exposes hidden material or an analysis log. -/
inductive Capability (n : Nat) where
  | peerPresent (keyId : Std.U64)
  | ownerPresent (owner : Nat)
  | appendOwner (sender : Std.U64) (serverIdentity : RawCtxServerRouting.Identity)
      (phase : InactivePhase)
  | advanceOwner (owner : Nat) (phase : InactivePhase)
  | installServer (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (kernel : KernelRef n)
  | installBeacon (owner : Nat) (shell : BeaconShell) (kernel : KernelRef n)
  | candidate (slot : Slot n) (owner : Nat) (expectedSender : Std.U64)
      (associatedData : Std.Array Std.U8 153#usize) (first : FirstMaterial) (raw : Pqxdh.Bytes)
  | commitCandidate (ticket : Ticket) (shell : BeaconShell)
  | discardCandidate (ticket : Ticket)
  | hash (bytes : Pqxdh.Bytes)
  | privateSend (handle : Handle) (plaintext : Pqxdh.Bytes)

abbrev CapabilitySpec (n : Nat) : OracleSpec (Capability n)
  | .peerPresent _ | .ownerPresent _ => Bool
  | .appendOwner _ _ _ => Nat
  | .advanceOwner _ _ | .installServer _ _ _ | .installBeacon _ _ _ => Bool
  | .candidate _ _ _ _ _ _ => Option CandidateReply
  | .commitCandidate _ _ | .discardCandidate _ => Bool
  | .hash _ => CtxRomAuth.CtxDigest
  | .privateSend _ _ => Option RawCtxSourceSend.Encrypted

/-- Only the interpreter answers the coins used by a registration program. -/
abbrev EnvEffects (n : Nat) := unifSpec + CapabilitySpec n

/-- Private world requests additionally include initial Server installation and ordinary raw record calls. They are unavailable to the environment handler. -/
abbrev WorldSpec (n : Nat) := (PqxdhLiveServerConstruction.Created Unit →ₒ Unit) +
  (EnvEffects n + RecordSpec .O)

/-- The environment's state is supplied only to its own handler. It receives no world-state lens. This is a typed access boundary, not an assertion that all of its adaptively learned data is statistically independent of hidden material. -/
structure Environment (n : Nat) (E : Type) where
  start : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × E))
  step : QueryImpl EnvSpec (StateT E (OracleComp (EnvEffects n)))

/-- Embed restricted effects into the private world's oracle sum. -/
def effectLift {n : Nat} : QueryImpl (EnvEffects n) (OracleComp (WorldSpec n)) :=
  fun query => ((WorldSpec n).query (.inr (.inl query)) : OracleComp (WorldSpec n) _)

/-- Initial Server birth uses only ordinary uniform coins before any hidden slot exists. -/
def coinLift {n : Nat} : QueryImpl unifSpec (OracleComp (WorldSpec n)) :=
  fun coin => ((WorldSpec n).query (.inr (.inl (.inl coin))) : OracleComp (WorldSpec n) _)

/-- Lift an environment command without giving its continuation record-state access. -/
def environmentStep {n : Nat} {E : Type} (env : Environment n E) (query : EnvQuery) :
    StateT E (OracleComp (WorldSpec n)) (EnvSpec.Range query) := fun state =>
  simulateQ effectLift ((env.step query).run state)

/-- Native command dispatch is a partition of the existing CE interface. Coins and records bypass the environment, including the secret coins and sends of the CE ledger. -/
def native {n : Nat} {E : Type} (env : Environment n E) :
    QueryImpl Spec (StateT E (OracleComp (WorldSpec n)))
  | .inl coin => StateT.lift (coinLift coin)
  | .inr (.serverSend keyId plaintext) =>
      StateT.lift ((WorldSpec n).query (.inr (.inr (.inl (.inl (plaintext, keyId))))) : OracleComp (WorldSpec n) _)
  | .inr (.serverRaw raw) =>
      StateT.lift ((WorldSpec n).query (.inr (.inr (.inl (.inr raw)))) : OracleComp (WorldSpec n) _)
  | .inr (.beaconSend owner plaintext) =>
      StateT.lift ((WorldSpec n).query (.inr (.inr (.inr (owner, .inl plaintext)))) : OracleComp (WorldSpec n) _)
  | .inr (.beaconRaw owner raw) =>
      StateT.lift ((WorldSpec n).query (.inr (.inr (.inr (owner, .inr raw)))) : OracleComp (WorldSpec n) _)
  | .inr (.create pin keyId) => environmentStep env ⟨.create pin keyId, trivial⟩
  | .inr (.bundle owner) => environmentStep env ⟨.bundle owner, trivial⟩
  | .inr (.accept raw) => environmentStep env ⟨.accept raw, trivial⟩
  | .inr (.build session payload) => environmentStep env ⟨.build session payload, trivial⟩
  | .inr (.finish owner raw) => environmentStep env ⟨.finish owner raw, trivial⟩
  | .inr (.hmac key message) => environmentStep env ⟨.hmac key message, trivial⟩
  | .inr (.hash bytes) => StateT.lift (effectLift (.inr (.hash bytes)))

/-- The exact existing secrecy wrapper and mode projection, still awaiting a world interpreter. Its analysis ledger is an output for the proof, never an argument to the environment. -/
noncomputable def program {n : Nat} {E X Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    OracleComp (WorldSpec n) (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E)) := do
  let born ← simulateQ coinLift env.start
  match born with
  | none => pure none
  | some (created, initial) => do
      let _ ← (WorldSpec n).query (.inl created)
      let result ← (simulateQ (native env)
        (PqxdhDeploymentSecrecy.wrap crypto codec created.server.server.metadata.sender bounds
          (asModeO mode adversary))).run initial
      pure (some (PqxdhRegistrationJointServerBirth.encode created, result))

/-- Capability costs are explicit; the candidate cap is separate from ordinary raw receives. These are obligations on the environment's actual programs, not cryptographic assumptions. -/
inductive EffectKind where
  | coin
  | hash
  | privateSend
  | candidate
  | administrative
  deriving DecidableEq

def effectKind {n : Nat} : (EnvEffects n).Domain → EffectKind
  | .inl _ => .coin
  | .inr (.hash _) => .hash
  | .inr (.privateSend _ _) => .privateSend
  | .inr (.candidate _ _ _ _ _ _) => .candidate
  | .inr _ => .administrative

/-- Pointwise bounds on each environment command, including rejection paths. The later interpreter must independently enforce installation/ticket rules and account for primitive work inside each capability. -/
def Frame {n : Nat} {E : Type} (env : Environment n E)
    (startupCoins : Nat) (allowance : EnvQuery → EffectKind → Nat) : Prop :=
  env.start.IsTotalQueryBound startupCoins ∧
    ∀ query state kind, ((env.step query).run state).IsQueryBoundP
      (fun effect => effectKind effect = kind) (allowance query kind)

/-- Generic record-lift parameters leave unresolved CE-wide hash and transient-receive caps visible. The eventual budget transport must bound these parameters from the outer CE budget and Frame. -/
structure Caps where
  outer : Budget
  privateSends : Nat
  candidateReceives : Nat
  sharedHash : Nat

/-- Each transient candidate is a raw receive too; its internal first-record component is owned by item 2. This conservative cap includes all of its at-most-51 KDF callbacks. -/
def Caps.derivations (caps : Caps) : Nat :=
  caps.outer.sends + caps.privateSends + 51 * (caps.outer.receives + caps.candidateReceives)

/-- The mode-O record specification reuses the complete source Server reply. -/
theorem server_reply (query : RawCtxServerMixed.SourceSpec.Domain) :
    (RecordSpec .O).Range (.inl query) = RawCtxServerMixed.SourceSpec.Range query := by
  cases query <;> rfl

/-- The mode-O Beacon reply is exactly the source optional result, including plaintext. -/
theorem beacon_reply (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) :
    (RecordSpec .O).Range (.inr (owner, query)) = RawCtxMixedOwner.SourceSpec.Range query := by
  cases query <;> rfl

/-- The sequence gate discards a later plaintext before an environment continuation can see it. This gate must run after the complete candidate opening and its primitive effects. -/
def candidateReply (ticket : Ticket) : core.option.Option RawCtxWholeOwner.Decrypted → Option CandidateReply
  | .None => none
  | .Some opened => if opened.sequence = 1#u64 then some ⟨ticket, opened.plaintext⟩ else none

/-- A successful candidate reply preserves the supplied sequence-one optional plaintext. Source-opening provenance requires the interpreter's separate simulation theorem. -/
theorem candidateReply_some (ticket : Ticket) (opened : core.option.Option RawCtxWholeOwner.Decrypted)
    (reply : CandidateReply) (accepted : candidateReply ticket opened = some reply) :
    ∃ value, opened = .Some value ∧ value.sequence = 1#u64 ∧ reply = ⟨ticket, value.plaintext⟩ := by
  cases opened with
  | none => cases accepted
  | some value =>
      simp only [candidateReply] at accepted
      split at accepted
      · exact ⟨value, rfl, ‹_›, (Option.some.inj accepted).symm⟩
      · cases accepted

end BeaconcryptCore.Computational.PqxdhRecordLiftInterface

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.server_reply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.server_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.beacon_reply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.beacon_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.candidateReply_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.candidateReply_some
