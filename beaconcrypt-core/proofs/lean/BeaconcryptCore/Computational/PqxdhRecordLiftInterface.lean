-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSecrecy
import BeaconcryptCore.Computational.PqxdhRecordLiftSeed

/-! The proposed record-lift capability boundary. This module fixes request and reply types, exact seed-kernel resolution and an open program, not a world interpreter or a security theorem. Restricted registration effects expose no hidden-state, cache or secrecy-ledger read and no record command. The exact CE secrecy wrapper runs outside those programs. CE must first prove its outstanding failed-finish erasure equality before connecting its ideal game to a future interpreter. -/
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
  | hidden (slot : Slot n)

/-- The installation operation chooses the role; a hidden reference cannot request the opposite role's kernel. -/
def hiddenKernel : Role → PqxdhRecordLiftSeed.Seed → RustM ConcreteRatchetKernel
  | .server => PqxdhRecordLiftSeed.serverKernel
  | .beacon => PqxdhRecordLiftSeed.beaconKernel

/-- Pure kernel semantics for the future private interpreter. Server installs resolve at .server and Beacon installs at .beacon. The seed assignment is not an environment input, and resolution performs no sampling or installation. -/
def resolveKernel {n : Nat} (role : Role) (seeds : Slot n → PqxdhRecordLiftSeed.Seed) :
    KernelRef n → RustM ConcreteRatchetKernel
  | .known kernel => .ok kernel
  | .hidden slot => hiddenKernel role (seeds slot)

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

/-- Inactive phase metadata may be updated without supplying an established kernel. -/
inductive InactivePhase where
  | fresh
  | freshWithCoins
  | initSent
  | aborted
  deriving DecidableEq

/-- Environment capabilities. The future interpreter must enforce vacant Server installs, legal Beacon phases and one install per slot/role, and route every hash through the record cache. No capability invokes a record command or returns hidden material or an analysis log. -/
inductive Capability (n : Nat) where
  | peerPresent (keyId : Std.U64)
  | ownerPresent (owner : Nat)
  | appendOwner (sender : Std.U64) (serverIdentity : RawCtxServerRouting.Identity)
      (phase : InactivePhase)
  | advanceOwner (owner : Nat) (phase : InactivePhase)
  | installServer (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (kernel : KernelRef n)
  | installBeacon (owner : Nat) (shell : BeaconShell) (kernel : KernelRef n)
  | hash (bytes : Pqxdh.Bytes)

abbrev CapabilitySpec (n : Nat) : OracleSpec (Capability n)
  | .peerPresent _ | .ownerPresent _ => Bool
  | .appendOwner _ _ _ => Nat
  | .advanceOwner _ _ | .installServer _ _ _ | .installBeacon _ _ _ => Bool
  | .hash _ => CtxRomAuth.CtxDigest

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

/-- The shared world coin route for startup, adversary and ledger coins. The chosen test bit is retained only in the analysis Ledger, with no direct environment read. -/
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
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    OracleComp (WorldSpec n) (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E)) := do
  let born ← simulateQ coinLift env.start
  match born with
  | none => pure none
  | some (created, initial) => do
      let _ ← (WorldSpec n).query (.inl created)
      let result ← (simulateQ (native env)
        (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds
          (asModeO mode adversary))).run initial
      pure (some (PqxdhRegistrationJointServerBirth.encode created, result))

/-- Resource categories for the actual restricted environment program. Installation rules and lazy seed sampling remain interpreter obligations, not assumptions in these costs. -/
inductive EffectKind where
  | coin
  | hash
  | administrative
  deriving DecidableEq

def effectKind {n : Nat} : (EnvEffects n).Domain → EffectKind
  | .inl _ => .coin
  | .inr (.hash _) => .hash
  | .inr _ => .administrative

/-- Startup and per-command-class resource bounds, uniformly over query bytes and rejection paths. F1/F3 installation rules and F4 lazy sampling must be implemented and proved separately; this resource predicate assumes no security or noninterference conclusion. -/
def Frame {n : Nat} {E : Type} (env : Environment n E)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat) : Prop :=
  env.start.IsTotalQueryBound startupCoins ∧
    ∀ query state kind, ((env.step query).run state).IsQueryBoundP
      (fun effect => effectKind effect = kind) (allowance (queryClass (.inl (.inr query.val))) kind)

/-- Generic parameters retain the existing CE budget and an explicit shared-hash cap. CE supplies the cap and its transport proof; neither the slot count nor a CE-wide formula is assumed here. -/
structure Caps where
  outer : Budget
  sharedHash : Nat

/-- Finite environment-effect allowance induced by the existing outer command-class budget. Startup coins are separate. This definition is not the future composition/transport theorem. -/
def Caps.envTotal (caps : Caps) (allowance : Fin 14 → EffectKind → Nat) (kind : EffectKind) : Nat :=
  Finset.univ.sum fun queryKind : Fin 14 => caps.outer.cap queryKind * allowance queryKind kind

/-- Ordinary-record derivation allowance. Test/fresh sends are already included in Budget.sends. This definition is not yet a bound theorem; failed registration receive work stays in CE before its erasure equality. -/
def Caps.derivations (caps : Caps) : Nat :=
  caps.outer.sends + 51 * caps.outer.receives

/-- Known installation semantics retain the supplied kernel exactly. -/
theorem resolveKernel_known {n : Nat} (role : Role) (seeds : Slot n → PqxdhRecordLiftSeed.Seed)
    (kernel : ConcreteRatchetKernel) :
    resolveKernel role seeds (.known kernel) = RustM.ok kernel := rfl

/-- Hidden Server semantics are exactly the existing post-sequence-one seed constructor. -/
theorem resolveKernel_server {n : Nat} (seeds : Slot n → PqxdhRecordLiftSeed.Seed)
    (slot : Slot n) :
    resolveKernel .server seeds (.hidden slot) = PqxdhRecordLiftSeed.serverKernel (seeds slot) := rfl

/-- Hidden Beacon semantics are exactly the existing post-sequence-one seed constructor. -/
theorem resolveKernel_beacon {n : Nat} (seeds : Slot n → PqxdhRecordLiftSeed.Seed)
    (slot : Slot n) :
    resolveKernel .beacon seeds (.hidden slot) = PqxdhRecordLiftSeed.beaconKernel (seeds slot) := rfl

/-- The mode-O record specification reuses the complete source Server reply. -/
theorem server_reply (query : RawCtxServerMixed.SourceSpec.Domain) :
    (RecordSpec .O).Range (.inl query) = RawCtxServerMixed.SourceSpec.Range query := by
  cases query <;> rfl

/-- The mode-O Beacon reply is exactly the source optional result, including plaintext. -/
theorem beacon_reply (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) :
    (RecordSpec .O).Range (.inr (owner, query)) = RawCtxMixedOwner.SourceSpec.Range query := by
  cases query <;> rfl

end BeaconcryptCore.Computational.PqxdhRecordLiftInterface

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.server_reply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.server_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.beacon_reply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.beacon_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.resolveKernel_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.resolveKernel_known

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.resolveKernel_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.resolveKernel_server

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.resolveKernel_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.resolveKernel_beacon
