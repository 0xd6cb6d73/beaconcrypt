-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler

/-! Public native designation uses a parsed-accept ordinal and the actual successful owner/session replies. A parsed-accept ordinal counts all decodable native accept calls, including authentication and replay rejection. It is distinct from both the raw accept ordinal and the encapsulation getter ordinal. Honest publication is witnessed by an earlier successful bundle with identical bytes; no public-key equality is treated as a birth receipt. The original fresh-message ledger is retained literally. These definitions make no claim that every changed accepted packet came from an honest bundle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeEvents
open RegistrationNativeInterface (Entry)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Handle)
variable {Value NativeState : Type}

structure Target where
  parsedAccept : Nat
  owner : Nat
  deriving DecidableEq

/-- Decodable calls count even when mandatory authentication or owned replay lookup later rejects. -/
def parsedAccept (wire : Wire) : Entry → Bool
  | ⟨.inl (.inr (.accept raw)), _⟩ => (RegistrationNativeWire.readInit wire raw).isSome
  | _ => false

def parsedAcceptCount (wire : Wire) (transcript : List Entry) : Nat :=
  (transcript.filter (parsedAccept wire)).length

/-- Membership refers to an actual earlier successful outgoing bundle, including its entire six-field native representation. -/
def PublishedBefore (owner : Nat) (raw : Pqxdh.Bytes) (before : List Entry) : Prop :=
  ∃ pre post, before = pre ++ (Entry.mk (.inl (.inr (.bundle owner))) (some raw)) :: post

/-- The designated accept actually returned its session, and decoded the exact bytes that this owner published earlier. -/
def AcceptedAt (wire : Wire) (target : Target) (transcript : List Entry) (session : Nat) : Prop :=
  ∃ before raw after,
    transcript = before ++ (Entry.mk (.inl (.inr (.accept raw))) (some session)) :: after ∧
    parsedAcceptCount wire before = target.parsedAccept ∧
    (RegistrationNativeWire.readInit wire raw).isSome ∧ PublishedBefore target.owner raw before

/-- Server peer designation follows the actual successful build response, with no equality between session and accept counters. -/
def Peer (wire : Wire) (target : Target) (transcript : List Entry) (keyId : U64) : Prop :=
  ∃ before session payload response after,
    transcript = before ++ (Entry.mk (.inl (.inr (.build session payload))) (some response)) :: after ∧
    response.keyId = keyId ∧ AcceptedAt wire target before session

/-- Owner designation requires an actual successful finish after the selected build's exact encoded response. -/
def Owner (wire : Wire) (target : Target) (transcript : List Entry) : Prop :=
  ∃ before raw application after session payload response buildPre buildPost,
    transcript = before ++ (Entry.mk (.inl (.inr (.finish target.owner raw))) (some application)) :: after ∧
    before = buildPre ++ (Entry.mk (.inl (.inr (.build session payload))) (some response)) :: buildPost ∧
    response.serialized = raw ∧ AcceptedAt wire target buildPre session

def Designated (wire : Wire) (target : Target) (transcript : List Entry) : Handle → Prop
  | .peer keyId => Peer wire target transcript keyId
  | .owner owner => owner = target.owner ∧ Owner wire target transcript

abbrev Observed (Value NativeState : Type) := Value × (RegistrationNativeLedger.State × NativeState)

/-- The exact-bundle APP subcase uses the original private message and requires an unchanged earlier bundle. It is not the full CE eligibility event. -/
def ExactBundleApp (wire : Wire) (target : Target) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) : Prop :=
  ∃ index guess entry, claim observed.1 = some (index, guess) ∧
    observed.2.1.ledger.fresh[index]? = some entry ∧
    Designated wire target observed.2.1.transcript entry.handle ∧ entry.message = guess

open Classical in
noncomputable def exactBundleAppEvent (wire : Wire) (target : Target) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) : Bool := decide (ExactBundleApp wire target claim observed)


/-- Full native APP eligibility retains the original CE verified-key designation, including changed valid packets. Native six-field decoding supplies the public classical fields; the extra ML fields remain in the native transcript. -/
def CEAppWin (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : U64)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) : Prop :=
  ∃ index guess entry, claim observed.1 = some (index, guess) ∧
    observed.2.1.ledger.fresh[index]? = some entry ∧
    (PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKid budget observed.2.1.ledger.transcript entry.handle).isSome ∧ entry.message = guess

open Classical in
noncomputable def ceAppEvent (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : U64)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) : Bool := decide (CEAppWin crypto wire serverKid budget claim observed)

end BeaconcryptCore.Computational.RegistrationNativeEvents
