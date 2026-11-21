-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted

/-! Internal source transcript evidence, to be discharged by the actual ledger induction. No security contract is introduced. -/
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsBindingLedger
open PqxdhRecordLiftIdeal PqxdhRecordFactsBindingKnown
open PqxdhRecordFactsOriginAccepted PqxdhRecordFactsOriginPublished
open PqxdhDeploymentInterface (Handle Entry Receiver)
variable {n : Nat} {Reader Response : Type}

/-- Exact source facts about the final transcript and private state. The protocol proof must derive this invariant from its literal execution. -/
structure LedgerEvidence (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (transcript : List Entry) : Prop where
  accepted : ∀ entry ∈ transcript, ∀ (receiver : Receiver) (raw : Pqxdh.Bytes)
    (opened : RawCtxWholeOwner.Decrypted) (handle : Handle),
    entry.received = some (receiver, raw, .Some opened) →
    receivingHandle route receiver raw = some handle →
    Accepted codec control secret handle raw opened
  published : ∀ entry ∈ transcript, ∀ (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted),
    entry.published = some (handle, encrypted) → Published codec control secret handle encrypted
  knownReceived : ∀ entry ∈ transcript, ∀ (receiver : Receiver) (raw : Pqxdh.Bytes)
    (opened : RawCtxWholeOwner.Decrypted) (handle : Handle),
    entry.received = some (receiver, raw, .Some opened) →
    receivingHandle route receiver raw = some handle →
    PqxdhRecordLiftFlat.KnownAt control handle → SharedRecord codec secret raw
  knownPublished : ∀ entry ∈ transcript, ∀ (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted),
    entry.published = some (handle, encrypted) →
    PqxdhRecordLiftFlat.KnownAt control handle → SharedRecord codec secret encrypted.ciphertext

end BeaconcryptCore.Computational.PqxdhRecordFactsBindingLedger
