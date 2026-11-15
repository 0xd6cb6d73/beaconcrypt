-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhEd25519EufCma

/-! The unchanged public tuple parser is independent of signing-game budgets and source ownership. It reads the three attached field messages without verifying their signatures. -/
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple

/-- The key tuple a published Phase 1 candidate carries: the messages of its three attached fields, parsed without a signature check. -/
def candidateTuple (candidate : PqxdhEd25519EufCma.Phase1Candidate) : Option PqxdhEd25519EufCma.Phase1KeyTuple := do
  let pre ← PqxdhEd25519EufCma.splitAttachedSignature candidate.preKey
  let one ← PqxdhEd25519EufCma.splitAttachedSignature candidate.oneTimeKey
  let pq ← PqxdhEd25519EufCma.splitAttachedSignature candidate.pqKey
  let prekey ← PqxdhEd25519EufCma.parsePrekeyMessage pre.2
  let oneTime ← PqxdhEd25519EufCma.parseOneTimeMessage one.2
  let pqKey ← PqxdhEd25519EufCma.parsePqMessage pq.2
  pure ⟨prekey, oneTime, pqKey⟩

end BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple
