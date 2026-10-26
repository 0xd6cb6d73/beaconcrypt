# Actual callback history milestone

## Obligation closed

The earlier byte trace theorem selected a Boolean sealing outcome as an action input. Its separate one-send callback theorem established coverage for a single real callback, but did not yet select all outcomes along an actual mixed history. `BoundaryExecution.lean` closes that composition obligation: callbacks may differ at every invocation and may return sealing failure according to the reached material and sequence.

## Execution and observation relation

`Action` contains the actual send/open callback along with all public inputs. `runAction` calls the established extracted `sealNext` or `receiveNext` composition with that actual callback; `runTrace` threads each actual resulting kernel into the next invocation.

`Invocation` contains all public fields: send associated data and complete plaintext, or receive wire sequence, associated data, and complete ciphertext. `byteInvocation` and `invocation` project the byte API and callback API to this same input type. The main theorem requires equality of the complete lists of these inputs. Its only existential choice at a send is the actual seal outcome annotation; no plaintext, ciphertext, associated data, target sequence, record, or observation is replaced.

`Correct` contains only primitive contracts. A successful seal callback must return the complete record selected by the byte record interpretation for the actual supplied material and associated data/plaintext; failure is unrestricted. An open callback must equal the record interpretation on the material returned by the extracted pending-material accessor, including exact optional plaintext and rejection. These equations contain no final kernel, protocol transition, trace, or desired refinement conclusion.

## Proved results

- `action_covered` selects a byte action for each actual callback invocation, retaining all public inputs and proving equality of actual extracted driver evaluations.
- `runTrace_refines` proves termination and matching byte-model observations/full related final state for every finite callback history satisfying those contracts. The induction threads the related reached kernel before selecting any later sealing outcome.
- `runTrace_observed` applies to any actual completed callback-history evaluation and returns the matching byte actions, exact input/observation equality, and `ByteKernelRefines` final state.
- `transfer_finite_property` transfers predicates over the actual invocation trace, exact observations, and represented final byte state. The byte-model property must hold for every seal-outcome schedule.

The fixed pure HKDF law, full record primitive interpretation, synchronous completion semantics, extraction/compiler boundary, and finite-property limitations are the same as in the byte trace ledger. This theorem does not verify callback implementations or model additional external effects and does not quantify over arbitrary manipulation of private pending values or persistence APIs.

## Validation and independent review

Lean 4.31.0 incremental checks and `lake.orig build BeaconcryptCore.Refinement.BoundaryExecution` pass. Guarded checks on the history and property-transfer theorems report only `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom, `sorry`, or `admit` is introduced. The ratchet workstream independently reviewed input preservation, primitive-only contracts, state-dependent callback failure selection, and final-state/observation preservation; it reported no blocking issue.
