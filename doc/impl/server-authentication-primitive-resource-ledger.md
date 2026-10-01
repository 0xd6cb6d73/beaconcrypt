# Ordinary primitive resource ledger for the authentication bound

`PqxdhServerAuthCtxPrimitiveResources` charges the two exact ordinary reductions used in `PqxdhServerAuthCtxObserverEvent.ctxLoss`: `validation` for modified nonce-AEAD IND$ and `integrity` for modified nonce-AEAD INT-CTXT. It consumes the original client's already discharged source and ordinary-interface bounds. No replacement reduction, target guess, cryptographic premise or new protocol capability is introduced.

Use the existing source bill `U = entryReductionBudget caps qCoin Q qHash qH`, and put `H = U + 76`. `U` contains all actual context, prefix, table, public evaluation and KEM/direct/base work. The source client and its observed ordinary reduction have explicit uniform and shared-hash caps `H`, selected-seal cap one and raw-attempt cap one. This module defines

```text
B = primitiveUniformBudget caps qCoin Q qHash qH
  = H + 64*(H + 1 + 1).
```

The additional factor64 accounts for digest sampling in the ordinary CTX simulation: all public shared-hash requests, the selected source seal and the selected raw attempt remain counted. Source API caps do not make this simulated randomness free.

## Actual primitive requests and challengers

`primitive_bills` instantiates the existing primitive-query theorems with the exact `Event.validation` and `Event.integrity` definitions. Validation's main program has at most `B` uniform draws and two attempted primitive seal/encryption requests: at most one source seal and one added candidate-key validation encryption. The latter is part of the same ordinary IND$ oracle interface; it is not an uncounted extra challenge. Integrity's main program has at most `B` uniform draws and one attempted seal. It uses the actual index-zero reduction because the original client has at most one raw attempt.

The ordinary adversary specification has only uniform and seal queries; neither reduction obtains a primitive opening oracle. The existing INT-CTXT endpoint returns one forgery and applies its single final `aeadOpen` in `ModifiedNonceAeadINTCTXTWin`, together with its exact full-tuple freshness test. These interface facts are the existing endpoint definition, not a new primitive implementation proof. Candidate-key validation performs its existing deterministic local check; this work remains in the program and is not counted as a challenger opening query.

`real_game_uniform` accounts for the actual real challengers. Each samples its own 32-byte key before running the constructed reduction. The complete real IND$ experiment and the complete INT-CTXT pre-verification game therefore have uniform cap `32 + B`. Final INT verification is deterministic primitive work under the existing contract and adds no random request. No claim about runtime follows from this uniform-query bound.

## Random ciphertext bytes remain separately charged

The random IND$ challenger samples ciphertext body bytes whose number depends on submitted plaintext length. Four source query-count caps alone do not bound those bytes. The weighted `AdaptiveCtxDynamicKnownBounds.PlaintextBound` counts every selected seal's submitted plaintext length along every possible branch, including attempted requests; known-key local encryption does not submit plaintext to the selected primitive challenger.

`monitor_plaintext` proves that retaining exact replies and attempt-time history preserves this weighted metric for every adaptive client and initial observer state. `observer_plaintext` proves the same for the actual final observer decision. These are exact equivalences of query bounds, independent of source execution success or freshness.

`validation_random_uniform` consumes a stated weighted bound `qBytes` for the exact original `CtxExperiment.client`. It transfers that bound through the actual observer and known-key wrapper, then applies the existing ordinary random-game bound. The result is `B + qBytes + 32`: all source/digest randomness, all submitted body bytes and at most two 16-byte tags. The added validation probe has empty plaintext, so it adds a tag but no body bytes. The random endpoint samples no hidden encryption key, so its final32 is tag randomness, not the real endpoint's key draw.

This weighted premise is a resource obligation on the concrete source client, not a security assumption. Its source discharge from the actual builder's checked `8 + payload.length ≤ Usize.max` overflow gate and the one-selected-seal control is a separate consumer. Until that consumer is applied, this module does not advertise an unconditional source-derived plaintext-byte cap or a random-game bound based only on API query counts.

| Exact endpoint | Uniform work | Primitive encryption/seal requests | Opening interface |
| --- | --- | --- | --- |
| Validation reduction main | `B` | at most `2` | no opening oracle |
| Integrity reduction main | `B` | at most `1` | no opening oracle; one final forgery verification |
| Real validation challenger | `32 + B` | same validation requests | unchanged |
| Integrity pre-verification game | `32 + B` | same integrity requests | final verification remains explicit |
| Random validation challenger | `B + qBytes + 32` | same validation requests | unchanged |

## Scope and validation

The source context and all four original adversary caps remain those of the approved `revealSeed=false` experiment. Restricted programmable Extract and shared CTX/BLAKE2b ROM contracts, the joint-use interface and the abstract codec/compiler boundary remain unchanged. Primitive implementations, serialization implementation, snapshots and persistence are excluded. The module adds no security loss, primitive assumption, session factor or record-selection factor; it supplies resource bounds for the same reductions already present in the final probability inequality.

The topic starts at the reviewed event checkpoint `559180b06ab8d104bd82ef5cad0a192001a25b23` and carries the exact `CtxResources` module and guide from `343be950a8923dd8b02b99ad01f58c6ef683f5d6`. All five new public statements have guarded standard-only axiom reports; the eleven dependency guards are unchanged. Focused checks and independent semantic review precede publication. Central imports and inventory remain the reviewed integration's responsibility.
