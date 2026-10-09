# Fresh private commitments after cache discard

`PqxdhRecordFactsPrivateCacheFresh` proves four exact local facts for the cache-discard construction. They expose the literal commitment sample and its full poststate. They do not yet prove that every source seal reaches a missing suffix.

`raw_cache` states that an erased raw receive preserves its entire private suffix dictionary, whether parsing succeeds or fails. The receive still performs the previously retained replay answer and history updates. This concerns the erased endpoint; the original endpoint can perform the discarded completion addressed by the separate observation law.

`privateAccess_fresh` assumes that the queried suffix is absent from the current cache and identifies the entire operation with one uniform 64-byte digest followed by its literal cache insertion and private-input log entry. Local nonce, seal and attempt histories and the shared public ROM remain exact. This is an operational cache-miss fact, with the missing-point premise explicit.

`sealing_fresh` gives the replay sealing computation when its nonce is unused and its actual real-AEAD tag suffix is missing. The original real ciphertext body and tag are computed first, and then one whole digest is sampled and recorded. `randomSealing_fresh` uses the corresponding premise for every possible sampled tag and retains the original order: random body of the plaintext length, random 16-byte tag, then random 64-byte commitment. Both equalities include the actual successful-seal dictionary, used nonce, private-input log, updated private cache and unchanged shared ROM.

The whole poststate appears on each right side, so any later continuation may be applied to these equalities. In particular, no assertion of independence after conditioning on a writer's return value is made. The literal seal is recorded before the external writer's possible failure, as in the separate service compiler proof. The source-level invariant that an unattempted coordinate has an empty private cache must still be proved and combined with `PqxdhRecordLiftProtocolHistory.program_fresh`; none of these four local facts substitutes that desired invariant as a cryptographic assumption.

All four statements have exact guarded axiom checks using only `propext`, `Classical.choice` and `Quot.sound`; the focused Lean 4.34 check has no diagnostics. These facts introduce no new primitive, codec or deployment contract. Query costs remain those of the counted source and separately constructed reductions. No global collision, origin or binding bound is claimed here.
