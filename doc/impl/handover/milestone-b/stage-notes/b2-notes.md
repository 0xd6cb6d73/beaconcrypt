# Stage B2 notes: `Computational/PqxdhServerAuthAssumptions`

Module: `/tmp/bc-arc-scratch/c-work/b2/PqxdhServerAuthAssumptions.lean` (237 lines), namespace `BeaconcryptCore.Computational.PqxdhServerAuthAssumptions`. Imports: `BeaconcryptCore.Computational.PqxdhJointGapDh` and `BeaconcryptCore.Model.Pqxdh.ResponseEncodingAlias` (both already built). No tracked file of the worktree was edited, and no state-changing git command was run.

## Compile

Command, serialized through `/tmp/bc-arc-scratch/lean.lock`:

```
cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean && flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean /tmp/bc-arc-scratch/c-work/b2/PqxdhServerAuthAssumptions.lean
```

Result: exit 0, no errors, no warnings, no output apart from lake's two "local changes" notices for the Hax and aeneas packages (all 14 `#guard_msgs` blocks match). Wall clock about 3 to 4 s, peak RSS about 3.9 GB. Log: `compile-final.out`.

## Declarations

Definitions (3):

- `X25519ClassLaw (c : Pqxdh.Crypto) : Prop := ∀ a left right, c.x25519 a left = c.x25519 a right → Pqxdh.ResponseEncodingAlias.SameDhReplies c left right` (verbatim from design 6.3 and `ClassLawCheck.lean`).
- `classEquivalence c law joint secretOfSeed wiring reference : PeerEquivalence joint` (same relation: equal `sourceScalarDh c reference`).
- `serverGapDhAdvantage c joint secretOfSeed wiring adversary : ℝ≥0∞ := PqxdhJointGapDh.advantage joint (sourceInterface c joint secretOfSeed wiring) adversary`. It reuses the existing game; no new game is defined.

Theorems (13), with axioms:

| Theorem | Statement (short) | Axioms |
| --- | --- | --- |
| `class_iff` | under the law, `x25519 a l = x25519 a r ↔ x25519 b l = x25519 b r` | none |
| `optional_inj` | the zero-rejecting optional view determines the raw bytes | `propext` |
| `optional_congr` | equal raw bytes give equal optional views | none |
| `sourceScalarDh_eq_iff` | `sourceScalarDh c a l = sourceScalarDh c a r ↔` raw outputs equal | `propext` |
| `sourceDhReply_eq_iff` | same for `sourceDhReply` (converted static secret) | `propext` |
| `static_iff` | `joint.staticDh seed l = joint.staticDh seed r ↔ sourceScalarDh c a l = sourceScalarDh c a r` (law, wiring) | `propext` |
| `scalar_iff` | `sourceScalarDh c b l = sourceScalarDh c b r ↔ sourceScalarDh c a l = sourceScalarDh c a r` (law) | `propext` |
| `classEquivalence` (def, guarded) | instance of `PeerEquivalence` | `propext` |
| `scalar_agreement` | `(sourceInterface …).dh a ((sourceInterface …).publicKey b) = (sourceInterface …).dh b ((sourceInterface …).publicKey a)` | `propext` |
| `sourceScalarDh_nonzero` | `sourceScalarDh c a p = some v → v ≠ zeroDh` | `propext` |
| `honest_accepts` | `PqxdhJointGapDh.wins (joint.staticDh seed ((sourceInterface …).publicKey scalar)) (some value) = true ↔ sourceScalarDh c scalar (joint.publicKeys seed).convertedX25519 = some value` | `propext` |
| `honest_candidate` | Beacon DH1 `= some value` and `value ∈ candidates` give the `candidateGame` success condition `∃ target, joint.staticDh seed (publicKey scalar) = some target ∧ target ≠ zeroDh ∧ target ∈ candidates` | `propext` |
| `serverGapDhAdvantage_eq` | `serverGapDhAdvantage … adversary = Pr[= true \| PqxdhJointGapDh.game joint (sourceInterface …) adversary]` (rfl) | `propext, Classical.choice, Quot.sound` |
| `candidate_eq_serverGapDh` | `Pr[= true \| candidateGame joint (sourceInterface …) client] = serverGapDhAdvantage … (extractor client)` | `propext, Classical.choice, Quot.sound` |

Guards: 14 repository-form guards (13 theorems plus `classEquivalence`). No `sorry`, `axiom` or `native_decide`. The class law is a `Prop` premise only.

## Deviations from the design and why

1. `NonzeroHonestDh` is not added (the B2 row lists it as "definition only, flagged"), and `X25519ScalarSpread` is not added, as instructed: the owner has not approved them.
2. `honest_accepts` has no statement in the design (only its name in the B2 row). I read it as the fact step A1 needs: the Gap-DH game on `sourceInterface` counts a guess as a win exactly when it is the Beacon's honestly computed DH1 (`agreement` plus the zero-rejecting optional view). `honest_candidate` is the form A1 uses directly (`candidateGame`'s success condition, with the nonzero side condition discharged). Neither needs the class law or `NonzeroHonestDh`. If the design intended something else (for example, that honest keys pass `serverDomain.accepts`), that version would need `NonzeroHonestDh`, which is not approved.
3. Helper lemmas added beyond the listed names: `class_iff`, `optional_inj`, `optional_congr`, `sourceScalarDh_eq_iff`, `sourceDhReply_eq_iff` (these replace the scratch's `optional_raw`, `optional_eq`, `scalar_raw`, `scalar_of_raw` with iff forms), `sourceScalarDh_nonzero`, `serverGapDhAdvantage_eq` and `candidate_eq_serverGapDh` (a restatement of the existing `candidate_success_eq_advantage` for this instance, for B6 step A3).
4. `serverGapDhAdvantage` takes `(c, joint, secretOfSeed, wiring)` rather than a `Setup`, because `Setup` is defined only in B4a. B4a's callers pass `s.source.crypto`, `s.joint`, `s.secretOfSeed` and `s.wiring`.
5. Docstring wording of `serverGapDhAdvantage` follows the task instructions, not design section 6.1: it states Gap-DH (anchored two-sided strong CDH) for libsodium's X25519 function treated as a black box, with decision services on every 32-byte input the function accepts; the plausibility sentence cites only Signal's PQXDH specification, Okamoto-Pointcheval (PKC 2001) and Abdalla-Bellare-Rogaway (CT-RSA 2001). It contains no twist remark and nothing about libsodium's point validation, and it says the module does not claim that textbook Gap-DH implies the assumption. When the owner settles the twist remark, only this docstring (and the module docstring's fourth paragraph if desired) needs editing.
6. The class-law plausibility note follows the owner's short form (equal outputs under one clamped scalar imply the peers agree up to negation and a small-order torsion point, which every clamped scalar maps identically; RFC 7748), plus design 6.3 item 5 (the law quantifies over all byte lengths because the abstract function does). The full item-by-item argument of design 6.3 is not copied into the Lean docstring; it belongs in the B11 documentation.
7. `set_option linter.deprecated false in` precedes `serverGapDhAdvantage_eq` and `candidate_eq_serverGapDh`, as in `PqxdhFirstRecordKeyBound` and `PqxdhHypothesisWitness`, because VCVio deprecates the `Pr[= … | …]` notation that the existing `PqxdhJointGapDh.advantage` and `candidate_success_eq_advantage` use.
8. Size is 237 lines, below the 300-400 estimate, because `NonzeroHonestDh` and the spread law are out of scope.

## Meaning check (scratch, not for the repository)

`/tmp/bc-arc-scratch/c-work/b2/B2MeaningCheck.lean` compiles (exit 0): the verbatim class law holds for the existing F6 toy `PqxdhHypothesisWitness.toyCrypto` (constant-zero X25519), so the premise is satisfiable together with every `Pqxdh.Crypto` law; and `law_restricts` shows that a non-constant function (`fun a p => if a = [] then [] else p`) violates the law's shape, so the law is a real restriction.

## Integration left for the main agent (tracked files, not edited here)

- Copy the module to `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhServerAuthAssumptions.lean`.
- Add `import BeaconcryptCore.Computational.PqxdhServerAuthAssumptions` to `BeaconcryptCore.lean`, and add the module to `check-inventory.sh` and `reviewed-inventory.txt` (merged once per wave, per design section 7).
- Documentation (B11): the class law as a functional contract and the Gap-DH term in both assumption lists, with the owner's final twist wording.
