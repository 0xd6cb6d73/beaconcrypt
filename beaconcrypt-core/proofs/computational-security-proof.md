# A concise paper proof of BeaconCrypt's computational security claims

This note explains the common deployment experiment's security argument in ordinary mathematics. It summarizes the existing Lean reductions; it introduces no new theorem or assumption. The claim is about the stated logical experiment, whose relationship to the current adapter is qualified below. Paths to computational modules are relative to [`lean/BeaconcryptCore/Computational/`](lean/BeaconcryptCore/Computational/).

## Statement and assumptions

Fix one honestly generated live Server, an adaptive adversary creating and scheduling Beacons within a finite command budget, and the experiment [`PqxdhDeploymentSecrecy.game`](lean/BeaconcryptCore/Computational/PqxdhDeploymentSecrecy.lean). The adversary chooses registration, messages, raw deliveries and scheduling, including attacker-owned identities. There is no honest-secret disclosure during execution. Authentication holds in both observation modes, with Beacon-side claims restricted to the protected Server's identity and key-ID pin; confidentiality uses mode P, where ordinary receives disclose success rather than plaintext. Left-or-right tests are confined to one designated session, with equal nonempty message lengths.

The bounds below use ML-KEM IND-CCA security with explicit correctness error $\delta_{\mathrm{corr}}$, HMAC-SHA-512 PRF security, the separate Extract game on a hidden uniform 32-byte input, and the record scheme's modified-nonce AEAD IND$ and INT-CTXT games. Authentication of identities uses the joint Ed25519/X25519 weak-EUF game. Authentication of the pinned Server additionally uses the twist-inclusive anchored Gap-DH game and the X25519 class/spread laws. Extract security with secret input is an additional assumption, not a consequence asserted here of ordinary HMAC PRF security.

BLAKE2b and the zero-salt HKDF-Extract operation on exactly 192-byte root inputs are shared programmable classical random oracles, consistent across honest operations and direct adversarial queries. Other public HKDF evaluations remain real. Functional premises include source HKDF correctness and prefix consistency, identity wiring, X25519 public-domain laws, functional KEM decapsulation, AEAD correctness and the named abstract codec read-back laws. The exact premise list is [the composition assumptions](https://github.com/0xd6cb6d73/beaconcrypt/blob/e9f5048b8e27144ef3648aa06b09bd063baa38d7/doc/composition-assumptions.md#common-deployment-experiment-approved-profile-and-scope-of-the-headline-claims-ce-13). No smallness of a primitive advantage is proved by Lean: the conclusions are explicit reductions to those games.

## Proof by successive games

**1. Select a target without guessing.** A claim names a session through its public transcript. Its designation is at most one pair $g=(i,k)$, where $i$ is a raw-accept ordinal and $k$ is a Beacon creation index. Write $E_g$ for an event $E$ whose claim designates $g$. The budget gives the exact disjoint decomposition

$$
\Pr[E\text{ with a designation}]=\sum_{g\in\mathcal G}\Pr[E_g],
\qquad \mathcal G=[q_{\mathrm{accept}}]\times[q_{\mathrm{create}}].
$$

Thus there is one summand per target, with no additional target-guessing factor. The source compiler preserves the complete experiment: optional failures, primitive state, counters, consumed IDs, pending tokens and the observation ledger. Rejected commands are charged too. These are [`compile_full_game`](lean/BeaconcryptCore/Computational/PqxdhDeploymentCompileSecrecy.lean) and [`split_named`](lean/BeaconcryptCore/Computational/PqxdhDeploymentHeadlineChain.lean).

**2. Hide the KEM contribution, then the root and initial material.** The exact root input is

$$
\mathtt{FF}^{32}\parallel DH_1\parallel DH_2\parallel DH_3\parallel DH_4\parallel SS_{\mathrm{KEM}}.
$$

Replace the selected encapsulation secret by a uniform 32-byte string using one ordinary KEM IND-CCA reduction, charging $\delta_{\mathrm{corr}}$ for honest decapsulation failure. Route R1 then replaces the target Server root entry and its Beacon finish entry by a lazy table indexed by their four DH coordinates. Equal inputs share a value; distinct inputs obtain independent values. Until another operation queries the hidden KEM coordinate, the original and programmed computations agree. The adaptive candidate bound is $(q_{\mathrm{accept}}+q_{\mathrm{finish}}+q_{\mathrm{hmac}})/2^{256}$. The subsequent secret-keyed Expand and uniform-input Extract hybrids produce the initial material, preserving shared inputs and output prefixes.

Consequently, for the corresponding two-slot ideal game $I_g$,

$$
\left|\Pr_{\mathrm{CE}}[E_g]-\Pr_{I_g}[E_g]\right|\le\kappa_g(E),
\qquad \kappa_g(E)=\mathrm{kemLoss}_g(E)+\mathrm{slotLoss}_g(E).
$$

Here `kemLoss` is one KEM advantage plus correctness error; `slotLoss` contains the candidate term, two root-Expand HMAC advantages and the two entries' key-schedule bounds. Each key-schedule bound has two uniform-input Extract and two HMAC advantages. This is CE-KT, a transfer of event probabilities; its ideal probability remains on the right. It does not assert a standalone root-recovery theorem. Sources: [`ce_kt_close`](lean/BeaconcryptCore/Computational/PqxdhDeploymentHeadlineKeyTransfer.lean), [`allIdeal_loss`](lean/BeaconcryptCore/Computational/PqxdhRegistrationJointKemKeyTransfer.lean) and [`fromRoot_bound`](lean/BeaconcryptCore/Computational/PqxdhKeyScheduleFromRoot.lean).

**3. Replace evolving material in chronological order.** Each ratchet step derives one 76-byte stream, partitioned as message key32, next chain32 and nonce12. The initializer uses the first 64 bytes at the same address. The proof preserves this prefix relationship and the two actual public HKDF labels; it adds no role or session domain bytes. An ordered hybrid replaces each reached derivation by uniform material, paying one uniform-input Extract advantage and one HMAC PRF advantage per index. At most $h=2n(S+51R)$ indices are needed for $n$ slots, send budget $S$ and raw-receive budget $R$; the deployment instantiation has $n=2$. The factor 51 covers bounded skipped-key derivation. Memoized values and source-history invariants handle aliases, repeated derivations and consumed keys; collision-free keys are not assumed. This is [`chain_lift`](lean/BeaconcryptCore/Computational/PqxdhRecordLiftChainLift.lean).

**4. Replace real records by ideal authenticated, then hidden records.** The CTX commitment authenticates

$$
U=H(K_{32}\parallel N_{12}\parallel AD_{281}\parallel T_{16}\parallel\mathrm{LE64}(s)\parallel\mathrm{LE64}(id)).
$$

The 357-byte encoding is injective in its fields. For a selected key, the shared hash simulation and nonce-AEAD reductions bound integrity failure by

$$
\operatorname{Adv}^{\mathrm{IND\$}}(V)+\frac{q_H}{2^{128}}
+2\sum_{r<q_{\mathrm{raw}}}\operatorname{Adv}^{\mathrm{INT\text{-}CTXT}}(F_r)
+\frac{q_{\mathrm{raw}}}{2^{512}}.
$$

Every attempted opening is included, with the displayed factor two. A further IND$ reduction hides the authenticated ciphertexts in mode P. Summing these reductions over the selected keys and adding step 3 gives the exact event-specific losses $\alpha_g(E)=\mathrm{authLoss}_g(E)$ and $\rho_g(E)=\mathrm{recLoss}_g(E)$. Their events retain the ideal-slot invariants. This is [`record_auth_lift`](lean/BeaconcryptCore/Computational/PqxdhRecordLiftComposition.lean), [`record_lift`](lean/BeaconcryptCore/Computational/PqxdhRecordLift.lean) and the loss definitions in [`PqxdhRecordLiftIdeal`](lean/BeaconcryptCore/Computational/PqxdhRecordLiftIdeal.lean).

The handoff to these record games can have a Beacon-side slot anomaly. A predict-then-compare KEM reduction bounds it by

$$
\beta_g=\operatorname{Adv}^{\mathrm{IND\text{-}CCA}}(P_g)+\delta_{\mathrm{corr}}+2^{-256}.
$$

Server-side slot conditions hold without this term. All reductions depend on the transferred event and claim; symbols for different events do not denote one interchangeable adversary.

**5. Evaluate the ideal failures and add the losses.** In the ideal authenticated world, a receive must reproduce a genuine produced record. A record whose writer failed was produced but never published; its hidden 512-bit commitment can still be guessed. Across the whole run this contributes $p_{\mathrm{pub}}=2RS/2^{512}$, including leakage through the writer's success bit. A decoded frame returned on one handle and accepted on a non-partner handle contributes $p_{\mathrm{bind},g}=(R+S+H_g)S/2^{512}$, where $H_g$ includes all shared hash queries and environment work. In the ideal hidden world, the byte-shift argument bounds guessing a private fresh message by $256^{-\ell}=2^{-8\ell}$ for minimum length $\ell$ bytes. The stronger byte endpoints retain this term instead of weakening it to the earlier $2^{-\ell}$ compatibility bound; they add no cryptographic assumption.

Triangle inequalities through steps 2–4 and the disjoint sum in step 1 prove the bounds below. CE-OR concerns ordinary raw receives: all Beacon-to-Server positions and Server-to-Beacon positions at least two. The sequence-one response opened inside registration finish belongs to CE-A1 instead.

| Headline failure | Bound, summed over $g\in\mathcal G$ |
| --- | --- |
| CE-OR: accepted record lacks required prior publication, Beacon to Server | $\sum_g(\kappa_g+\alpha_g+p_{\mathrm{pub}})$ |
| CE-OR: Server to Beacon | $\sum_g(\kappa_g+\alpha_g+\beta_g+p_{\mathrm{pub}})$ |
| CE-UKS: receiver-side binding failure | $\sum_g(\kappa_g+\alpha_g+p_{\mathrm{bind},g})$ |
| CE-UKS: sender-side binding failure | $\sum_g(\kappa_g+\alpha_g+\beta_g+p_{\mathrm{bind},g})$ |
| CE-APP: guess a designated private fresh message, mode P | $\sum_g(\kappa_g+\rho_g+\beta_g+256^{-\ell})$ |

The CE-APP Server-only form omits $\beta_g$. Event arguments are suppressed in the table. The corresponding statements are in [`HeadlineOrigin`](lean/BeaconcryptCore/Computational/PqxdhDeploymentHeadlineOrigin.lean), [`HeadlineUks`](lean/BeaconcryptCore/Computational/PqxdhDeploymentHeadlineUks.lean) and [`HeadlineByteApp`](lean/BeaconcryptCore/Computational/PqxdhDeploymentHeadlineByteApp.lean). The earlier [`HeadlineApp`](lean/BeaconcryptCore/Computational/PqxdhDeploymentHeadlineApp.lean) statements remain available with their conservative guessing term.

For CE-LOR, let $J$ be public-view eligibility and $W$ eligible correct guessing of the hidden bit. Ideal hidden records satisfy $\Pr[W]=\tfrac12\Pr[J]$. Transfer both events separately, combining the slot anomaly before bounding it, to obtain

$$
\left|\Pr_{\mathrm{CE}}[W]-\tfrac12\Pr_{\mathrm{CE}}[J]\right|
\le\sum_g\left(\kappa_g(W)+\rho_g(W)+\tfrac12[\kappa_g(J)+\rho_g(J)]+\tfrac12\beta_g\right).
$$

This is an unconditional bound on eligible success masses, without dividing by eligibility probability. The Server-only form again omits $\beta_g$. See [`ce_lor`](lean/BeaconcryptCore/Computational/PqxdhDeploymentHeadlineLor.lean). This completes the designated-session argument.

## Registration, broader eligibility and later disclosure

Joint weak-EUF reduces an accepted signed tuple absent from an honest identity's signing history to forgery (CE-A2). Relating that history to a returned bundle requires the explicit `NoBundleFailureAt`/`NoBundleFailure` condition: a rejected Fresh bundle call may already have signed. Pinned-Server response origin (CE-A1) uses the Gap-DH, joint-signature, schedule and record reductions. Its ten-field agreement corollary retains the same bound; root equality, assigned-ID and payload agreement are not added deployment events. Registration consumption and record replay rejection are deterministic zero-loss facts. See [`DeploymentProvenance`](lean/BeaconcryptCore/Computational/PqxdhDeploymentProvenance.lean), [`DeploymentServerAuth`](lean/BeaconcryptCore/Computational/PqxdhDeploymentServerAuth.lean), [`DeploymentSessionAgreement`](lean/BeaconcryptCore/Computational/PqxdhDeploymentSessionAgreement.lean) and [the registration premise list](https://github.com/0xd6cb6d73/beaconcrypt/blob/e9f5048b8e27144ef3648aa06b09bd063baa38d7/doc/composition-assumptions.md).

The corollaries using ProVerif-shaped eligibility add the applicable registration-origin reductions; injective forms additionally charge identity collisions. Their fully closed forms also discharge ciphertext gaps and collisions: the gap costs a separate $\sum_g\kappa_g(\mathrm{gap})$ plus random-oracle guessing/birthday terms; ciphertext collision costs $q_{\mathrm{create}}\binom{q_{\mathrm{accept}}}{2}(\operatorname{Adv}^{\mathrm{IND\text{-}CCA}}(C)+2\delta_{\mathrm{corr}}+2^{-256})$. Thus these forms retain no unexplained ciphertext-gap probability and assume no separate KEM ciphertext-entropy property. See [`HeadlineDctClosedP2b`](lean/BeaconcryptCore/Computational/PqxdhDeploymentHeadlineDctClosedP2b.lean) and [the exact closed-term definitions](https://github.com/0xd6cb6d73/beaconcrypt/blob/e9f5048b8e27144ef3648aa06b09bd063baa38d7/doc/impl/deployment-experiment.md#the-terms-of-the-bounds). No ProVerif verdict is used as a computational proof step.

The LQ-F variants repeat the confidentiality argument after the run reveals the specified Ed25519 identity seeds and DH scalars, retaining the ML-KEM secrets, roots, chains and plaintexts as private. The root candidate term includes post-run HMAC queries: $(q_{\mathrm{accept}}+q_{\mathrm{finish}}+q_{\mathrm{hmac}}+q_{\mathrm{hmac},2})/2^{256}$. The post adversary remains classical; these are later-disclosure confidentiality claims, without quantum/QROM or later-authentication claims. The exact reveal and its exceptions are in [the experiment guide](https://github.com/0xd6cb6d73/beaconcrypt/blob/e9f5048b8e27144ef3648aa06b09bd063baa38d7/doc/impl/deployment-experiment.md#later-quantum-mode-lq-f).

## Native mandatory ML authentication and populated AD281

The separate native endpoint [`RegistrationNativeProductionSecurity.ceapp_bound`](lean/BeaconcryptCore/Computational/RegistrationNativeProductionSecurity.lean) bounds the broad original CE-APP event of the generated native profile in publication mode. It executes the actual constructor, local ML credential generation, mandatory Init and response authentication callbacks, populated AD281 bindings, both protocol roles and the unchanged original raw/secrecy ledger. Let $q=q_{\mathrm{build}}+q_{\mathrm{finish}}$ and $\mathcal G_N=\mathrm{Fin}(q_{\mathrm{accept}})\times\mathrm{Fin}(q_{\mathrm{create}}+1)$. Its bound has the following form:

$$
\Pr[\mathrm{CE\text{-}APP}_{\mathrm{native}}]
\le \varepsilon_{\mathrm{Ed}}
+\sum_{g\in\mathcal G_N}\left(
\varepsilon_{\mathrm{key},g}+\varepsilon_{\mathrm{KEM},g}
+2\left[\varepsilon_{\mathrm{recovery},g}+q\,256^{-160}+q\,256^{-32}\right]
+\varepsilon_{\mathrm{records},g}+256^{-\ell}
\right).
$$

Here $\varepsilon_{\mathrm{Ed}}$ is the global real-source Ed25519 identity-origin sum, charged outside the single canonical target sum. Each target's key term contains the explicit ordinary related-input family advantage and the five primitive key-schedule losses summed over at most $q$ admitted material demands. The family advantage remains an explicit loss whose smallness requires its corresponding related-input assumption. Each KEM term is one concrete whole-client ordinary IND-CCA advantage plus one unconditional correctness error. Each recovery term is the explicit PRF advantage of one suffix-key recovery tester whose adversary samples the entire honest startup and KEM prior; the displayed factor two also doubles both guessing allowances. This additional primitive family is $F_k(h)=\operatorname{fromRoot}(\mathrm{source},\operatorname{nativeRoot}(\mathrm{source},h\mathbin{\|}k))$, with a uniform 32-byte key $k$, an adaptive 160-byte head $h$ and a complete 108-byte answer. Its smallness is an explicit composite-family PRF requirement, beyond ordinary HMAC PRF security. The record term is the genuine-prior expectation of the three concrete, exactly billed HMAC/Extract, CTX integrity and IND-dollar privacy losses. These expected record advantages remain context indexed in the theorem.

The proof derives the original target's protected input and successful installation ordinal from its actual monitored path, then derives the same claimed physical handle's hidden origin in the actual selective execution. The final origin-aware observer is carried through every record hop before applying the byte-accurate fresh-message bound. Constructor and ML-generation coin caps, supported-prior callback `Frame` allowances, both wire readback contracts, the source identity conversion, full key-schedule correctness, functional decapsulation and short-signature rejection remain explicit conditions. All Ready, prefix-count, installation-origin and source-game joins are proved internally. This native endpoint is an ordinary CE-APP claim; the earlier later-disclosure and other headline statements retain their own stated profiles.

## Raw CBOR headline profile

The source14 raw-CBOR profile now has named [`ce_app`](lean/BeaconcryptCore/Computational/CborRawHeadlineApp.lean), [`ce_or_s2b` and `ce_or_b2s`](lean/BeaconcryptCore/Computational/CborRawHeadlineOrigin.lean), and [`ce_lor`](lean/BeaconcryptCore/Computational/CborRawHeadlineLorSecurity.lean) bounds. Its compiler preserves the complete original event ledger and raw returned bytes while executing separate registration and ordinary-record writers, including failed-writer poststates and the original private test/fresh draws. The bounds consume actual primitive reductions, the explicit Beacon-side KEM/correctness/guessing anomaly, and the failed-publication term $2RS/2^{512}$ where applicable; CE-APP uses $256^{-\ell}$.

This is the legacy source14 registration profile, with its original ML-field layout. It is distinct from the native mandatory-ML CE-APP experiment above. Concrete codec, canonical readback, routing and source contracts remain explicit at the raw-CBOR boundary.

## Relationship to implementation

The source-game equalities preserve full returned values and state under their codec and interpreter contracts. Their connection to unextracted adapter code includes reviewed Rust-to-Lean transcriptions; primitive implementations, compiler behavior, side channels, physical erasure, persistence, snapshots and restoration remain outside this proof. The resource bills bound coins and oracle calls, not running time.

The logical profiles above retain their stated primitive, codec, source and resource contracts. The native mandatory-ML result covers its broad ordinary CE-APP event; the source14 raw-CBOR and later-disclosure results have their separately identified scope. Concrete adapter, parser and primitive implementation correspondence remains part of the reviewed trust boundary in [trusted-boundary.md](trusted-boundary.md).
