# Actual initialized registration through the selected KEM interface

Status: independently reviewed focused source-routing and resource checkpoint; central integration remains separate. This joins the existing dynamic one-key KEM router to the actual initialized registration compiler. It is not the final selected-accept challenge reduction or an end-to-end secrecy claim.

## Exact source and retained continuation

The eight `PqxdhRegistrationJointKemCommands`, `KemInitialization`, `KemOrigin`, `KemRouting`, `OpenUniform`, `KemCosts`, `KemInitializedRouter` and `KemInitializedCosts` modules contain 39 checked statements. The shortened names share the `PqxdhRegistrationJoint` prefix. The source is the already proved one-Server, many typed-Beacon registration interface with its 14 request classes. Raw accept, optional failure, bundle generation, pending build, Beacon finish, live-field reads and the supplied/generated Server distinction retain their original semantics. Raw constructor admission, `new_onetime`, deletion and the complete record API remain outside this scheduler surface.

`KemCommands.program` is the literal existing source-client/open-backend compiler, retaining the complete native state and owner list. `creations` and `decapsulations` derive the creation and attempted-finish caps from the source request certificates. `selected_source` instantiates the existing complete-continuation reservation theorem: the chosen creation index is sampled first, every other possible key pair is sampled locally, and the actual adaptive source program uses those pairs at their original positions. The equality includes all native fields, caches, logs, private identity/KEM histories and replies. It requires enough reservation entries for the source creation cap, not successful creation, an honest candidate or public-key uniqueness.

`KemInitialization.constructor_kem` proves that actual Server initialization preserves the KEM pool, including failure and successful generated/imported branches. `initialized` places the same reservation behind that constructor. `constructor_order` moves only the selected KEM draw before the constructor, quantifying over the complete evaluated continuation and using the original samplers' independence and existing losslessness guarantee. Failed initialization then draws and discards the selected pair. That draw is counted even though it leaves the returned distribution unchanged. `initialized_first` and `actual_source_first` retain the entire initializer origin, runtime and original source outcome through this change of order.

## Issued fields and exact selected public key

`KemOrigin.issued_pq` consumes the actual chronological signing-attempt invariant: every issued tuple retains the constructor PQ field, including failed writer attempts. `selected_public` identifies that field with the reserved public key by its creation index; it does not infer index equality from key equality.

`raw_selected` consumes a supported original initialized source prefix, an actual addressed owner, the concrete created-prefix reservation relation and a literal successful raw native accept. It supplies the exact parsed candidate and detached signature verification and concludes either that its PQ field is the selected reserved key or that an original signed field was unissued at that owner's source identity index. Attacker-owned or relabelled candidates remain covered by this alternative. It does not assume the candidate signs under the addressed owner's key. The generated-index/key-match/reveal-history authentication reduction must discharge that alternative at the eventual authenticated target event. The created-prefix relation remains an explicit concrete state premise here; its reservation projection and this supported source event must still be joined at the selected acceptance cut.

## Ordinary CCA simulation and actual reveals

`KemRouting.pre_source` and `post_source` instantiate the existing ordinary CCA router with the entire compiled source command. The selected secret is supplied only to the mathematical CCA interpreter. The comparison uses a redacted reservation; unselected keys stay local. The postchallenge router uses the challenger candidate within the client, blocks the exact selected challenge ciphertext from ordinary decapsulation, and simulates every other permitted query. Its equality uses the existing functional-decapsulation and ordinary recipient-correctness contracts on actual supported key-generation and encapsulation outputs. No authentication or cross-public-key injectivity assumption is introduced. Later public-boundary nonexposure of the candidate remains a separate obligation.

`fresh_pre_event` equates an actual successful selected KEM-secret disclosure in the original history with the stopped interpreter's freshness marker. Missing or future handles keep their ordinary optional rejection and do not count as disclosures. Its event can inspect the complete source/native/private result. This is KEM freshness, distinct from identity-reveal transport for signature freshness. `pre_decapsulations` and `post_decapsulations` retain the source attempted-finish allowance with every typed reply.

`KemInitializedRouter.pre` receives only the selected public key, runs actual supplied/generated Server initialization, samples the unselected pairs locally, constructs the redacted reservation and resumes the complete source compiler. There is no selected-secret argument. Its `source` theorem equates ordinary interpretation with the whole stopped source experiment, retaining constructor failure and both private histories. This supplies an initialized scheduling simulator for a later selected-encapsulation cut; it has not replaced that encapsulation by a challenge or constructed the final IND-CCA distinguisher.

## Every-reply query accounting

Let `qCoin`, `qCreate`, `qBundle`, `qAccept`, `qBuild`, `qFinish`, `qHmac`, `qHash`, `qIdentityRead` and `qKemRead` denote the existing source request allowances. `KemBound` is the existing resource contract for the actual primitive programs and base interpreter. `keygenCost` and `encapsCost` include direct uniform calls plus the primitive base-call cap times the base interpreter's uniform cap. Deterministic primitive work remains a primitive/runtime efficiency contract; zero randomness does not mean free computation.

`OpenUniform.native_bound` forwards actual native draws. `prefix_step`, `prefix_bound` and `prepare_bound` prove the raw collector costs at most `32 + encapsCost` on every optional service reply. `tail_bound` proves the actual root/token continuation costs at most 64, and `accept_bound` combines them. `pool_bound`, `backend_step` and `backend_program` retain the complete adaptive compiler and native state. `total_eq` and `command_program` give:

```text
U = qCoin + 32*qCreate + 32*qBundle
    + (96 + encapsCost)*qAccept + 64*qBuild
    + 3584*qFinish + 64*qHmac + 64*qHash
    + qIdentityRead + qKemRead.
```

Each finish has at most 56 native callbacks charged at 64 each. The two read terms conservatively cover the older compiler's `other` class, which also includes possible explicit joint uniform requests. No tightness claim is made. This complete command-suffix bound applies to all native states and every typed challenger reply; the previous source uniform allowance covered only the evaluated real private interpreter.

`KemCosts.identity_creations` derives the actual joint identity cap. `local_uniform` and `local_base` express the existing local decapsulation contracts at the ordinary CCA interface. The pre/post theorems give:

| Resource | Command-suffix bound |
| --- | --- |
| Indexed KEM creation requests | `qCreate` |
| Generated joint identity requests | `qCreate` |
| Logical ordinary CCA decapsulation | `qFinish` |
| Uniform requests | `32*qCreate + U + decapsUniform*qFinish` |
| Forwarded base callbacks | `decapsBase*qFinish` |

The extra `32*qCreate` pays for the local joint interpreter's generated identity seeds. Native encapsulation and its base interpreter are already charged through `encapsCost` in `U`. Actual source generator and encapsulator invocation caps remain `qCreate` and `qAccept`; their internal resource contracts remain `KemBound`. Already interpreted local base callbacks are not new external CCA base queries.

Let `n` count the unselected reservation pairs and `g` be one for generated Server initialization, zero for a supplied seed. `KemInitializedCosts.uniform`, `excluded`, `decapsulations` and `base` prove the complete prechallenge wrapper caps:

```text
uniform <= qInit + 32*g + keygenCost*n
           + 32*qCreate + U + decapsUniform*qFinish
logical decapsulation <= qFinish
forwarded base <= decapsBase*qFinish.
```

`qInit` explicitly bounds every runtime initialization continuation. The ordinary challenger separately performs one selected key generation. The wrapper samples all `n` local pairs after successful initialization even when fewer source creations are used, so all are charged. Signing and report caps remain in the existing identity/source ledger. No target, session or record selection factor is inferred from these distribution equalities alone.

## Remaining joins

The next security consumer must select an actual accepted source encapsulation, derive its selected public-key routing from the authentication/issued-attempt event, interrupt and resume the exact continuation with challenger outputs, and combine pre/post reveal freshness and source target selection. It must feed the resulting exact 192-byte input and complete public context into the corrected secret-input Extract/HMAC construction, establish target-input nonexposure, and combine constructed reductions, losses and global bills. The native scheduler still uses its documented restricted Extract-ROM analysis interpreter; real public-HKDF replacement or computational justification is not inferred. Public HKDF stays real in the final intended interface. Codec internals, snapshots and persistence experiments remain outside this work as directed. No primitive algorithm or implementation is proved.
