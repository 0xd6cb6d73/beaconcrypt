# Milestone B: staged Lean design for server authentication (working copy)

This is the staged design used to build the Milestone B proof (route R1), copied from the working scratch file so the plan survives the session. Owner decisions are recorded in `audit-0b4039e-remediation-plan.md` section 6. Status on 2026-09-30: stages B1, B2, B3a, B8a, B9a, B4a and B5a are committed (`PqxdhExtractRomSeparation`, `PqxdhServerAuthAssumptions`, `PqxdhExtractRomFamily`, `PqxdhServerAuthKeySchedule`, `PqxdhPhase2LocalMatching`, `PqxdhServerAuthExperiment`, `PqxdhServerAuthNegativeControl`). Stage B6 is now proved in `PqxdhServerAuthGapDh` (138 guarded theorems; see `server-authentication-gap-dh.md`). The source Server-send factor is integrated in `PqxdhServerAuthSendFactor` (24 guarded theorems). B7 is now proved in `PqxdhServerAuthCollision` (36 guarded theorems; original adaptive collision bound `choose(Q,2)*64/2^256`). The actual logged Server build factor is integrated in `PqxdhServerAuthLoggedSendFactor` (12 guarded theorems). The Beacon factor is integrated in `PqxdhServerAuthBeaconFactor` (16 guarded statements), and the original B6 source/reduction accounting is integrated in four resource modules (61 guarded statements). B8b is now closed by the sixteen `PqxdhServerAuthEntry*` modules (215 guarded statements): complete original per-entry source comparison, five concrete component reductions and their source/challenger query bounds; see `server-auth-entry-factor.md`. B3b/B4b is now proved in `PqxdhServerAuthNative` (67 guarded statements): the complete original native experiment, literal reachable Beacon owner and both production constructor-order interchanges. B9b now also includes `PqxdhServerAuthCtxNative` and `PqxdhServerAuthCtxNativeBounds` (9 and 15 guarded statements), preserving both complete ordinary tails and their one-hash bounds; the selected adaptive ordinary CTX reduction remains in progress. The intermediate B10a assembly is proved in `PqxdhServerAuthIntermediate` (10 guarded statements), retaining explicit uniform-entry CTX probabilities, the same five per-entry component losses and the full constructed reduction ledger. B10, the complete B5b witness/control and documentation stage B11 remain open. Section 10 records the spike that de-risked B8b, and the notes appended after it record review obligations for later stages.


Worktree `/tmp/beaconcrypt-authenticated-root-completion`, branch `codex/full-proof-composition`. The design was written at `fbe31f9`. The worktree is now at `1c9aa50`; the two new commits are Milestone C work, and plan section 6 is unchanged. All paths below are relative to `beaconcrypt-core/proofs/lean/BeaconcryptCore/` unless they start with `doc/` or `beaconcrypt/`. The authoritative source is `doc/impl/audit-0b4039e-remediation-plan.md` section 6, including "Review decision (2026-09-29)" and "Design grounded in the Rust implementation (2026-09-29)". Where the older section 6 text differs (partnering on validated Phase 1 fields, reveals only of non-partners, an event stated modulo the ephemeral encoding, "implied by Gap-DH"), this design follows the two 2026-09-29 subsections and section 6.1 below.

Revision 2 addresses the review of revision 1. The changes are listed in section 9 ("Critique responses"). The main ones are:

- the Gap-DH assumption is restated as a twist-inclusive strengthening of Gap-DH;
- the event is frozen at the Beacon's acceptance and gains W3 (two partners);
- the collision term is narrowed, and an intermediate headline keeps it as a named game term until the owner rules on the spread law;
- two further negative controls are added (honest relay, pre-seal reveal);
- the stage plan is re-estimated, split, gated and limited to two concurrent compiles.

Scratch checks (not repository files) were all compiled with `lake env lean` in this worktree. Their axioms stay within `propext`, `Classical.choice` and `Quot.sound`:

- `/tmp/bc-arc-scratch/c-work/b-design/RomSeparation.lean`: `romHmac`, `ratchet_input_ne`, `root_input_eq`, `extract_other`, `extract_root`, `expandRoot_same`, `expandFull_same`.
- `/tmp/bc-arc-scratch/c-work/b-design/ClassLawCheck.lean`: `X25519ClassLaw`, `static_iff` (`[propext]`, guarded), `classEquivalence` (an instance of the existing `PeerEquivalence`), `scalar_agreement`.
- `/tmp/bc-arc-scratch/c-work/b-design/BDesignCheck.lean`:
  - the R1 family `romImpl`;
  - `rom_public_real`: outside the table domain, the public HMAC is the existing `impl` branch (`[propext, Classical.choice, Quot.sound]`);
  - `rootExpand_outside`: the 47-byte root Expand input never enters the table (`[propext]`);
  - `romCandidates` and `padded`;
  - the one-coordinate Server matcher `testServer`, with `serverCoordinate_some_iff` and `testServer_result` (`[propext, Quot.sound]`);
  - the definitions `X25519ClassLaw`, `X25519ScalarSpread` and `NonzeroHonestDh`.
- `/tmp/bc-arc-scratch/c-work/b-design/EventCheck.lean` (new in revision 2):
  - the acceptance `Snapshot`, `Ghost`, `Partner`, `W1`, `W2`, `W3`, `Win` and the narrowed `CollB`;
  - `win_frozen`: `Win` reads only the write-once snapshot (`[propext, Quot.sound]`, guarded);
  - `w3_collB`: W3 implies the narrowed collision, given the prefix invariant (`[propext, Quot.sound]`, guarded).

Decisions needed from the owner are collected in section 8.1. There are three:

- approval of `X25519ScalarSpread`, which the final headline needs; an intermediate headline without it is planned;
- approval of `NonzeroHonestDh`, which only the negative control uses; a fallback is planned;
- whether the Server's accept and build stay one oracle, as the plan says, or become two, as the public Rust trait exposes them.

## 1. The experiment

### 1.1 Design principle

The experiment is written once, as a program `body` over `PqxdhJointDhExtractRoot.RootSpec` (coins, `sign`, `publicHmac`, `derive`) that uses neither the Server seed nor the Beacon prekey scalar. Both roles already route their root through one family request `.derive message`, followed by one public Expand query (`PqxdhJointDhExtractRoot.root`/`reduction`):

- the Server through `PqxdhServerRelatedRootConsumer.client`, with message `PqxdhServerRelatedRootInput.message` (a `serverMessage` whose third coordinate is `.known`);
- the Beacon through `PqxdhPhase2DhRootConsumer.tail`/`PqxdhPhase2DhStage.stage`, with message `beaconMessage` (third coordinate `.selected`).

The Server seed enters only through the public reference of `PqxdhServerStaticDhSource.prefixImpl` and through the family's `input`. The Beacon prekey scalar enters only through the public reference of `PqxdhPhase2GapDhSource.prefixImpl` and through the family's `input`. The same `body` is therefore interpreted three ways:

- the real ROM experiment interprets `RootSpec` by `romImpl … seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction` (section 1.4);
- the Gap-DH reduction interprets it by a symbolic family `symImpl ∘ₛ reduction` that holds neither secret, in `OracleComp PqxdhJointGapDh.AdversarySpec` (section 5, step A);
- the native formulation is proved equal to the executable one (stage B4b, off the critical path), so the headline also holds for extracted code. It uses the extracted `server_accept`, `PqxdhServerRegistrationPublication.build` and `PqxdhBeaconPhase2Publication.nativeOwner`, and replaces only the root derivation by the table.

### 1.2 Parameters and primitives (module `PqxdhServerAuthExperiment`)

```lean
namespace BeaconcryptCore.Computational.PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointDhExtractRoot
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Fixed primitives. Every field is an existing functional contract; none is a security law. -/
structure Setup (baseSpec : OracleSpec ι) (KemSK : Type) where
  source : FixedHkdfSha512NoSaltSource            -- c := source.crypto
  hmac : HmacSha512
  joint : Primitives
  secretOfSeed : IdentitySeed → List.Vector UInt8 64
  wiring : SourceWiring source.crypto joint secretOfSeed
  serverDomain : PqxdhServerStaticDhSource.PublicDomain joint
  beaconDomain : PqxdhPhase2GapDhSource.PublicDomain (sourceInterface source.crypto joint secretOfSeed wiring)
  kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK)
  baseImpl : QueryImpl baseSpec ProbComp
  serverKeyId : Std.U64                            -- compiled-in ServerBinding.identity_key_id

def Setup.dh (s : Setup baseSpec KemSK) : DhInterface s.joint :=
  sourceInterface s.source.crypto s.joint s.secretOfSeed s.wiring

/-- Messages are abstract byte strings each side decodes; only pure public functions, no law. -/
structure Codec (Reader Response : Type) where
  read1 : Pqxdh.Bytes → Option Reader                          -- Server .decode
  identity pqField preField oneField : Reader → Option Pqxdh.Bytes
  write1 : Phase1Candidate → Option Pqxdh.Bytes                -- Beacon PqxdhBeaconPhase1Publication.WriterSpec
  write2 : PqxdhServerRegistrationPublication.ResponseFields → Option Pqxdh.Bytes   -- Server AuxQuery.write
  read2 : Pqxdh.Bytes → Option Response                        -- Beacon .decode
  ciphertext : Response → Option Ciphertext
  ephemeral serverIdentity : Response → Option Word32
  assignedId : Response → Std.U64
  application : Response → Option Pqxdh.Bytes                  -- Beacon AuxQuery.application
  frameRead : RawCtxReceive.FrameDecoder
  frameWrite : RawCtxMixedShared.Writer

/-- Public admission and allocation predicates of the reference implementation. -/
structure Checks where
  identityPoint : PqxdhEd25519EufCma.Ed25519PublicKey → Bool     -- Server .identityPoint
  x25519Point : Word32 → Bool                                     -- Server .parseDh
  kemKey : PqxdhKemIndCca.MlKem768PublicKey → Bool               -- Server .parseKem
  beaconIdentity : RawCtxServerRouting.Identity → Bool           -- tail .checkIdentity
  reserveRegistration reservePeer : Bool
  reservePlaintext : Nat → Bool
```

The experiment fixes the callback interpretations; the adversary never supplies them. Every callback that touches a secret is fixed to the functional primitive, so no parameter can leak a secret:

| Callback | Interpretation |
| --- | --- |
| Server `.decode`, getters | `codec.read1`, `codec.identity`, … |
| Server `.verify id bytes` | `source.crypto.verify id bytes` (attached Ed25519 verification) |
| Server `.identityPoint`, `.parseDh`, `.parseKem` | `checks.*` |
| Server `.registrationStatus rid`, `.reserveRegistration` | membership in the consumed set; `checks.reserveRegistration` (faithful, not used by the proof) |
| Server `.generate` (E := `ScalarBytes`) | `e ← sampleScalar; pure (some ⟨e, rootArray (xpub e)⟩)` |
| Server `.ephemeralDh e P` | `(sourceScalarDh c e (peer P)).map rootArray` |
| Server `.encapsulate pk` | `kem.encaps` through `kemAmbientImpl baseImpl` |
| Server `.publicConversion`, `.privateConversion` | `c.xpkConv`; `true` |
| Server `.staticDh P` | `PqxdhServerStaticDhSource.prefixImpl serverDomain` (reference only; the seed appears only in `romImpl.input`) |
| root consumer aux (`eraseShared`, `eraseInput`, `consume`) | no-op, no-op, insert into the consumed set |
| tail aux (`checkIdentity`, `reservePeer`, `reservePlaintext`, `erase`, `write`) | `checks.*`, no-op, `codec.write2` |
| tail seal (`RawCtxSourceSeal.NativeSpec`) | KDF `RawCtxSourceHkdf.response c`, hash `CtxRomAuth.ctxRandomOracle` on the shared cache, AEAD `c.aeadSeal`, frame `codec.frameWrite` |
| Beacon `.dhPair (.inl ()) EK` | `PqxdhPhase2GapDhSource.prefixImpl beaconDomain` (reference only) |
| Beacon `.dhPair (.inr s) EK`, `.dhIdentity () EK` | `sourceScalarDh c s (peer EK)`, `joint.staticDh beaconSeed (peer EK)` |
| Beacon `.decapsulate`, `.publicConversion` | `kem.decaps kemSk` through `baseImpl`; `c.xpkConv` |
| Beacon `.initial`, `.application`, raw open | `PqxdhRootTableInitialization.initialResponse c`; `codec.application`; `RawCtxSharedPrimitive.nativeImpl c (RawCtxSourceHkdf.response c)` on the shared cache |

The `checks` predicates sit at fixed Rust positions. `identityPoint` and `x25519Point` stand at libsodium-rs `from_bytes` calls that check only the length (server.rs:342 and :362-367), so their Rust instance is constantly `true`; point-dependent rejections come from `.verify`, `.publicConversion` and the DH interfaces at their own positions. `kemKey` stands for the ML-KEM encapsulation-key admission that Rust performs inside `crypto_kem::mlkem768::encapsulate` (server.rs:373), after the ephemeral draw; its Rust instance is the encapsulation key check of the abstract ML-KEM contract, not `true`. `acceptAll` therefore matches Rust only on ML-KEM keys that pass that check, such as the honest generated keys used by `relay_live`. No theorem may take a hypothesis that `identityPoint` or `x25519Point` returns `false` on some input, and a hypothesis that `kemKey` returns `false` is admissible only for keys that ML-KEM encapsulation rejects.

### 1.3 Adversary interface

```lean
inductive Query where
  | server (phase1 : Pqxdh.Bytes) (payload : Option Pqxdh.Bytes)  -- accept and build (cbinds.rs:280-291); see 8.1.3
  | finish (phase2 : Pqxdh.Bytes)           -- target Beacon finish; single-shot by the Beacon phase
  | hmac (key : HmacBlock) (message : Pqxdh.Bytes)   -- patched public HMAC (R1)
  | hash (bytes : Pqxdh.Bytes)              -- BLAKE2b random oracle (CtxRO)
  | reveal (keyId : Std.U64)                -- post-registration Server state

abbrev QueryRange : Query → Type
  | .server _ _ => Option PqxdhServerRegistrationPublication.Response
  | .finish _ => Option Pqxdh.Bytes
  | .hmac _ _ => HmacBlock
  | .hash _ => CtxRomAuth.CtxDigest
  | .reveal _ => Option ratchet.concrete.ConcreteRatchetKernel

abbrev Spec := unifSpec + (QueryRange : OracleSpec Query)

structure Input where
  server : PublicIdentity            -- joint.publicKeys seed
  serverKeyId : Std.U64
  phase1 : Option Pqxdh.Bytes        -- the target Beacon's published Phase 1
  revealed : Option IdentitySeed     -- `some seed` only in the negative control

abbrev Adversary := Input → OracleComp Spec Unit

def IsRomQuery : Spec.Domain → Prop
  | .inr (.hmac key message) => key = zeroSalt ∧ message.length = 192
  | _ => False
def IsServerQuery : Spec.Domain → Prop | .inr (.server _ _) => True | _ => False
def IsHashQuery : Spec.Domain → Prop | .inr (.hash _) => True | _ => False

structure Budget (adversary : Adversary) (Q qH qHash : Nat) : Prop where
  server : ∀ input, (adversary input).IsQueryBoundP IsServerQuery Q
  rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH
  hash : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash
```

The payload is `Option Pqxdh.Bytes`, exactly as in Rust. `none` selects `REGISTRATION_WITNESS` (`[0xFF]`, `shared.rs:50`, `server.rs:459`; `registrationWitness` and `data.getD` in `PqxdhServerRegistrationPublication.lean:151,166`), and an empty payload fails after the derive (`server.rs:460`, Lean line 167).

Only the patched HMAC is exposed. There is no HKDF oracle (component gap 8), so every 192-byte zero-salt evaluation is a table query. HMAC on any other key or length is the real function, which the adversary can also evaluate locally. Finish and reveal need no cap: the Beacon phase makes finish single-shot (`PqxdhBeaconPhase2Publication.owner_inactive`), and reveals are free.

Adversary restrictions and their justification. Each is repeated in the module docstring of `PqxdhServerAuthExperiment` and in the analysis.

1. Budgets `Q`, `qH`, `qHash` are ordinary query bounds. `Q` is a parameter of the bound, evaluated at a few tens (user decision).
2. There is no Beacon secret reveal. Key-compromise impersonation is not claimed (user decision).
3. A Server reveal returns only the kernel installed by `publish`, for any session including the partner. This is all the Rust Server stores or exposes (`server.rs:39-42, 410, 422, 456, 504-532`, `ser.rs:195-213`). The installed kernel holds the control, the send chain after one step, the receive chain and empty receive slots. It never holds the initial send chain or the sequence-one key. `preseal_reveal_control` (section 4) shows that this boundary is load-bearing.
4. There are no Server record oracles. Rust exposes `encrypt_and_update` and `decrypt_and_update` (`server.rs:504-532`, `persistence.rs:441-466`), which return the post-operation `RatchetSnapshot`. They are omitted because they can be simulated without loss, for the following reasons:
   - After `publish`, session `kid`'s Server state is exactly the kernel that `.reveal kid` returns.
   - Server encryption and decryption are deterministic functions of that kernel, the inputs, the ratchet KDF and BLAKE2b. The ratchet KDF is the real HMAC on 32-byte Extract inputs and on Expand inputs, which are outside the table by `ratchet_input_ne`/`extract_other`. BLAKE2b is the `.hash` oracle.
   - They never touch the Extract table, the Beacon, the Beacon's finish or `ghost.seals`. Records they produce have sequence 2 or more, and the single finish requires sequence one (`beacon.rs:468`).

   So for every adversary with record oracles there is one without them that has the same view, the same ghost and therefore the same `Win`. It reveals `kid` once and runs the operations locally, tracking the advanced kernel to answer later reveals. It keeps `Q` and `qH`, and adds the per-operation hash count to `qHash`. The argument goes in the docstring and the analysis. A Lean version is the optional stage B13.
5. Accept and build are one oracle, as the plan's Rust-grounded subsection fixes (`cbinds.rs:280-291`; the Go and Python bindings also combine them). The public `ProviderServer` trait and the persistence wrappers expose them separately (`server.rs:118-121`, `persistence.rs:412-419`). Splitting would change three things:
   - Key IDs would be allocated in build order (`server.rs:434`, core `pqxdh.rs:847-870`). Key IDs enter no key, associated data or commitment, and the proof uses no key-ID property.
   - Sessions that derive without sealing would appear. The combined oracle already reaches them: an empty payload fails after the derive.
   - The adversary would learn the derive outcome before choosing the payload and the build time. The partner's seal could then come after the Beacon's acceptance.

   The acceptance-frozen event (section 2) and step H_j already handle seals after acceptance. But an exact simulation of the split interface by the combined one needs the derive outcome to be a public function. That holds for real X25519, where a zero output occurs exactly for small-order peers and whatever the scalar, but it is not a stated contract. Whether to model two oracles is decision 8.1.3.
6. The adversary chooses the payload (`Option`, as above). This is stronger than the real interface, where the host chooses it, and `none` covers the witness default.
7. There is no Server-seed reveal in the headline. Before the finish it makes the claim false, which is what the negative control shows. After the finish it cannot change `Win`, which reads only the snapshot written inside the single finish (checked `win_frozen`). The optional corollary B12 formalizes post-acceptance corruption. Until B12 is built, the documentation lists it as a restriction with this justification.
8. There is no persistence, no snapshot access and no access to running code: these are outside the threat model (plan section 6).
9. There is one target Beacon and one finish. Beacon keys are per object and are used for one Phase 1 and one finish (`beacon.rs:306-334, 403-406, 488-491`). Several Beacons follow by a union bound.
10. Seals are logged at the successful seal callback, not at publication. A record that is sealed but whose Phase 2 writer then fails (`server.rs:471-488`: `encrypt_message_with_ratchet` precedes `write_message(...).ok()?`, and the session is not installed) still counts as the partner's output. So a Beacon acceptance of exactly that unsent tuple is not a W2 win. Reproducing it means producing the Server's ciphertext under a hidden `K1` without seeing it, which CTX treats as a full-tuple match, not a forgery. The omission is therefore consistent with the CTX notion and negligible. It avoids Milestone C's unprovable writer-failure case.
11. Availability, replay protection and key-ID uniqueness are neither claimed nor used.

### 1.4 The R1 family (module `PqxdhExtractRomFamily`, checked in `BDesignCheck.lean`)

```lean
noncomputable def romImpl (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl PqxdhJointDhExtractFamily.Spec (StateT PqxdhJointDhExtractFamily.State ProbComp)
-- coins and sign: as in `impl`
-- publicHmac key message: if key = zeroSalt ∧ message.length = 192 then HmacOracle.randomOracle on
--   state.cache (logged as .publicHmac) else the real hmac.eval, exactly `impl`'s branch (rom_public_real)
-- derive message: match input joint dh seed scalar message with
--   | none => logged none | some bytes => HmacOracle.randomOracle bytes on the same cache
```

It reuses `PqxdhJointDhExtractFamily.State`, so it plugs into the existing `family` parameters of `PqxdhServerRelatedRootConsumer.stage` and `PqxdhPhase2DhStage.impl` without edits. `impl`, `protectedExtract`, `realImpl` and `idealImpl` are not modified. The family `History` records `.derive message (some PRK)` and `.publicHmac PRK rootExpandInput root`, so it holds key material. Step E_j erases it before factoring (section 5).

### 1.5 State, ghost and oracles

```lean
structure Accepted where
  keyId : Std.U64
  payload : Pqxdh.Bytes
  associatedData : Pqxdh.Bytes

inductive Touch where                       -- ordered analysis log of table touches
  | session (index : Nat) (message : PqxdhJointDhExtractFamily.Message)
  | beacon (message : PqxdhJointDhExtractFamily.Message)
  | adversary (bytes : Pqxdh.Bytes)         -- only IsRomQuery calls

/-- Frozen copy of the logs at the Beacon's acceptance (checked in EventCheck.lean). -/
structure Snapshot where
  accepted : Accepted
  touches : List Touch
  seals : List (Nat × RawCtxSourceSend.SealContext)

structure Ghost where
  touches : List Touch
  seals : List (Nat × RawCtxSourceSend.SealContext)   -- successful sequence-one seals, by session
  acceptance : Option Snapshot                        -- written once, at the end of a successful finish

structure GameState (KemSK : Type) where
  ctx : CtxRomAuth.CtxRO.QueryCache
  server : PqxdhServerRegistrationPublication.State Unit Unit (List pqxdh.RegistrationId)
  beacon : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK
  sessions : Nat
  ghost : Ghost
```

The handler writes the ghost and never returns it to the adversary. The finish logs `Touch.beacon` when the Beacon's derive runs, which is inside the finish call and before its open. On success it writes `acceptance := some ⟨accepted, touches, seals⟩` with the logs at that moment. The finish is one oracle call and single-shot, so no other oracle interleaves between the Beacon's derive and its acceptance, and `acceptance` is written at most once. B4a proves the invariant `snapshot_prefix`: `snap.touches <+: ghost.touches` and `snap.seals <+: ghost.seals`.

Oracles (all `StateT (GameState KemSK) (OracleComp RootSpec)`):

```lean
/-- One Server session: ordered prefix with a public static reference, extracted server_accept with one
family root request, then the response tail with the adversary's payload. -/
noncomputable def serverSession (setup) (codec) (checks) (index : Nat) (raw : Pqxdh.Bytes)
    (payload : Option Pqxdh.Bytes) :
    StateT (GameState KemSK) (OracleComp RootSpec) (Option PqxdhServerRegistrationPublication.Response)
-- 1. input ← simulateQ (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain serverAux (fun _ => pure ()))
--      (PqxdhServerRootPreparation.collect raw)                       -- ≤ 22 callbacks (collect_bound)
-- 2. returned ← simulateQ (familyLift + rootAux) (PqxdhServerRelatedRootConsumer.client binding input)
--      logging Touch.session index (PqxdhServerRelatedRootInput.message input)
-- 3. on ok (some ⟨root, pending⟩): PqxdhServerRegistrationPublication.build setup.source pending root
--      payload () state.server, run through `nativeAdapter` with the seal handler above, logging seals

/-- Target Beacon finish: executable preparation and related-root tail, then the unchanged final checks. -/
noncomputable def beaconFinish (setup) (codec) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (raw : Pqxdh.Bytes) : StateT (GameState KemSK) (OracleComp RootSpec) (Option Pqxdh.Bytes)
-- match state.beacon.beacon.phase with
-- | .initSent control (.inl ()) (.inr oneTime) kemSk =>
--     staged ← simulateQ (beaconHandler …) (PqxdhPhase2DhStage.stage publicValue codec.frameRead control () oneTime kemSk raw)
--       -- the family derive inside logs Touch.beacon (beaconMessage publicValue collected)
--     (out, beacon') := PqxdhBeaconPhase2Publication.finish control state.beacon staged
--     on success: ghost.acceptance := some ⟨accepted, ghost.touches, ghost.seals⟩
-- | _ => pure none                                        -- single shot (owner_inactive)

def reveal (keyId : Std.U64) (state : GameState KemSK) : Option ratchet.concrete.ConcreteRatchetKernel :=
  (state.server.server.peers keyId).map RawCtxServerRouting.Peer.kernel
```

`.hmac key message` is forwarded as the `RootSpec` query `publicHmac`, and logged as `Touch.adversary` when `IsRomQuery` holds. `.hash bytes` runs `ctxRandomOracle ((), bytes)` on `state.ctx` with coins from `RootSpec`. Coins are forwarded.

The target Beacon's Phase 1 is `PqxdhLivePhase1Bundle.bundle projection` from `.fresh ⟨⟨rootArray (joint.publicKeys seed).ed25519, setup.serverKeyId⟩⟩ (.inl ()) kemSk`, where:

- `projection.dh (.inl ()) := publicValue.prekey` and `projection.dh (.inr s) := xpub s`;
- the one-time generator returns `.inr oneTime`;
- `DynamicSpec` service requests are signed by `joint.sign beaconSeed`;
- `codec.write1` is the writer.

It reads the Beacon prekey only through `publicValue.prekey`.

### 1.6 Games

```lean
/-- Body that uses neither the Server seed nor the prekey scalar: Beacon secrets and Phase 1, then the adversary. -/
noncomputable def body (setup) (codec) (checks) (adversary : Adversary) (revealed : Option IdentitySeed)
    (publicValue : PublicChallenge) : OracleComp RootSpec (GameState KemSK) := do
  let beaconSeed ← coins sampleSeed                 -- Beacon identity (not a Gap-DH secret)
  let oneTime ← coins sampleScalar
  let (kemPk, kemSk) ← coins (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  let (phase1, beacon) ← coins (phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk)
  let input : Input := ⟨publicValue.identity, setup.serverKeyId, phase1, revealed⟩
  Prod.snd <$> (simulateQ (handler setup codec checks publicValue beaconSeed) (adversary input)).run (initial beacon)

/-- Full final state, for the analysis events. The Server seed and prekey scalar are sampled inside, first. -/
noncomputable def gameState (setup) (codec) (checks) (revealSeed : Bool) (adversary : Adversary) :
    ProbComp (IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State) := do
  let seed ← sampleSeed                             -- Server identity: Gap-DH `seed`
  let scalar ← PqxdhJointGapDh.sampleScalar         -- Beacon signed prekey: Gap-DH `scalar`
  let publicValue := challenge setup.joint setup.dh seed scalar
  let (final, family) ← (simulateQ (romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
    (body setup codec checks adversary (if revealSeed then some seed else none) publicValue)).run
      PqxdhJointDhExtractFamily.empty
  pure (seed, scalar, final, family)

/-- Executable ROM experiment. -/
noncomputable def game (setup) (codec) (checks) (revealSeed : Bool) (adversary : Adversary) : ProbComp Bool :=
  (fun (seed, scalar, final, _) => decide (Win setup seed scalar final.ghost)) <$>
    gameState setup codec checks revealSeed adversary

/-- Native formulation (B4b, off the critical path): `romNativeSession` runs collect under
`PqxdhServerStaticDhSource.nativeImpl joint seed`, `romSource` (= `PqxdhServerRelatedRootConsumer.source`
with `nativeRoot` replaced by `romRoot`) and `build`; the Beacon runs `PqxdhBeaconPhase2Publication.nativeOwner`
with `.dhPair (.inl ())` by `PqxdhPhase2GapDhSource.nativeImpl dh scalar` and `.root` by `withRoot romRootReply`. -/
noncomputable def actual (setup) (codec) (checks) (revealSeed : Bool) (adversary : Adversary) : ProbComp Bool

theorem actual_game … : actual setup codec checks revealSeed adversary = game setup codec checks revealSeed adversary
```

`romRoot` reads or samples `cache[absBytes root_key_input.bytes]` and returns `first32 (hmac.eval prk rootExpandInput)`, with the same history entries as `romImpl ∘ₛ reduction`. The sampling order "seed, scalar, Beacon identity, one-time, KEM" differs from source order only between independent draws. If wanted, an exchange lemma `actual_source_order` restates `actual` in source order (identity, prekey, KEM, one-time).

## 2. Events

The event definitions below are checked in `EventCheck.lean`, where `setup` is replaced by `dh` for brevity.

```lean
def rootInput (setup) (seed scalar) (message : PqxdhJointDhExtractFamily.Message) : Option Pqxdh.Bytes :=
  PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message

def beaconInput … (touches : List Touch) : Option Pqxdh.Bytes :=
  (touches.findSome? fun | .beacon m => some m | _ => none).bind (rootInput setup seed scalar)

/-- Partnering by identical root derivation (same 192-byte root input), before acceptance. -/
def Partner … (snap : Snapshot) (index : Nat) : Prop :=
  ∃ message bytes, Touch.session index message ∈ snap.touches ∧
    rootInput setup seed scalar message = some bytes ∧ beaconInput … snap.touches = some bytes

def sealed (context : RawCtxSourceSend.SealContext) : Accepted :=
  ⟨context.targetId, context.plaintext.drop 8, context.associatedData⟩

def W1 … (ghost : Ghost) : Prop := ∃ snap, ghost.acceptance = some snap ∧ ∀ index, ¬ Partner … snap index

def W2 … (ghost : Ghost) : Prop :=
  ∃ snap, ghost.acceptance = some snap ∧ (∃ index, Partner … snap index) ∧
    ∀ index, Partner … snap index → ∀ context, (index, context) ∈ snap.seals → sealed context ≠ snap.accepted

/-- Injective agreement: two partners at acceptance. Charged to the collision term. -/
def W3 … (ghost : Ghost) : Prop :=
  ∃ snap, ghost.acceptance = some snap ∧ ∃ i j, i ≠ j ∧ Partner … snap i ∧ Partner … snap j

def Win … (ghost : Ghost) : Prop := W1 … ghost ∨ W2 … ghost ∨ W3 … ghost
```

This is a matching-conversation or agreement notion. The partner must have derived the Beacon's root input, and sealed the accepted tuple, before the Beacon accepted. A later partner or a later matching seal changes nothing (`win_frozen`). `rootInput` recomputes the bytes with the seed and scalar, which only the experiment holds. B4a proves that on every reached run it equals the extracted builder's input (`PqxdhServerRelatedRootInput.source_input`, `PqxdhJointDhExtractRoot.beacon_source`). So partnering is equality of `absBytes root_key_input.bytes` between the extracted Server and Beacon candidates.

`sealed` uses the tail's `firstContext`: `targetId = candidate.key_id`, `plaintext = key_id_binding ++ payload` and `associatedData = candidate.associated_data`. If the partner sealed nothing before acceptance, every Beacon acceptance counts. The key ID enters the event but not partnering, as the Rust-grounded subsection requires.

Analysis events (not part of `Win`):

```lean
/-- The adversary queried the table at the Beacon's root input (final log). -/
def BadB … (ghost : Ghost) : Prop :=
  ∃ bytes, beaconInput … ghost.touches = some bytes ∧ Touch.adversary bytes ∈ ghost.touches

/-- The Gap-DH scan event, read from the family history, exactly the list the scanning reduction outputs. -/
def CandHit … (qH : Nat) (history : PqxdhJointDhExtractFamily.History) : Prop :=
  ∃ value, setup.joint.staticDh seed (setup.dh.publicKey scalar) = some value ∧ value ≠ zeroDh ∧
    value ∈ (padded qH (romCandidates history)).toList

/-- Narrowed collision: two Server sessions derived the Beacon's root input (final log). -/
def CollB … (ghost : Ghost) : Prop :=
  ∃ i j mi mj bytes, i ≠ j ∧ Touch.session i mi ∈ ghost.touches ∧ Touch.session j mj ∈ ghost.touches ∧
    beaconInput … ghost.touches = some bytes ∧ rootInput … mi = some bytes ∧ rootInput … mj = some bytes

/-- First toucher of the Beacon's table entry: session j < Q, the Beacon (index Q) or the adversary. -/
def owner … (ghost : Ghost) : Option (Fin (Q + 1))
```

`w3_collB` (checked) gives `W3 → CollB` from `snapshot_prefix`. Under `¬BadB` the owner is a session or the Beacon (`owner_partition`), and the owner determines the case (`owner_cases`, B8b):

- If the owner is session `j < Q`, that session touched the entry before the Beacon's derive. So it is a partner, `W1` fails, and only `W2` remains.
- If the owner is the Beacon, then no session touched the entry before the Beacon's derive, and none can touch it between that derive and acceptance, because the finish is atomic. So only `W1` remains.

## 3. Headline theorems

```lean
namespace PqxdhServerAuthentication

/-- Explicit game term: probability of the narrowed session collision in the executable experiment. -/
noncomputable def sessionCollGame (setup) (codec) (checks) (adversary) : ℝ :=
  (Pr[fun (seed, scalar, final, _) => CollB setup seed scalar final.ghost |
    gameState setup codec checks false adversary]).toReal

/-- Pairwise Server-session root-input collision, from the approved scalar-spread law (8.1.1). -/
noncomputable def serverCollision (Q : Nat) : ℝ := (Q.choose 2 : ℝ) * 64 / 2 ^ 256

/-- Per-entry loss for table entry j (session j < Q, or the Beacon's own entry j = Q). -/
noncomputable def entryLoss (setup) (codec) (checks) (adversary) (fallback : ModifiedNonceAeadForgery)
    (Q qH qHash : Nat) (j : Nat) : ℝ :=
  (hmacPrfRealGame setup.hmac (rootExpandReduction … j)).boolDistAdvantage (hmacPrfRandomGame (rootExpandReduction … j))
  + (extractRealGame setup.hmac uniform32 (initExtractReduction … j)).boolDistAdvantage
      (extractUniformGame uniform32 (initExtractReduction … j))
  + (hmacPrfRealGame setup.hmac (initExpandReduction … j)).boolDistAdvantage (hmacPrfRandomGame (initExpandReduction … j))
  + (extractRealGame setup.hmac uniform32 (stepExtractReduction … j)).boolDistAdvantage
      (extractUniformGame uniform32 (stepExtractReduction … j))
  + (hmacPrfRealGame setup.hmac (stepExpandReduction … j)).boolDistAdvantage (hmacPrfRandomGame (stepExpandReduction … j))
  + (ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c (AdaptiveCtxPrefixValidation.validationReduction
        rawDecode c (AdaptiveCtxDynamicKnownKeys.decisionClient c (decision rawDecode (ctxClient … j))) qHashCtx))
      + (qHashCtx : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹
      + 2 * modifiedNonceAeadINTCTXTAdvantage c (AdaptiveRawNonceAead.indexedReduction (baseDecoder rawDecode)
          fallback (AdaptiveCtxReceive.wrapped rawDecode
            (AdaptiveCtxDynamicKnownKeys.decisionClient c (decision rawDecode (ctxClient … j)))) 0)
      + 1 / (2 ^ 512 : ℕ)).toReal
-- rawDecode : AdaptiveCtxReceive.RawDecoder, the CTX target decoder induced by codec.frameRead (as in HB-112)
-- uniform32 := do let x ← $ᵗ RootOutput; pure ((), x.toList)   (independent uniform 32-byte hidden input)
-- qHashCtx := qHash + Q * sealHashes + openHashes, constants from native_build_bounds and PqxdhBeaconPhase2Bounds

/-- Intermediate headline (B10a): no spread law; the session collision stays a named game term. -/
theorem server_authentication_coll
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (classLaw : X25519ClassLaw setup.source.crypto)
    (rootCorrect : SourceRootCorrect setup.source setup.hmac)
    (fullCorrect : SourceFullCorrect setup.source setup.hmac)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : Budget adversary Q qH qHash)
    (fallback : ModifiedNonceAeadForgery) :
    (Pr[= true | game setup codec checks false adversary]).toReal ≤
      (PqxdhJointGapDh.advantage setup.joint setup.dh
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal
      + sessionCollGame setup codec checks adversary
      + ∑ j ∈ Finset.range (Q + 1), entryLoss setup codec checks adversary fallback Q qH qHash j

/-- Final headline (B10, after approval of the spread law and B7). -/
theorem server_authentication … (spread : X25519ScalarSpread setup.source.crypto) … :
    (Pr[= true | game setup codec checks false adversary]).toReal ≤
      (PqxdhJointGapDh.advantage setup.joint setup.dh
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal
      + serverCollision Q
      + ∑ j ∈ Finset.range (Q + 1), entryLoss setup codec checks adversary fallback Q qH qHash j

theorem server_authentication_actual …  -- the same bound for `actual` via `actual_game` (B4b)
theorem scanClient_signing …            -- 0 signing requests (extractor_signing)
theorem scanClient_decisions …          -- ≤ 2*qH*(Q+1) + 2*(Q+1)*(qH+Q+1); extractor adds qH
theorem scanClient_uniform …            -- 64 + (Beacon, ephemeral, KEM, table and hash coins) (extractor_game_uniform)
```

Each loss term is the advantage of an explicitly constructed reduction or an explicit number:

| Term | Meaning | Assumption |
| --- | --- | --- |
| `advantage … (extractor (scanClient …))` | Gap-DH recovery of the scanning reduction. The candidates are the DH1 coordinates of the adversary's `qH` table queries, zero-padded. | anchored two-sided strong CDH with twist-inclusive decision oracles (`PqxdhJointGapDh.game`, section 6.1) |
| `sessionCollGame` (B10a) or `serverCollision Q` (B10) | two Server sessions derived the Beacon's root input; they would seal twice under one key and nonce | explicit game term, or the X25519 scalar spread (pending approval) |
| `rootExpandReduction j` | PRK_j to root_j, one HMAC query at `rootExpandInput` | HMAC-SHA-512 PRF |
| `initExtractReduction j`, `initExpandReduction j` | root_j to the 64-byte initializer | Extract PRG-type game, HMAC PRF |
| `stepExtractReduction j`, `stepExpandReduction j` | first half to (K1, N1, chain_1), two Expand blocks | Extract PRG-type game, HMAC PRF |
| CTX group | first-record integrity for the selected key K1_j with `qSeal = 1`, `qRaw = 1` (`authentication_bound`) | nonce-AEAD IND$ and INT-CTXT, BLAKE2b random oracle |

There is no separate Extract-ROM collision or guessing term. The only table loss is `BadB`, which is contained in `CandHit` and charged to Gap-DH. Each KDF hop's real world reproduces the table distribution exactly, so PRK or root coincidences need no exclusion (section 5). There is no KEM term and no weak-EUF term (section 8.1, items 5 and 6). No premise has the form "for all adversaries, advantage ≤ ε". `codec`, `checks` and `setup.kem` are universally quantified with no law.

Numerical reading for the documentation, at `Q = 32` and `qHash = 2^64`:

- The dominant explicit number is the CTX guessing term summed over the 33 entries: 33 · qHashCtx / 2^128 ≈ 33 · 2^-64 ≈ 2^-59. The honest hashes in `qHashCtx` are a few hundred and do not change this.
- The other explicit numbers are far smaller: 33 · 2^-512, and `serverCollision 32 = 496 · 2^-250 < 2^-241`.
- The rest are 264 advantages of constructed reductions, whose sizes the primitive assumptions govern: 165 KDF-type, 33 IND$ and 66 INT-CTXT, plus one Gap-DH advantage.
- `qH` affects only the Gap-DH reduction's candidate count and resources.

## 4. Negative controls

```lean
namespace PqxdhServerAuthNegativeControl

/-- Control-only functional laws; none is a premise of the upper bound. -/
structure ControlLaws (setup) (codec) (checks) : Prop where
  nonzero : NonzeroHonestDh setup.source.crypto            -- pending approval (8.1.2); fallback below
  phase1 : ∀ bundle bytes, codec.write1 bundle = some bytes → Phase1ReadBack codec bundle bytes
  phase1Total : ∀ bundle, HonestBundle bundle → (codec.write1 bundle).isSome
  phase2 : ∀ fields bytes, codec.write2 fields = some bytes → Phase2ReadBack codec fields bytes
  phase2Total : ∀ fields, HonestFields fields → (codec.write2 fields).isSome
  frame : ∀ frame bytes, codec.frameWrite frame = some bytes → codec.frameRead bytes = some frame
  frameTotal : ∀ frame, HonestFrame frame → (codec.frameWrite frame).isSome
  checks : HonestChecks setup checks        -- honest keys pass point/KEM/identity checks; allocations succeed
  functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem

abbrev kemError (setup) : ℝ :=
  (Pr[= true | simulateQ (kemAmbientImpl setup.baseImpl) (PqxdhKemCorrectnessError.errorExperiment setup.kem)]).toReal

/-- The adversary uses only the revealed seed: it runs one honest Server session locally on the target's
Phase 1 (family derive computed with the seed, table queries through `.hmac zeroSalt`, hashes through
`.hash`) and delivers that Phase 2 to the Beacon. It never calls `.server`. -/
noncomputable def controlAdversary (setup) (codec) (checks) (payload : Pqxdh.Bytes) : Adversary

/-- Honest relay: one `.server` on the target's Phase 1 with `payload`, then the response to the finish. -/
noncomputable def relayAdversary (payload : Option Pqxdh.Bytes) : Adversary

theorem control_no_server … : (controlAdversary …) input |>.IsQueryBoundP IsServerQuery 0
theorem control_budget … : Budget (controlAdversary setup codec checks payload) 0 1 controlHashes
theorem relay_budget … : Budget (relayAdversary payload) 1 0 0

/-- Gate (B5a): the event is reachable when the Server key is revealed. -/
theorem negative_control (setup) (codec) (checks) (laws : ControlLaws setup codec checks)
    (payload : Pqxdh.Bytes) (nonempty : payload ≠ []) :
    1 - kemError setup ≤ (Pr[= true | game setup codec checks true (controlAdversary setup codec checks payload)]).toReal

/-- Gate (B5a): honest runs do not win; W2's definition matches what the Beacon accepts. -/
theorem relay_not_win (setup) (codec) (checks) (laws : ControlLaws setup codec checks)
    (payload : Option Pqxdh.Bytes) (nonempty : payload.getD registrationWitness ≠ []) :
    (Pr[= true | game setup codec checks false (relayAdversary payload)]).toReal ≤ kemError setup

/-- B5b: the Rust reveal boundary is load-bearing. In `presealGame` the reveal also returns the session's
initial send chain chain_0, which Rust never exposes; the adversary relays the partner's Phase 2 with its own
payload resealed under (K1, N1) = step chain_0 and wins W2. -/
theorem preseal_reveal_control (setup) (codec) (checks) (laws : ControlLaws setup codec checks)
    (payload other : Pqxdh.Bytes) (nonempty : payload ≠ [] ∧ other ≠ []) (differ : payload ≠ other) :
    1 - kemError setup ≤ (Pr[= true | presealGame setup codec checks (presealAdversary setup codec payload other)]).toReal

/-- B5b: joint satisfiability of every premise of all theorems, with zero KEM error. -/
theorem witness : ∃ (setup : Setup Base Unit) (codec : Codec …) (checks : Checks),
    ControlLaws setup codec checks ∧ X25519ClassLaw setup.source.crypto ∧
    X25519ScalarSpread setup.source.crypto ∧ SourceRootCorrect setup.source setup.hmac ∧
    SourceFullCorrect setup.source setup.hmac ∧ kemError setup = 0
theorem relay_zero …  -- relay_not_win at the witness: Pr[Win] = 0
```

Proof sketch of `negative_control`. With no Server session, `W1` holds whenever the Beacon publishes. Outside the KEM `Bad` set the Beacon publishes on every sample, by this chain:

1. Codec round trips give the Beacon the Server's fields.
2. `NonzeroHonestDh`, `conv_agree`, `dh_comm` and `scalar_agreement` give identical nonzero DH1 to DH4 on both sides, and `good_agreement` gives the same SS.
3. The same table entry gives the same PRK and root, and `PqxdhInitialRatchetComplementarity` gives complementary kernels.
4. Seal then open through the shared BLAKE2b cache succeeds (new lemma `ctx_seal_open`, from `aead_open_seal`, `frame` and cache consistency).
5. `registration_key_id_binding_abs` and `LE64_inj` give binding authentication, and the pins hold by construction of `Setup`.

An exchange of independent draws puts the Beacon's keygen before the control adversary's encapsulation, as `PqxdhKemCorrectnessError.sample` requires. `continuation_bound` then gives the `1 - error` bound.

Proof sketch of `relay_not_win`. The argument uses the same lemmas and runs outside the KEM `Bad` set:

- The relay's session is the unique partner before acceptance, so `W1` and `W3` fail.
- The Beacon accepts exactly `sealed` of the partner's seal (key ID from the binding, `plaintext.drop 8`, `absBytes` of the AD), so `W2` fails.

Inside the `Bad` set nothing is claimed, because the abstract AEAD has no law that stops a wrong key from opening. The bound is therefore the KEM error, and it is zero at the witness (`relay_zero`). This lemma is the early check that `sealed`, `accepted` and `Partner` are defined consistently.

`presealGame` is defined in B5b as a separate handler. It reuses B4a's session components with a KDF interpretation that also logs the sequence-one chain argument, plus a reveal that returns the kernel with its send chain replaced by that chain_0. B4a's headline handler is not parameterized, so the main chain is unaffected.

Fallback if `NonzeroHonestDh` is not approved: `ControlLaws` drops `nonzero`. The two lower bounds gain the explicit game term `zeroDhGame`, the probability in the control run that some honest DH output is all-zero, and `witness` evaluates it to 0.

The witness cannot reuse F6's X25519, codec or callbacks (constant-zero DH, all decoders `none`). Proposed toy X25519: `x25519 a p := setBit0 (norm32 a ⊕ norm32 p)` and `xpub b := norm32 b`. Here `norm32` truncates or zero-pads to 32 bytes, and `setBit0` forces bit 0 of byte 0. The toy satisfies:

- `dh_comm` and `NonzeroHonestDh`;
- the class law, because outputs determine the peer up to bit 0 of byte 0, which never matters, and lengths are normalized;
- the spread law, with two preimages.

Reused from F6: `toyHmac`, `hkdfOf`, `toy_full_correct`, `toy_root_correct`, `toyKem`, `toyFunctional`, `Base` and `baseImpl`. The toy codec is identity-like with an explicit field layout. The toy has not been checked in Lean yet.

## 5. Hybrid chain

Notation: `G` is `gameState … false adversary`; `R_B` is the Beacon's root input.

| Step | Game or inequality | Lemma (stage) | Loss |
| --- | --- | --- | --- |
| 0 | `actual` | definition (B4b) | — |
| 1 | `actual = game` | `actual_game` from `server_stage_rom`, `beacon_stage_rom`, `owner_stage` (B3b/B4b, off the critical path) | 0 |
| 2 | `Pr[Win] ≤ Pr[BadB] + Pr[CollB] + Pr[(W1 ∨ W2) ∧ ¬BadB ∧ ¬CollB]` | `win_le_games` (B4a), using `w3_collB` (checked) and `snapshot_prefix` | — |
| A1 | `BadB → CandHit` on the support | `badB_candidate` (B6). `readDh 32 R_B` is the DH1 of `beaconMessage`, whose static peer is `publicValue.prekey = dh.publicKey scalar`. It is nonzero by `beaconDomain.nonzero` and `agreement`. `touches_history` puts the adversary's `R_B` touch into `romCandidates family.history`, and `candidates_length` (budget plus `honest_no_rom_public`) keeps it inside the padded vector. | 0 |
| A2 | `Pr_G[CandHit] = Pr[candidateGame joint dh scanClient]` | `sym_complete` (B6): exact simulation of `romImpl` by `symImpl` under `serviceImpl`, with state concretization. The family history is carried unchanged, so both sides read the same candidate list. | 0 |
| A3 | `= advantage joint dh (extractor scanClient)` | existing `candidate_success_eq_advantage` | Gap-DH |
| B | `Pr_G[CollB] ≤ serverCollision Q` (B10 only) | `server_collision` (B7, gated on 8.1.1). `CollB` implies a pairwise collision `i < j`. Session j samples `e_j` after the adversary fixed its converted identity, and equal root inputs force `x25519 e_j IK_j = DH2_i ≠ 0`. Spread gives `≤ 64/2^256` per ordered pair. | `serverCollision Q` |
| C | `Pr[(W1 ∨ W2) ∧ ¬BadB ∧ ¬CollB] = ∑_{j ≤ Q} Pr[E_j]`, `E_j := (W1 ∨ W2) ∧ ¬BadB ∧ ¬CollB ∧ owner = some j` | `owner_partition`, `owner_cases` (B8b). Under `¬BadB` the owner is a session (W2 case) or the Beacon (W1 case). | 0 |
| D_j | table entry `R_j` of owner j is sampled at its creation and routed to every honest hit; an adversary table query at `R_j` aborts | `entry_programmed` (B8b), identical until abort. It restates `PqxdhHiddenRoot` 1245-1268 (`tvDist_simulateQ_run_le_probEvent_output_bad`) for `HmacOracle`. `E_j` implies no abort. | 0 |
| E_j | the run uses `PRK_j` only through `f PRK_j := (step (first32 init), second32 init)` with `init := HKDF(expandRoot PRK_j, INFO_R, 64)`, 108 bytes | `history_erase` (B8b): the family history (which holds `PRK_j` in `.derive` entries and `root_j` in the root Expand `.publicHmac` entry) and the cache entry at `R_j` are projected to placeholders, since neither the handler nor `E_j` reads them (`map_run_simulateQ_eq_of_query_map_eq`). Then `entry_factor` (B8b) gives a key-free continuation `D_j` for both the Server-send half and the Beacon-receive half, with placeholders for root, initializer and chain_0 (and for a pending root if decision 8.1.3 selects split oracles). | 0 |
| F_j | `f PRK_j` replaced by 108 uniform bytes | `keySchedule_bound` (B8a, generic, no protocol code): five hops, each shaped like `sourceRootAdvantage_le_extract_add_hmac`, using `SourceFullCorrect` for the 64- and 76-byte HKDF and `second_observed` for the split | five KDF terms of `entryLoss j` |
| G_j | key-first reorder: `K1 ← $ᵗ CtxKey` first, then `N1` and `chain_1`, with the other half sampled by the client | `key_first` (B9b), pattern of `PqxdhFirstSharedMessagePrefix.adaptive_endpoint` | 0 |
| H_j | `E_j → won` of `RawCtxSelectedAuthenticationObserver` for `ctxClient j` (selected key K1_j, all other keys known, one shared BLAKE2b cache) | `event_won` (B9b). A Beacon acceptance whose tuple differs from every seal in `snap.seals` has no full-tuple match with a prior seal; this uses the local-owner `matching_open`, `afterOpening_success`, `plaintextBinding_bytes`, `registration_key_id_binding_abs` and `LE64_inj`. The snapshot makes "prior" definitional. With `¬CollB` at most one seal uses K1_j. | 0 |
| I_j | observer bound | existing `authentication_bound` with `qSeal = 1`, `qRaw = 1` (`compiled_opens`-style lemma), `small` trivial | CTX group of `entryLoss j` |

Intermediate statements that keep game terms explicit, as in Milestone C:

- `win_le_games` (B4a) gives `Pr[Win] ≤ Pr[BadB] + Pr[CollB] + ∑_j Pr[E_j]`.
- `badB_le_gapDh` (B6) replaces `Pr[BadB]`.
- `entry_le_uniform` (B8b) gives `Pr[E_j] ≤ KDF_j + uniformEntryGame j`.
- `uniformEntry_le_ctx` (B9b) replaces `uniformEntryGame j`.
- `server_authentication_coll` (B10a) keeps `sessionCollGame`.

Each is a standalone theorem, so a stall in a later stage leaves a correct statement with named game terms.

Details of `sym_complete` (step A2). `symImpl : QueryImpl PqxdhJointDhExtractFamily.Spec (StateT SymState (OracleComp PqxdhJointGapDh.AdversarySpec))` keeps an ordered table of entries with their sampled blocks. Each entry is either `concrete bytes` or `message m`; in a message entry DH1 is unknown, and DH3 is unknown exactly when `m.third = .selected`. It also keeps the same `PqxdhJointDhExtractFamily.History` as `romImpl`. A lookup scans in order and returns the first equal entry:

- concrete against concrete: byte equality;
- concrete `x` against a Server-shaped message: `testServer` (one `decideDh false P x[32..64]`, checked `testServer_result`);
- concrete `x` against the Beacon message: `PqxdhPhase2GapDhInput.test` (two decisions);
- message against message: known coordinates must be equal. DH1 is compared by the class law with a scalar the reduction holds (`static_iff`, checked). DH3 known against selected uses `decideDh true EK d3`. DH3 selected against selected uses the class law (`scalar_iff`, from the scratch lemmas);
- `derive` rejection: `serverDomain.accepts` and `beaconDomain.accepts`, without any secret.

The symbolic handler is first flattened with `serviceImpl joint dh seed scalar` into one `QueryImpl PqxdhJointDhExtractFamily.Spec (StateT (SymState × PqxdhJointGapDh.History) ProbComp)`, following the `flattenStateT` pattern of `AdaptiveCtxDynamicKnownKeys.source_view`. Both sides then share the base monad `ProbComp`. The projection maps the symbolic table to a cache by first-wins insertion, concretizing each message with `input … seed scalar`, keeps the family history, and drops the decision history. The per-query equation then holds for every symbolic state, so VCVio's `map_run_simulateQ_eq_of_query_map_eq` (`VCVio/OracleComp/SimSemantics/StateT/StateProjection.lean:57`) applies without a reachability invariant.

If first-wins does not match the cache semantics, the invariant-gated `map_run_simulateQ_eq_of_query_map_eq_inv'` (same file, line 103) applies instead, with the invariant "no two entries have equal concretizations". The client is `scanClient publicValue := do let (_, sym) ← (simulateQ (symImpl ∘ₛ reduction) (body … none publicValue)).run SymState.empty; pure (padded qH (romCandidates sym.history))`. Beacon, KEM and hash coins come from the `unifSpec` side, and `baseImpl` is lifted.

`touches_history` (B6) states that on every reached state the `Touch.adversary` subsequence of `ghost.touches` equals the zero-salt, 192-byte `.publicHmac` subsequence of the family history. It follows from two facts:

- `.hmac` appends to both logs in lockstep;
- `honest_no_rom_public`: no honest code issues such a query. Roots go through `.derive`, the root Expand input is 47 bytes (`rootExpand_outside`), and the CTX KDF calls `c` directly rather than through `RootSpec`.

Why step D_j costs nothing: the only way the adversary learns `PRK_j` is a table query at `R_j`, and under `owner = j` that query is `BadB`, which `E_j` excludes.

Why steps E_j to F_j need no alias term: after each hop, the replaced value (PRK_j, root_j or the initializer) has no other honest use. The experiment has no record traffic beyond sequence one, and the Beacon never sends. Coincidences with other entries' values are part of the real distribution, which each hop's real world reproduces exactly. If B8b finds a use that breaks this (for example a shared KDF memo cache), the term is (pairs)/2^256 and is added explicitly.

## 6. New assumptions and contracts

All are separate definitions. `Pqxdh.Crypto` gets no new field, because that would add a premise to every existing theorem. Only 6.1, 6.2 and 6.3 go into the documentation lists now. 6.4 and 6.5 go in only after the owner approves them (8.1.1, 8.1.2).

### 6.1 Anchored two-sided strong CDH with twist-inclusive decision oracles (hardness assumption, headline)

Lean: the existing `PqxdhJointGapDh.game`/`advantage` with `dh := sourceInterface c joint secretOfSeed wiring`, applied to a constructed reduction. The game works as follows:

- It samples a uniform 32-byte Ed25519 seed (the Server identity; its X25519 scalar is the clamped SHA-512-derived converted scalar) and a uniform 32-byte X25519 scalar (the Beacon prekey, clamped by X25519).
- It publishes the Ed25519 public key and the prekey `xpub scalar`.
- Two decision services answer whether a supplied candidate equals X25519 of one of the two secrets at any 32-byte peer encoding. `PqxdhJointGapDh.reply` places no restriction on the peer.
- The goal is the nonzero cross value DH1 = X25519(k_S, prekey), a point on the curve.

The scanning reduction queries the services at adversary-chosen Phase 1 prekeys (`testServer`: `decideDh false SPK_i x`) and at adversary-chosen ephemerals (`decideDh true EK x`). The Server rejects only small-order encodings, and libsodium does not reject points on the quadratic twist or non-canonical u ≥ p, so the services also answer on twist points, under the same clamped scalar. The reduction makes no signing request (`scanClient_signing = 0`, from `extractor_signing`), so only the signing-free part of the game is relied on.

Relation to the literature: this is a strong-DH / Gap-DH assumption for the pair (Curve25519, its quadratic twist), with one clamped scalar per side, on the joint Ed25519-seed distribution, with the CDH target on the curve. It is a strengthening of textbook Gap-DH and is not implied by it. Okamoto and Pointcheval's Gap-DH gives a DDH oracle only on the prime-order group, whereas each service here is a strong-DH oracle in the sense of Abdalla, Bellare and Rogaway for one fixed secret, and it also answers on the twist. The `PqxdhJointGapDh` module docstring already says this ("not a proved equivalence to textbook prime-order GapDH").

Plausibility:

- Curve25519 has order 8·ℓ with ℓ ≈ 2^252 prime, and its twist has order 4·ℓ' with ℓ' ≈ 2^253 prime. Generic discrete logarithm costs about 2^125 in the ℓ-subgroup and about 2^126 in the ℓ'-subgroup. Bernstein chose the curve so that its twist is secure for exactly this reason: implementations that skip point validation still resist twist attacks.
- A clamped scalar is ≡ 0 mod 8, so it annihilates the cofactor-8 component of a curve point and the cofactor-4 component of a twist point. A decision query therefore answers only about the prime-order component, and there is no small-subgroup leakage.
- Non-canonical u ≥ p and the masked top bit are reduced as RFC 7748 prescribes, so they are aliases of canonical points and give the adversary no extra oracle.
- The Server's scalar is derived from a uniform Ed25519 seed through SHA-512 and clamping (RFC 8032, RFC 7748), not sampled uniformly. The game keeps that joint distribution.
- The game is stated on libsodium's X25519 as a black box over 32-byte strings. Nothing about libsodium is proved.
- Signal's PQXDH specification and the CryptoVerif analysis assume Gap-DH on Curve25519. The twist-inclusive oracle is this project's explicit strengthening. It is needed because both roles process adversary-chosen X25519 inputs without point validation.

Literature:

- Okamoto and Pointcheval, "The Gap-Problems: a new class of problems for the security of cryptographic schemes", PKC 2001;
- Abdalla, Bellare and Rogaway, "The Oracle Diffie-Hellman Assumptions and an Analysis of DHIES", CT-RSA 2001 (strong DH oracle);
- Bernstein, "Curve25519: new Diffie-Hellman speed records", PKC 2006 (twist security);
- RFC 7748 (sections 5 and 7);
- Signal, "The PQXDH Key Agreement Protocol" (Kret and Schmidt), security considerations;
- Bhargavan, Jacomme, Kiefer and Schmidt, "Formal verification of the PQXDH post-quantum key agreement protocol for end-to-end secure messaging", USENIX Security 2024.

The plan's section 6 item 2 says "This is implied by Gap-DH (Okamoto and Pointcheval, PKC 2001)". That sentence must be corrected to the wording above (interim edit, section 6.6).

### 6.2 Zero-salt HKDF-Extract on 192-byte inputs as a random oracle (idealization)

Lean: `romImpl` (section 1.4) and `romHmac` with the separation lemmas (B1). HKDF-Expand, the 32-byte initial and ratchet Extract calls, and every other HMAC use stay real, and the existing HMAC-PRF and Extract PRG-type games cover them.

Separation holds because the extracted core emits only 192-byte `RootKeyInput` and 32-byte `SymmetricRatchetKdfRequest` (`Extraction/Types.lean:40-42, 149-150`), and Expand inputs are 42, 47, 106 or 111 bytes. So a patch on `(zeroSalt, 192-byte)` changes no other call, even when a PRK equals `zeroSalt`. That production performs exactly one Extract per request, with the request as IKM, is adapter-level trust (`beaconcrypt/src/pqxdh.rs:46-58`, `beaconcrypt/src/ratchet.rs:86-98`).

Plausibility:

- The restricted idealization is implied by modelling the whole fixed-zero-key HMAC-SHA-512 as a random oracle. In that full model the function's values on 192-byte inputs form a uniform table independent of its values on every other input, which is exactly this table. The remaining inputs are a fixed function, and the theorems hold for every choice of it, because `hmac` is universally quantified.
- The full model is where the indifferentiability results apply: HMAC with one fixed key over Merkle-Damgård SHA-512 is indifferentiable from a random oracle when the compression function is ideal, and the weak-key-pair issue does not arise with a single key. Under the full model the 32-byte Extract PRG-type games also hold.
- SHA-512's length padding puts the message length into the last block, which separates 192-byte inputs from 32-byte inputs.
- Restricting the oracle keeps every other use real, so the standard-model games for those uses stay premises. This is a weaker idealization than the full model.
- HMAC pads keys shorter than the block (128 bytes for SHA-512) with zero bytes (RFC 2104), and HKDF-Extract without salt uses HashLen zero bytes (RFC 5869). So the empty salt, the 64-byte zero salt and the all-zero block key all define the same function, and the model has one zero key.
- No quantum-random-oracle claim is made.

Literature:

- Bellare and Rogaway, "Random Oracles are Practical", CCS 1993;
- Dodis, Ristenpart, Steinberger and Tessaro, "To Hash or Not to Hash Again? (In)differentiability Results for H² and HMAC", CRYPTO 2012;
- Coron, Dodis, Malinaud and Puniya, "Merkle-Damgård Revisited", CRYPTO 2005;
- RFC 2104 and RFC 5869.

### 6.3 X25519 class law (functional primitive contract)

```lean
def X25519ClassLaw (c : Pqxdh.Crypto) : Prop :=
  ∀ a left right, c.x25519 a left = c.x25519 a right → Pqxdh.ResponseEncodingAlias.SameDhReplies c left right
```

Plausibility, for real X25519 on 32-byte inputs with clamped `k`, where `2^254 ≤ k < 2^255` and `k ≡ 0 mod 8`:

1. Encodings. X25519 masks the top bit of the u-coordinate and reduces a non-canonical u ≥ p modulo p (RFC 7748, section 5). Every 32-byte encoding therefore denotes the point with u-coordinate `u mod p`, and two encodings of the same u give equal outputs under every scalar.
2. Same curve. For u ≠ 0, the value u³ + Au² + u = u(u² + Au + 1) is nonzero, because A² − 4 is a non-square mod p. So it is either a square (u is on the curve) or a non-square (u is on the twist): a nonzero u-value lies on exactly one of the two. Suppose the outputs are equal and nonzero. `[k]L` lies on L's curve and `[k]R` on R's curve, and both have the same nonzero u, so L and R are on the same curve and `[k]L = ±[k]R`.
3. Torsion. Then `[k](L ∓ R) = O`. The group order is 8ℓ (curve) or 4ℓ' (twist), and no clamped k is a multiple of ℓ or ℓ'. The multiples of ℓ in `[2^254, 2^255)` are 4ℓ, 5ℓ, 6ℓ and 7ℓ, and those of ℓ' are 3ℓ' and 4ℓ' (2ℓ' = 2^254 − 18 − 4δ lies below 2^254, where ℓ = 2^252 + δ). Since ℓ and ℓ' are odd, none of these is ≡ 0 mod 8. So `L ∓ R` has order dividing 8 (resp. 4), every clamped `k'` annihilates it, and `[k']L = ±[k']R` gives equal outputs for every scalar.
4. Zero outputs. X25519 returns 0 exactly when `[k]L ∈ {O, (0,0)}`. `[k]L = (0,0)` is impossible for `8 | k`, because 8·E has no 2-torsion on either curve. So a zero output means L has small order, whatever the scalar, and equal zero outputs mean both inputs have small order and give zero under every scalar.
5. Lengths. `Pqxdh.Crypto.x25519` is a function on byte strings of any length, and the checked law quantifies over all of them (8.1.9), because `static_iff` applies it to `xsk (secretOfSeed seed)` and `xsk` has no width law. Production calls libsodium only on 32-byte arrays, so other lengths are a modelling artefact. A witness satisfies the law on them by normalizing inputs to 32 bytes, as the toy's `norm32` does.

The reduction uses the law to decide DH1 equality with its own scalar. It is the premise already used in `Model/Pqxdh/ResponseEncodingAlias.lean`. Literature: RFC 7748; Bernstein, PKC 2006.

### 6.4 X25519 scalar spread (approved functional contract, 8.1.1; used only by B7/B10)

```lean
def X25519ScalarSpread (c : Pqxdh.Crypto) : Prop :=
  ∀ (peer : PeerEncoding) (value : DhOutput), value ≠ zeroDh →
    (Finset.univ.filter fun scalar : ScalarBytes => c.x25519 scalar.toList peer.toList = value.toList).card ≤ 64
```

Plausibility:

- If the peer P has small order, every output is zero, which the law excludes.
- Otherwise 8P has order n ∈ {ℓ, ℓ'}. A clamped scalar is k = 2^254 + 8m with 0 ≤ m < 2^251 < n, so m ↦ [k]P = [2^254]P + [m](8P) is injective.
- A nonzero u-value belongs to at most two points ±Q, so it has at most two m, and therefore at most two clamped scalars.
- Clamping ignores five bits, so each clamped scalar corresponds to 32 byte strings: 64 in total.

The review confirmed this count. Literature: RFC 7748; Bernstein, PKC 2006.

### 6.5 Nonzero honest DH (approved functional contract, 8.1.2; negative controls only)

```lean
def NonzeroHonestDh (c : Pqxdh.Crypto) : Prop := ∀ a b, c.x25519 a (c.xpub b) ≠ Pqxdh.zero32
```

Plausibility: `xpub b` has prime order ℓ, and no clamped scalar is a multiple of ℓ (6.3, item 3). Today this appears only as the side condition `HonestRun.Ok` (`Model/Pqxdh/Theorems.lean:395`). Fallback without it: the explicit `zeroDhGame` term (section 4).

### 6.6 Documentation text

Both lists get the entries below, each with the plausibility argument and literature above. The lists are `doc/composition-assumptions.md` ("Primitive guarantees, additional assumptions and idealizations") and `doc/formal-verification-analysis.md:797-807`.

- The anchored two-sided strong CDH with twist-inclusive decision oracles, as a new headline assumption. It is stated as a strengthening of Gap-DH, not as implied by it.
- The Extract random oracle, as an idealization next to the BLAKE2b random oracle.
- The class law, as a functional contract.

The spread law and the nonzero-honest-DH contract are added to both lists, and to the first list (`doc/formal-verification-analysis.md:787-795`), only after the owner approves them.

The existing "Required hybrids and losses" row "Authenticate the pinned Server to the Beacon" (`doc/composition-assumptions.md:42`) is replaced once B10 or B10a is built; no second row is added. Proposed replacement:

| Step | Existing result or usable ingredient | Missing argument for production composition |
| --- | --- | --- |
| Authenticate the pinned Server to the Beacon | `PqxdhServerAuthentication.server_authentication` (with `server_authentication_coll`, which needs no spread law and keeps the session collision as a named game term). The experiment samples the Server seed and the Beacon's prekey, identity, one-time and ML-KEM secrets inside the game. It gives the adversary `Q` Server sessions (accept and build) on arbitrary Phase 1 bytes and payloads, the target Beacon's single finish, post-registration state reveals of every Server session including the partner, the patched HMAC and BLAKE2b. The event is fixed at the Beacon's acceptance: W1 (no Server session derived the Beacon's root input), W2 (a partner exists and none of its seals matches the accepted key ID, payload and associated data) or W3 (two partners). The bound has three parts: the advantage of a constructed scanning reduction against the twist-inclusive anchored strong CDH game `PqxdhJointGapDh.game` (a strengthening of Gap-DH); `C(Q,2)·64/2^256` from the X25519 scalar-spread law; and, for each of the `Q+1` table entries, five HMAC-PRF and Extract PRG-type advantages and the first-record CTX terms (IND$, `qHashCtx/2^128`, two INT-CTXT advantages, `2^-512`). The other premises are the X25519 class law and source HKDF correctness. The idealizations are zero-salt Extract on 192-byte inputs and BLAKE2b as random oracles. Justified restrictions: no Beacon secret reveal (no KCI); no Server-seed reveal (event frozen at acceptance); Server record oracles omitted because the reveal simulates them; accept and build combined; one target Beacon and a single finish. `negative_control`: with the Server seed revealed, the event has probability at least one minus the KEM correctness error. `relay_not_win`: honest relays do not win. `preseal_reveal_control`: revealing the initial send chain would break the claim. At `Q = 32` and `qHash = 2^64` the explicit numbers total about `2^-59`. | Later records the Beacon accepts (second stage, from Milestone C), several target Beacons (union bound), post-acceptance corruption (unless B12 is built), a split accept and build interface (unless decision 8.1.3 selects it), and the adapter-level facts that production makes exactly one Extract per KDF request and that libsodium implements the modelled functions. |

Interim edits to tracked files, for the main agent (this task is read-only):

- `doc/composition-assumptions.md:42`: replace "The assumption route awaits review" by "Route R1 was chosen on 2026-09-29 (review decision in the remediation plan); the Lean build follows the staged design."
- `doc/impl/audit-0b4039e-remediation-plan.md` section 6, "Proposed assumptions", item 2: replace "This is implied by Gap-DH (Okamoto and Pointcheval, PKC 2001)" by "It strengthens Gap-DH (Okamoto and Pointcheval, PKC 2001): the decision services also answer on the quadratic twist under the same clamped scalar, which is plausible because the twist is secure (Bernstein, PKC 2006)".

## 7. Staged implementation plan

Every module does the following:

- ends with `#guard_msgs in #print axioms` for each main theorem (a subset of `propext`, `Classical.choice` and `Quot.sound`);
- is added to `BeaconcryptCore.lean`, `check-inventory.sh` and `reviewed-inventory.txt`;
- modifies no existing theorem.

Sizes are re-estimated against Milestone C. Its comparable first-record integrity chain is about 14.9k lines (`PqxdhFirstRecordStopTagged` alone is 6966), and it needed two extra passes to remove game terms.

| Stage | Module | Main content | Depends on | Size (lines) |
| --- | --- | --- | --- | --- |
| B1 | `Computational/PqxdhExtractRomSeparation` | `romHmac`, `ratchet_input_ne`, `root_input_eq`, `extract_other`, `extract_root`, `expandRoot_same`, `expandFull_same` (scratch-checked); `production_ratchet_unchanged`; `root_under_patch` | existing | 200-300 |
| B2 | `Computational/PqxdhServerAuthAssumptions` | `X25519ClassLaw`, `static_iff`, `scalar_iff`, `classEquivalence`, `scalar_agreement` (scratch-checked); `honest_accepts`; `serverGapDhAdvantage`; `NonzeroHonestDh` (definition only, flagged) | existing | 300-400 |
| S | scratch spike, not committed | `entry_factor` on the Server-send half only: `PqxdhServerRegistrationPublication.build` plus the native seal path, with placeholders for root, initializer and chain_0, shown to depend on `PRK` only through the 108-byte `f PRK`. Output: the placeholder interface, whether the `PqxdhSelectedInitialOwnerCompiler` pattern transfers, and re-estimates of B8b and B9b. | existing | 500-1000 |
| B3a | `Computational/PqxdhExtractRomFamily` | `romImpl` (checked), `rom_public_real`, `rom_hit`, `rom_miss`, `rom_derive_hit`, `rom_side` | B1 | 400-600 |
| B8a | `Computational/PqxdhServerAuthKeySchedule` | generic `keySchedule_bound` (five constructed-reduction advantages for any 108-byte distinguisher) | existing | 450-700 |
| B4a | `Computational/PqxdhServerAuthExperiment` | `Setup`, `Codec`, `Checks`, `Query`, `Spec`, `Input`, `Adversary`, `Budget`, `GameState`, `Ghost`, `Snapshot`, oracles, `phase1Run`, `body`, `gameState`, `game`. Events `Partner`, `W1`, `W2`, `W3`, `Win`, `BadB`, `CandHit`, `CollB`, `owner`, `sessionCollGame`. Support lemmas `snapshot_prefix`, `win_frozen`, `w3_collB`, `win_le_games`, `partner_iff_root_input`, `finish_single_shot`, `seal_once_per_session`, `reveal_post_registration`, `empty_payload_derives`. The restriction list in the docstring. | B3a | 2000-2800 |
| B9a | `Computational/PqxdhPhase2LocalMatching` | `matching_open` for the Phase 2 local owner; `accepted_of_match` | existing | 500-800 |
| B5a (gate) | `Computational/PqxdhServerAuthNegativeControl` | `ControlLaws`, `controlAdversary`, `relayAdversary`, budgets, `ctx_seal_open`, `honest_session_accepted`, `negative_control`, `relay_not_win` | B2, B4a | 1500-2200 |
| B6 | `Computational/PqxdhServerAuthGapDh` | `SymState`, `testServer` (checked), `symImpl`, `sym_step`, `sym_complete`, `scanClient`, `honest_no_rom_public`, `touches_history`, `candidates_length`, `badB_candidate`, `badB_le_gapDh`, `scanClient_signing`, `scanClient_decisions`, `scanClient_uniform` | B2, B4a, B5a | 1800-2800 |
| B8b | `Computational/PqxdhServerAuthEntryFactor` (may split into Server-send and Beacon-receive modules) | `owner_partition`, `owner_cases`, `entry_programmed`, `history_erase`, `entry_factor` (both halves), `entry_le_uniform` | B4a, B5a, B8a, S | 5000-8000 (re-estimate after S) |
| B9b | `Computational/PqxdhServerAuthCtx` | `key_first`, `ctxClient`, `ctx_compiled`, `ctx_budgets`, `event_won`, `uniformEntry_le_ctx` | B8b, B9a | 3500-5500 (re-estimate after S) |
| B10a | `Computational/PqxdhServerAuthenticationGames` | `entryLoss`, `server_authentication_coll`, axiom guards; built incrementally as B6, B8b and B9b land | B6, B9b | 300-500 |
| B7 | `Computational/PqxdhServerAuthCollision` | `X25519ScalarSpread`, `spread_probability`, `server_collision` | B4a, B5a; **owner approval of 8.1.1** | 500-800 |
| B3b/B4b | `Computational/PqxdhServerAuthNative` | `romRoot`, `romSource`, `romNativeStage`, `server_stage_rom`, `romRootReply`, `beacon_stage_rom`, `owner_stage`, `actual`, `actual_game` | B3a, B4a | 1500-2500 |
| B5b | `Computational/PqxdhServerAuthWitness` | toy instance, `witness`, `relay_zero`, `presealGame`, `presealAdversary`, `preseal_reveal_control` | B5a | 1300-1800 |
| B10 | `Computational/PqxdhServerAuthentication` | `serverCollision`, `server_authentication`, `server_authentication_actual` | B7, B10a, B4b | 200-300 |
| B12 (optional) | `Computational/PqxdhServerAuthCorruption` | a game with `.corrupt` enabled after the finish; truncation at the finish call (the snapshot is constant afterwards, and `OracleComp` has total mass); `server_authentication_corrupt` | B10a | 600-1000 |
| B13 (optional) | `Computational/PqxdhServerAuthRecordOracles` | record oracles simulatable from the reveal, using `RawCtxServerSend`/`RawCtxServerMixed` | B4a | 1000-2000 |
| B11 | docs | plain-English explanation in `doc/formal-verification-analysis.md` (new proofs), both assumption lists, the replaced table row, an implementation record `doc/impl/server-authentication.md` and README counts; `make -C beaconcrypt-core verify` and `check-inventory` once for the milestone | B10 (or B10a) | — |

Estimated total: 20k to 32k lines, against 13k in revision 1.

Critical path: B1 → B3a → B4a → B5a (gate) → B8b → B9b → B10a → B10 → B11. The spike S must finish before B8b starts. B5a is a gate for the stages that depend on the experiment definitions (B6, B7, B8b, B9b). If `negative_control` or `relay_not_win` fails, the definitions are fixed before those stages start. B8a and B9a are generic component lemmas and do not wait for the gate. The native equality (B3b/B4b) is off the critical path, and only `server_authentication_actual` needs it.

Concurrency, for a 16 GB machine shared with two other proof agents:

- At most two compile-heavy stages run at once.
- All `lake env lean` checks across agents are serialized through one lock, for example `flock /tmp/bc-arc-scratch/lean.lock timeout 1200 lake env lean …`. No `lake build` runs during the stages.
- `BeaconcryptCore.lean` and the inventories are merged once per wave.

| Wave | Stages (≤ 2 compile-heavy) |
| --- | --- |
| 1 | B1, B2 |
| 2 | B3a, S |
| 3 | B4a, B8a |
| 4 | B5a (gate), B9a |
| 5 | B8b, B6 |
| 6 | B8b (continued), B7 if approved, else B5b |
| 7 | B9b, B3b/B4b |
| 8 | B10a, B5b or B7 (whichever is left) |
| 9 | B10, optional B12 or B13 |
| 10 | B11, `make -C beaconcrypt-core verify`, `check-inventory` |

## 8. Risks, open questions and flags

### 8.1 Decisions and confirmations

Items 1 to 3 need the owner's input; items 4 to 10 are confirmations.

1. **Approve `X25519ScalarSpread` (needs owner input).** Two Server sessions with equal root inputs seal different plaintexts under the same (K1, N1). This is a real ChaCha20-Poly1305 nonce-reuse attack, and the CTX challengers refuse the repeated nonce, so `Pr[CollB]` must be charged. None of Gap-DH, the Extract random oracle and the class law bounds it. The spread law (6.4) is a functional counting fact about clamped X25519, and the review confirmed it; it gives `C(Q,2)·64/2^256 < 2^-241` at `Q = 32`. Without approval, `server_authentication_coll` (B10a) is the final statement, with `sessionCollGame` as a named, unevaluated game term, as Milestone C did with `collGame`. B7 and B10 wait for this decision. Nothing else does.
2. **Approve `NonzeroHonestDh` for the negative controls only (needs owner input).** Without approval, the controls carry an explicit `zeroDhGame` term, which the witness evaluates to 0 (section 4).
3. **Accept and build: combined or split (needs owner input).** The plan text fixes one combined oracle (`cbinds.rs:280-291`), but the public `ProviderServer` trait and the persistence wrappers expose `get_shared_secret` and `build_registration_response` separately. An exact reduction from split to combined is not available without a further functional law (restriction 5 in 1.3). Recommendation: model two oracles, `.accept phase1 : Option Unit` and `.build payload`, with a pending list in `GameState`. The proof technique is unchanged, because the acceptance-frozen event already handles seals after acceptance. The cost is about 400-700 more lines in B4a and B8b (one more placeholder). If the owner keeps the combined oracle, restriction 5 stays in the docstring and the row.
4. Post-acceptance corruption: listed as a restriction by default, with optional stage B12. Recommended only if time allows, because `win_frozen` already makes it a formality.
5. No KEM correctness term in the upper bound. Partnering is on the root input, so the upper bound never needs `decaps` to agree with `encaps`. The KEM error appears only in the controls. IND-CCA is not needed either, since the reduction knows SS.
6. No weak-EUF term. Partnering on the root input removes the need.
7. Index sum. W2 needs the selected CTX key at the partner, which is known only when the Beacon finishes, so the KDF and CTX terms are summed over `Q + 1` table owners, with no guessing factor inside any reduction.
8. Record oracles: an explicit argument in the docstring and analysis by default, with optional Lean stage B13.
9. Class-law domain: the checked form quantifies over all byte strings (6.3, item 5).
10. The plan's "implied by Gap-DH" sentence is corrected (6.6). The owner should know that the assumption is a strengthening of Gap-DH. It is still the assumption the owner chose (`PqxdhJointGapDh.game`), described accurately.

### 8.2 Technical risks

- B8b is the largest item. It needs a key-free continuation of the whole run for one table entry, on both the Server-send and the Beacon-receive halves. `PqxdhSelectedInitialOwnerCompiler` and `RawCtxSelectedInitialSecond` cover only the Beacon-owner orientation of HB-112; the spike S tests the Server-send half first.
- `history_erase` must also drop the root Expand `.publicHmac` entries and the `R_j` cache entry. B8b must check that no handler branch reads the family history (the `rom_*` lemmas read only the cache).
- No end-to-end CTX completeness lemma (seal, then raw open through the shared cache) was found. B5a must prove `ctx_seal_open`.
- `sym_complete` relies on first-match lookup on both sides. If `HmacOracle.randomOracle`'s cache semantics differ from first-wins insertion on duplicates, the invariant-gated projection lemma is used instead.
- The CTX step's `qHashCtx` includes honest hashes. The constants come from `PqxdhServerRegistrationPublication.native_build_bounds` and `PqxdhBeaconPhase2Bounds`.
- `reveal_post_registration` must confirm that the published kernel's material slots hold no sequence-one material.
- The Beacon's raw receive may accept a frame with sequence 2 or more under keys derived from the revealed `chain_1`. `afterOpening` rejects it (`beacon.rs:468`), and B9b must route such attempts as known-key attempts.
- B12's truncation needs the lemma that a component the continuation never writes has a point distribution after the continuation. This holds because VCVio's `OracleComp` has no failure, so every run has total mass one.

### 8.3 Open questions

- Should `Q` also be enforced inside the game, so that sessions beyond `Q` answer `none`, in addition to the `Budget` premise?
- Later records the Beacon accepts: a follow-up B14 composing this experiment with Milestone C's first-record integrity, in the Server-to-Beacon direction.
- Several target Beacons: state the union bound as a corollary, or leave it to the documentation?
- Should `actual_source_order` be proved, or should the independent-draw order stay?

## 9. Critique responses

1. Gap-DH wording (major): **accepted.** Section 6.1 now describes the services as answering on the twist and on non-canonical encodings under the same clamped scalar. It calls the assumption a strengthening of textbook Gap-DH, gives the ℓ/ℓ' and clamping plausibility, and cites Bernstein (PKC 2006) and RFC 7748. It keeps `scanClient_signing = 0`. The plan's sentence is scheduled for correction (6.6); it is not edited here because this task is read-only.
2. Collision term (major): **accepted.**
   - `Coll` is narrowed to `CollB` (two sessions share the Beacon's root input), which is all that H_j needs.
   - `server_authentication_coll` keeps `sessionCollGame` as a named game term, so the headline survives a rejection of the spread law.
   - `X25519ScalarSpread` and `NonzeroHonestDh` are separate decisions (8.1.1, 8.1.2). They are added to the doc lists only after approval.
   - The spread definition moves from B2 into the gated B7.
3. Stage plan (major): **accepted.**
   - A Server-send spike S runs in wave 2, before B8b, and re-estimates B8b and B9b.
   - B3/B4 are split, with the native equality in B3b/B4b off the critical path.
   - B5a (`negative_control` and `relay_not_win`) is a gate.
   - Every stage has an intermediate theorem with explicit game terms.
   - Sizes are raised to 5000-8000 (B8b) and 3500-5500 (B9b), for a total of 20-32k.

   One refinement: the gate applies to the experiment-dependent stages B6, B7, B8b and B9b. B8a and B9a are generic component lemmas that read no experiment definition, so holding them back would only lengthen the schedule.
4. Concurrency (minor): **accepted.** At most two compile-heavy stages run at once, all `lake env lean` checks are serialized through one lock, and inventories are merged once per wave.
5. Final-ghost event (minor): **accepted.**
   - `Ghost.acceptance` stores a frozen snapshot of the logs at acceptance.
   - Partner and W2 read only the snapshot, and W3 (two partners) is part of `Win`, charged to `CollB`.
   - This is checked in `EventCheck.lean` (`win_frozen`, `w3_collB`, axioms `[propext, Quot.sound]`).

   The snapshot also makes H_j's "prior seal" definitional, and it yields `owner_cases`: owner is a session ⇒ W2, owner is the Beacon ⇒ W1. For post-acceptance corruption I chose a truncation corollary (optional B12) over a Gap-DH reduction that stops at the finish. With the event frozen, truncation handles every reduction at once, and the headline reductions stay unchanged. Until B12 exists, the documentation lists the restriction.
6. Unjustified restrictions (minor): **accepted, with one partial disagreement on (b).**
   - (a) Record oracles: restriction 4 gives the simulation argument (deterministic in the revealed kernel, hashes through `.hash`, ratchet Extract outside the table, no effect on the Beacon or the seals). The Lean version is optional B13.
   - (c) Payload: the query now takes `Option Pqxdh.Bytes`, exactly Rust's `data`, so `none` reaches `REGISTRATION_WITNESS` without an argument.
   - (b) Split accept and build, partial disagreement: the key-ID-order argument is not enough on its own. The split interface also shows the adversary the derive outcome before the build, and in the abstract model that outcome can depend on the fresh ephemeral (a zero-DH check). It is public only for real X25519. So restriction 5 states the argument honestly, and the choice goes to the owner with a recommendation to model two oracles (8.1.3).
7. Negative controls (minor): **accepted, with one correction.** `relay_not_win` cannot be `Pr[Win] = 0` under the control laws alone. When decapsulation disagrees, the Beacon derives another root, and the abstract AEAD has no law that stops a wrong key from opening. The statement is therefore `Pr[Win] ≤ kemError` (in the gate B5a), and `relay_zero` gives 0 at the witness (B5b). `preseal_reveal_control` is added in B5b as a separate handler, so the headline handler is unaffected.
8. Class-law note (minor): **accepted, with one arithmetic correction.** Section 6.3 now covers the same-curve fact, the torsion fact, zero outputs, non-canonical encodings with the masked bit, and the length artefact. Correction: the multiples of ℓ' in `[2^254, 2^255)` are 3ℓ' and 4ℓ', not 2ℓ' and 3ℓ'. 2ℓ' = 2^254 − 18 − 4δ lies below 2^254 (computed with ℓ = 2^252 + δ, ℓ' = 2^253 − 9 − 2δ, and 2(p+1) − 8ℓ = 4ℓ'). 3ℓ' is odd and 4ℓ' ≡ 4 mod 8, so the conclusion is unchanged.
9. Extract random-oracle note (minor): **accepted.** Section 6.2 now derives the restricted idealization from modelling the whole fixed-zero-key HMAC as a random oracle, and notes that the 32-byte Extract games hold there and that length padding separates input lengths. The key remark is rephrased by RFC 2104 and RFC 5869, with no library internals.
10. B6/B8b gaps (minor): **accepted.**
    - (a) `history_erase` (B8b) projects away the family history and the `R_j` cache entry before `entry_factor`.
    - (b) Instead of an ordered equality used by A2, `CandHit` is now defined directly on the family history, which is exactly the list `scanClient` outputs, so A2 needs no list lemma. A1 uses `touches_history` (the lockstep equality of the adversary subsequences, with `honest_no_rom_public`) and `candidates_length`, both in B6.
11. Documentation plan (minor): **accepted.** The existing row at `composition-assumptions.md:42` is replaced rather than duplicated. The new row names the class law, the spread law, the Extract random oracle, the simulatable record oracles, the combined accept and build, and the corruption restriction. The numerical reading now leads with `33 · qHashCtx / 2^128 ≈ 2^-59` at `qHash = 2^64`, and counts the 264 constructed-reduction advantages.

I disagree with none of the critique's conclusions about soundness. The review's statements on partner reveals, sequence-one forgery, the W2 direction and Rust fidelity are consistent with this design. The note that a sealed but unsent record counts as a legitimate partner output is documented as restriction 10.

## 10. Spike S results (2026-09-29)

Source: /tmp/bc-arc-scratch/c-work/spike/SpikeServerSend.lean (574 lines, no sorry, compiles through the lock, standard axioms only) and spike/notes.md.

- `server_send_factor` proves the Server-send half of `entry_factor`: for any aux handler, the native registration build run through `registrationImpl` equals `factored source writer aux (factor source root) …`, an equality of the whole run (response, Server peers, aux state, CTX cache). `root_only_through_factor` and `factor_bytes` show the factor is exactly the design's 108-byte `f` (the 76-byte chain_0 step response and second32 of the initializer), using only `source.prefixConsistent`. `prim_send_source` generalizes the chain placeholder to any lawful monad and seal primitive. Beacon-side checks `initial_factor_beacon` and `beacon_receive_factor` show one challenge serves both halves.
- Placeholder interface: `Factor := RatchetKdfResponse × RootOutput`; chain_0 is `RawCtxSelectedChain.Slot.hidden`, stepped by `factor.1` through `RawCtxSelectedChain.calls`; the initializer is `RawCtxSelectedInitialConstructor.initial false factor.2`; output kernels are resolved by a fixed interpretation that never uses chain_0, justified by settlement (every published kernel has both chains known). B8b must prove Beacon settlement or project the Beacon kernel away (`Win` reads only the ghost). The derive reply needs a sum-typed reply or a sentinel root plus a per-session flag.
- Transfer: for B8b the existing HB-112 builder machinery (`PqxdhInitialGenericBuilder.candidate_native`, `PqxdhInitialGenericPublication.after_native`, `RawCtxSelectedChain.send_source`/`receive_source`, `RawCtxSelectedInitialConstructor`) already covers the Server-send orientation. For B9b only partly: selected seals in the Server orientation exist (`RawCtxSelectedSendCompiler.send_source`/`native_send`, `RawCtxSelectedSealConsumer`), but C's builder compile is only under `KnownSend` and its message layer is address-based; keeping "no alias term" needs an address-free material layer (`RawCtxChainRealization.send_execute`/`receive_execute`, `RawCtxSelectedMessageKey.decoded_selected`).
- Split accept/build: the spike's results do not depend on it; splitting adds 300-500 lines of pending bookkeeping in `game_factor` and needs a check that `build` consumes the pending (no double seal under one (K1, N1)).
- New lemmas for B8b: port `cut_source`, `build_native`, `initial_factor`, `send_shape`, `settle_*`, `server_send_factor`, `prim_send_source`, `factor_bytes`; handler-level copies `after_tail`, `candidate_tail`, `build_tail`; `session_factor`, `beacon_finish_factor`, `history_erase`, `entry_programmed`, `owner_partition`, `owner_cases`, `game_factor`, `entry_le_uniform`. For B9b: `key_first`, `material_labels_send`/`material_labels_receive`, `compiled_build_selected` (state relation "Clean plus exactly one selected seal", new), `compiled_owner_free`, `ctxClient j`, `ctx_compiled`, `ctx_budgets`, `event_won` (main risk, analogue of C's gap game), `uniformEntry_le_ctx`.
- Re-estimates: B8b 5000-7500 lines (Server-send part now low risk; remaining risk in `game_factor`, `entry_programmed` and the Beacon half); B9b 4000-6500 lines. `server_send_factor` is stated in `StateT (SharedState A) ProbComp`; B4a should define the Server tail as a lifted ProbComp computation or use the generic-monad `prim_send_source`.

- Name clashes (review B8a): realGame, step, uniformGame, initializer, Output, withContext exist in other namespaces (PqxdhJointDhExtractFamily, RawCtxSelectedChain, ...); B8b must use qualified PqxdhServerAuthKeySchedule.* names.
- B4a re-check (2026-09-30): ghost session touches now log the derive reply (the root), so B8b's `history_erase` must also erase the replies in `ghost.touches` and in the acceptance snapshot's touches (in addition to the family history, the root Expand entries, the R_j cache entry and the pending-root placeholder); the reviewer's scratch `/tmp/bc-arc-scratch/c-work/recheck-b4a-regressions-erase.lean` shows Win, BadB, CollB, entryOwner and EntryEvent are unchanged under that erasure. The seal-to-root link beyond `sealTouched` (touch with `some root`) is left to B9b's `compiled_build_selected`.
- B5a witness: /tmp/bc-arc-scratch/c-work/b5a/WitnessCheck.lean (toy instance with x25519 := replicate 32 1, wired sign/verify, toyKem, injective codec; proves control_wins, relay_loses, relay_accepts with kemError = 0); B5b should start from it. F6's toyCrypto fails NonzeroHonestDh and cannot be wired, so B5b must replace x25519 and sign/verify.
