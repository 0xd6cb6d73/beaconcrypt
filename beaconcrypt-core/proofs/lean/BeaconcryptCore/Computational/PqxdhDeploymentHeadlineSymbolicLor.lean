-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor

/-!
# `symbolic_lor` (CE-12 P2, design-v2 section 7.5; F-ct2 form)

The symbolic left-or-right corollary of CE-LOR with the public NoBundleFailure filter (plan section 19). The symbolic eligibility `e_sym` (`LorEligSym`) is: a Server was constructed, a test session exists, the run has no rejected bundle call in Fresh, and every admitted test handle is symbolically eligible (`SymServer` for a Server peer with the final native identity keys, `SymBeacon` for an owner pinned to the constructed Server and the protected key ID); `LorWinSym` adds a correct guess of the test bit. CE-LOR's eligibility is `PqxdhDeploymentHeadlineEvents.LorElig` with the filter `nbfFilter` (NoBundleFailure read on the mode-P view, `nbfFilter_iff`).

- Inclusion (`lor_inclusion`, design-v2 `e_CE ∧ NBF ⊆ e_sym ∧ NBF`): a designated handle on a NoBundleFailure run is symbolically eligible (`designated_sym`: a designated peer's accepted identity key is the designated owner's, whose honest bundle carries it; a designated owner's linked build response carries the constructed Server's identity, `build_pin`).
- Difference (`lor_difference`): symbolic eligibility without CE eligibility is a gap (an admitted handle undesignated, `ServerGap`/`BeaconGap`) or a movement of designation after an admission. Admitted tests share the first test's session at admission (`SameSession`), the ledger's test session starts at the first admissible test (`ledgerInv_game`, from `PqxdhRecordLiftFlat.ledger_inv`), and designations of a prefix move only by `moves` (`peer_moves`: the designated owner decreases only when two distinct owners published one identity field, `SameField`, an identity collision on every outcome, `field_collision`; `owner_moves`: the designated session decreases only when two sessions carry the owner's ciphertext to its published PQ key, `CtCollAt`), using prefix stability of the transcript functions (`findSome_prefix`, `owners_prefix`, `publishes_prefix`, `linked_prefix`).
- `symbolic_lor_le`: the two advantages (`Pr[W] − ½Pr[E]`) differ by at most half the probability of the difference event (nested sets, `nested_arith`). `lor_difference_bound`: that probability is at most `ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ctCollTerm` (`sym_gap`, `identity_collision_game`). `symbolic_lor`: `|adv_sym − adv_CE| ≤ ½(ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ctCollTerm)`; `symbolic_lor_bound`: `|adv_sym| ≤` CE-LOR's bound at `nbfFilter` `+ ½(…)`.
- Server-side form (every admitted test handle a Server peer, CE-LOR's `PeerTests`; `LorEligPeerSym`, `LorWinPeerSym`): the difference is a Server-side gap or an identity collision (`lor_difference_peer`: an undesignated admitted peer is `ServerGap`, and a peer's designation moves only by `SameField`; neither the Beacon-side gap nor `CtColl` arises). `symbolic_lor_server_le`, `lor_difference_server_bound` (`ε_A2pub + ε_inj`), `symbolic_lor_server`: `|adv_sym_peer − adv_CE_peer| ≤ ½(ε_A2pub + ε_inj)`; `symbolic_lor_server_bound`: `|adv_sym_peer| ≤` `ce_lor_server`'s bound at `nbfFilter` (no `β_g`) `+ ½(ε_A2pub + ε_inj)`. No explicit term and no CE-A1 premise on this side.

Explicit terms (`symbolic_lor`, `symbolic_lor_bound` only): `ctGapTerm` (F-ct2: the D-ct spike stopped, design-v2 section 8) and `ctCollTerm` (design-v2 section 7.4's `ε_ctcoll` needs the game-level `ct_collision_game`, not proved). No `StableTest` condition. No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailure NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (protectedBinding)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt IdentityCollision)
open PqxdhDeploymentHeadlineSymbolic (SymHandle)
open PqxdhRecordLiftIdeal (firstTest AdmittedTest admissibleTest)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### Prefix stability and monotonicity of the public transcript functions -/

section Prefix
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)

/-- A search that finds a value in a prefix finds the same value in every extension. -/
theorem findSome_prefix {α β : Type} (f : α → Option β) (before rest : List α) (value : β)
    (found : before.findSome? f = some value) : (before ++ rest).findSome? f = some value := by
  rw [List.findSome?_append, found]
  rfl

/-- The created owners of a prefix are a prefix of the created owners of the transcript. -/
theorem owners_prefix (before rest : List Entry) :
    (summarize before).owners <+: (summarize (before ++ rest)).owners := by
  rw [PqxdhDeploymentServerAuthEvent.summarize_regs, PqxdhDeploymentServerAuthEvent.summarize_regs]
  simp only [PqxdhDeploymentServerAuthEvent.regsOf, List.filterMap_append]
  rw [PqxdhDeploymentServerAuthEvent.summarizeReg_append]
  exact PqxdhDeploymentHeadlineGap.owners_foldl_prefix _ _

/-- The number of accept attempts only grows. -/
theorem acceptCount_prefix (before rest : List Entry) : acceptCount before ≤ acceptCount (before ++ rest) := by
  unfold acceptCount
  rw [List.countP_append]
  exact Nat.le_add_right _ _

/-- `Publishes` is stable under extension. -/
theorem publishes_prefix (before rest : List Entry) (accepted : PqxdhEd25519EufCma.Phase1Candidate)
    (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (k : Nat) (holds : Publishes codec before accepted pqKey k) :
    Publishes codec (before ++ rest) accepted pqKey k := by
  obtain ⟨published, found, identity, pq⟩ := holds
  obtain ⟨bytes, bytesFound, read⟩ := Option.bind_eq_some_iff.mp found
  exact ⟨published, by rw [bundleOf, findSome_prefix _ before rest bytes bytesFound]; exact read, identity, pq⟩

/-- `Linked` is stable under extension. -/
theorem linked_prefix (before rest : List Entry) (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (session : Nat)
    (holds : Linked crypto codec before ciphertext pin pqKey session) :
    Linked crypto codec (before ++ rest) ciphertext pin pqKey session := by
  obtain ⟨response, accepted, keys, built, ct, pinned, acceptFound, keysFound, pq⟩ := holds
  obtain ⟨raw, rawFound, read⟩ := Option.bind_eq_some_iff.mp acceptFound
  exact ⟨response, accepted, keys, findSome_prefix _ before rest response built, ct, pinned,
    by rw [acceptOf, findSome_prefix _ before rest raw rawFound]; exact read, keysFound, pq⟩

/-- A linked session carries its ciphertext to its PQ key. -/
theorem linked_carries (transcript : List Entry) (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (session : Nat)
    (holds : Linked crypto codec transcript ciphertext pin pqKey session) :
    CarriesTo crypto codec transcript ciphertext pqKey session := by
  obtain ⟨response, accepted, keys, built, ct, _, acceptFound, keysFound, pq⟩ := holds
  exact ⟨response, accepted, keys, built, ct, acceptFound, keysFound, pq⟩

/-- Two distinct owners whose first published bundles carry the same identity field. -/
def SameField (transcript : List Entry) (k k' : Nat) : Prop :=
  k ≠ k' ∧ ∃ published published', (bundleOf transcript k).bind (candidateOf codec) = some published ∧
    (bundleOf transcript k').bind (candidateOf codec) = some published' ∧ published.identityKey = published'.identityKey

/-- Movement of an owner's designation (design-v2 section 7.5 (b)): between a prefix and its extension the designated session can only decrease, and when it does two sessions carry the owner's ciphertext to its published PQ key (`CtColl`). -/
theorem owner_moves (before rest : List Entry) (c : Nat) (session session' k k' : Nat)
    (early : designate crypto codec serverKid before (.owner c) = some (session, k))
    (late : designate crypto codec serverKid (before ++ rest) (.owner c) = some (session', k')) :
    k' = k ∧ (session' = session ∨ ∃ j, CtCollAt crypto codec (before ++ rest) c session' j) := by
  obtain ⟨kc, _, pin, raw, ciphertext, published, pqKey, binding, finished, ciphertextFound, publishedFound, pqFound,
    bound, linked⟩ := PqxdhDeploymentTranscript.designate_owner crypto codec serverKid before c session k early
  obtain ⟨kc', established', pin', raw', ciphertext', published', pqKey', binding', finished', ciphertextFound',
    publishedFound', pqFound', _, linked'⟩ :=
    PqxdhDeploymentTranscript.designate_owner crypto codec serverKid (before ++ rest) c session' k' late
  refine ⟨kc'.trans kc.symm, ?_⟩
  obtain ⟨extra, extraEq⟩ := owners_prefix before rest
  rw [← extraEq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp binding).1, binding, Option.some.injEq,
    Prod.mk.injEq] at binding'
  obtain ⟨rfl, _⟩ := binding'
  have finishedLate : finishOf (before ++ rest) c = some raw := by
    unfold finishOf at finished ⊢
    exact findSome_prefix _ before rest raw finished
  rw [finishedLate, Option.some.injEq] at finished'
  subst finished'
  rw [ciphertextFound, Option.some.injEq] at ciphertextFound'
  subst ciphertextFound'
  obtain ⟨bytes, bytesFound, read⟩ := Option.bind_eq_some_iff.mp publishedFound
  have stable : (bundleOf (before ++ rest) c).bind (candidateOf codec) = some published := by
    rw [bundleOf, findSome_prefix _ before rest bytes bytesFound]
    exact read
  rw [stable, Option.some.injEq] at publishedFound'
  subst publishedFound'
  rw [pqFound, Option.some.injEq] at pqFound'
  subst pqFound'
  have extended := linked_prefix crypto codec before rest ciphertext pin pqKey session linked
  obtain ⟨first, firstLe, firstFound⟩ := PqxdhDeploymentTranscript.designate_owner_complete crypto codec serverKid
    (before ++ rest) c pin raw ciphertext published pqKey session established' (by
      rw [← extraEq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp binding).1]; exact binding)
    finishedLate ciphertextFound stable pqFound (lt_of_lt_of_le bound (acceptCount_prefix before rest)) extended
  rw [late, Option.some.injEq, Prod.mk.injEq] at firstFound
  obtain ⟨sessionEq, _⟩ := firstFound
  subst sessionEq
  by_cases same : session' = session
  · exact Or.inl same
  · exact Or.inr ⟨session, lt_of_le_of_ne firstLe same, ciphertext, published, pqKey, stable, pqFound,
      linked_carries crypto codec _ ciphertext pin pqKey session' linked',
      linked_carries crypto codec _ ciphertext pin pqKey session extended⟩

/-- Movement of a Server peer's designation (design-v2 section 7.5 (b)): between a prefix and its extension the session is fixed and the designated owner can only decrease, and when it does two distinct owners published the same identity field. -/
theorem peer_moves (before rest : List Entry) (keyId : Aeneas.Std.U64) (session session' k k' : Nat)
    (early : designate crypto codec serverKid before (.peer keyId) = some (session, k))
    (late : designate crypto codec serverKid (before ++ rest) (.peer keyId) = some (session', k')) :
    session' = session ∧ (k' = k ∨ SameField codec (before ++ rest) k' k) := by
  obtain ⟨response, raw, accepted, keys, linked, rawFound, acceptedFound, keysFound, created, publishes⟩ :=
    PqxdhDeploymentTranscript.designate_peer crypto codec serverKid keyId before session k early
  obtain ⟨response', raw', accepted', keys', linked', rawFound', acceptedFound', keysFound', _, publishes'⟩ :=
    PqxdhDeploymentTranscript.designate_peer crypto codec serverKid keyId (before ++ rest) session' k' late
  rw [linkOf, findSome_prefix _ before rest _ linked, Option.some.injEq, Prod.mk.injEq] at linked'
  obtain ⟨rfl, rfl⟩ := linked'
  refine ⟨rfl, ?_⟩
  rw [acceptOf, findSome_prefix _ before rest raw rawFound, Option.some.injEq] at rawFound'
  subst rawFound'
  rw [acceptedFound, Option.some.injEq] at acceptedFound'
  subst acceptedFound'
  rw [keysFound, Option.some.injEq] at keysFound'
  subst keysFound'
  have extended := publishes_prefix codec before rest accepted keys.2.pqKey k publishes
  obtain ⟨extra, extraEq⟩ := owners_prefix before rest
  obtain ⟨first, firstLe, firstFound⟩ := PqxdhDeploymentTranscript.designate_peer_complete crypto codec serverKid keyId
    (before ++ rest) session response raw accepted keys k (by rw [linkOf, findSome_prefix _ before rest _ linked])
    (by rw [acceptOf, findSome_prefix _ before rest raw rawFound]) acceptedFound keysFound
    (by rw [← extraEq, List.length_append]; omega) extended
  rw [late, Option.some.injEq, Prod.mk.injEq] at firstFound
  obtain ⟨_, kEq⟩ := firstFound
  subst kEq
  by_cases same : k' = k
  · exact Or.inl same
  · obtain ⟨published, found, identity, _⟩ := publishes'
    obtain ⟨published', found', identity', _⟩ := extended
    exact Or.inr ⟨same, published, published', found, found', by rw [identity, identity']⟩

end Prefix

/-- Movement of any handle's designation between a prefix and its extension: it stays, or two distinct owners published the same identity field, or two sessions carry one ciphertext to an owner's published PQ key. -/
theorem moves (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    (before rest : List Entry) (handle : Handle) (early late : Nat × Nat)
    (earlyFound : designate crypto codec serverKid before handle = some early)
    (lateFound : designate crypto codec serverKid (before ++ rest) handle = some late) :
    late = early ∨ (∃ k k', SameField codec (before ++ rest) k k') ∨
      ∃ c i j, CtCollAt crypto codec (before ++ rest) c i j := by
  cases handle with
  | peer keyId =>
      obtain ⟨sessionEq, same | field⟩ := peer_moves crypto codec serverKid before rest keyId early.1 late.1 early.2 late.2
        earlyFound lateFound
      · exact Or.inl (Prod.ext sessionEq same)
      · exact Or.inr (Or.inl ⟨_, _, field⟩)
  | owner c =>
      obtain ⟨kEq, same | ⟨j, coll⟩⟩ := owner_moves crypto codec serverKid before rest c early.1 late.1 early.2 late.2
        earlyFound lateFound
      · exact Or.inl (Prod.ext same kEq)
      · exact Or.inr (Or.inr ⟨c, late.1, j, coll⟩)

/-! ### The NoBundleFailure filter and the symbolic LOR events -/

section Events

open Classical in
/-- The public filter `NoBundleFailure` on the mode-P transcript view (design-v2 section 7.5): some transcript with this view has no rejected bundle call in Fresh. Since `NoBundleFailure` depends only on the mode-P view (`PqxdhDeploymentTranscript.phase_view`), on a transcript's own view it is exactly `NoBundleFailure` of the transcript (`nbfFilter_iff`). -/
noncomputable def nbfFilter (view : List (PqxdhDeploymentInterface.PublicEntry .P)) : Bool :=
  decide (∃ transcript : List Entry, transcript.map (Entry.view .P) = view ∧ NoBundleFailure transcript)

/-- On a transcript's own mode-P view, the filter is `NoBundleFailure` of the transcript. -/
theorem nbfFilter_iff (transcript : List Entry) :
    nbfFilter (transcript.map (Entry.view .P)) = true ↔ NoBundleFailure transcript := by
  classical
  simp only [nbfFilter, decide_eq_true_eq]
  constructor
  · rintro ⟨other, same, clean⟩
    exact ((PqxdhDeploymentTranscript.phase_view other transcript same).2.2).mp clean
  · intro clean
    exact ⟨transcript, rfl, clean⟩

/-- `e_sym` (design-v2 section 7.5): a Server was constructed, a test session exists, the run has no rejected bundle call in Fresh, and every admitted test handle is symbolically eligible. -/
def LorEligSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧ final.1.test.isSome ∧
    NoBundleFailure final.1.transcript ∧
    ∀ before entry after handle left right, final.1.transcript = before ++ entry :: after →
      entry.query = .inr (.test handle left right) →
      AdmittedTest setup.source.crypto codec setup.serverKeyId before handle left right →
      SymHandle setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native)
        (protectedBinding setup created).1 setup.serverKeyId handle

/-- `e_sym` and a correct guess of the test bit. -/
def LorWinSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (guess : X → Bool)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  LorEligSym setup codec outcome ∧ ∃ created output final, outcome.1 = some (created, output, final) ∧
    final.1.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess output)

open Classical in
/-- `LorEligSym` as a Boolean of the outcome. -/
noncomputable def lorEligSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (LorEligSym setup codec outcome)

open Classical in
/-- `LorWinSym` as a Boolean of the outcome. -/
noncomputable def lorWinSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (guess : X → Bool)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (LorWinSym setup codec guess outcome)

/-- The Server-side `e_sym`: `e_sym` with every admitted test handle a Server peer (CE-LOR's `PeerTests` on the final observation, the condition of `ce_lor_server`). -/
def LorEligPeerSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  LorEligSym setup codec outcome ∧ ∃ created output final, outcome.1 = some (created, output, final) ∧
    PqxdhDeploymentHeadlineEvents.PeerTests setup.source.crypto codec setup.serverKeyId (output, final.1, final.2.produced)

/-- The Server-side `e_sym` and a correct guess of the test bit. -/
def LorWinPeerSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (guess : X → Bool)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  LorEligPeerSym setup codec outcome ∧ ∃ created output final, outcome.1 = some (created, output, final) ∧
    final.1.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess output)

open Classical in
/-- `LorEligPeerSym` as a Boolean of the outcome. -/
noncomputable def lorEligPeerSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (LorEligPeerSym setup codec outcome)

open Classical in
/-- `LorWinPeerSym` as a Boolean of the outcome. -/
noncomputable def lorWinPeerSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (guess : X → Bool)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (LorWinPeerSym setup codec guess outcome)

end Events

/-! ### Support facts -/

section Support

/-- On every outcome of the experiment the ledger's test session starts at the first admissible test of the transcript (`PqxdhRecordLiftFlat.ledger_inv` along the run). -/
theorem ledgerInv_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) :
    PqxdhRecordLiftFlat.LedgerInv final.1 := by
  simp only [PqxdhDeploymentSecrecy.game, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, _, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    cases reached
    have invariant := OracleComp.simulateQ_run_preserves_inv_of_query
      (PqxdhDeploymentSecrecy.handler setup codec checks route constructed.seed bounds)
      (fun state => PqxdhRecordLiftFlat.LedgerInv state.1)
      (fun query state holds result member => by
        rcases state with ⟨ledger, native⟩
        rw [PqxdhDeploymentEligibility.handler_run, support_map] at member
        obtain ⟨reached, reachedMember, rfl⟩ := member
        have value : reached.1 ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec
            setup.serverKeyId bounds query).run ledger) := by
          apply OracleComp.support_simulateQ_run'_subset
            (PqxdhDeploymentNative.handler setup codec checks route constructed.seed) _ native
          rw [StateT.run'_eq, support_map]
          exact ⟨reached, reachedMember, rfl⟩
        exact PqxdhRecordLiftFlat.ledger_inv setup.source.crypto codec setup.serverKeyId bounds query ledger holds
          reached.1 value)
      (PqxdhDeploymentInterface.asModeO mode adversary)
      (PqxdhDeploymentSecrecy.Ledger.empty, PqxdhDeploymentNative.initial constructed)
      PqxdhRecordLiftFlat.ledgerInv_empty _ executedMember
    exact invariant

/-- `encodedIdentity` is injective. -/
theorem encodedIdentity_injective (first second : PqxdhEd25519EufCma.Ed25519PublicKey)
    (same : PqxdhEd25519EufCma.encodedIdentity first = PqxdhEd25519EufCma.encodedIdentity second) : first = second := by
  have parsed := PqxdhEd25519EufCma.parseIdentity_encodedIdentity first
  rw [same, PqxdhEd25519EufCma.parseIdentity_encodedIdentity] at parsed
  exact (Option.some.inj parsed).symm

/-- On a transcript in `Agree` with the native state, the first published bundle of an owner carries the encoding of that owner's identity key (`Phase1ReadBack`). -/
theorem bundle_identity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (server : RawCtxServerRouting.Identity)
    (transcript : List Entry) (native : PqxdhRegistrationSchedule.State KemSK)
    (agree : PqxdhDeploymentEligibility.Agree setup codec server transcript native) (k : Nat)
    (published : PqxdhEd25519EufCma.Phase1Candidate)
    (found : (bundleOf transcript k).bind (candidateOf codec) = some published) :
    ∃ owner : PqxdhRegistrationSchedule.Owner KemSK, native.owners[k]? = some owner ∧
      published.identityKey = PqxdhEd25519EufCma.encodedIdentity (setup.joint.publicKeys owner.beacon.identity).ed25519 := by
  obtain ⟨bytes, bytesFound, read⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨owner, keys, preSignature, oneSignature, pqSignature, ownerFound, written, _⟩ :=
    agree.bundles _ (PqxdhDeploymentKeyMatch.bundleOf_mem transcript k bytes bytesFound)
  rw [PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at read
  exact ⟨owner, ownerFound, by rw [← read]; rfl⟩

/-- On every outcome of the experiment, two distinct owners that published the same identity field are an identity collision of the final native identity seeds (`IdentityCollision`, bounded by `ε_inj`). -/
theorem field_collision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (k k' : Nat) (field : SameField codec final.1.transcript k k') :
    IdentityCollision setup outcome := by
  obtain ⟨different, published, published', foundK, foundK', same⟩ := field
  have agree := PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit 0 bounds mode adversary
    runtime outcome member created output final found
  obtain ⟨owner, ownerFound, identity⟩ := bundle_identity setup codec phase1 _ _ _ agree k published foundK
  obtain ⟨owner', ownerFound', identity'⟩ := bundle_identity setup codec phase1 _ _ _ agree k' published' foundK'
  refine ⟨created, output, final, found, k, k', different, owner.beacon.identity, owner'.beacon.identity, ?_, ?_, ?_⟩
  · simp [PqxdhDeploymentServerAuthInjective.identities, ownerFound]
  · simp [PqxdhDeploymentServerAuthInjective.identities, ownerFound']
  · exact encodedIdentity_injective _ _ (by rw [← identity, ← identity', same])

/-- On every outcome of the experiment, a designated handle on a run with no rejected bundle call in Fresh is symbolically eligible (design-v2 section 7.5, the inclusion `e_CE ∧ NBF ⊆ e_sym ∧ NBF`): a designated peer's accepted identity is the identity key of the designated owner `k`, whose honest bundle carries it (`Phase1ReadBack`); a designated owner is Established and pinned to the constructed Server, because its linked session's build response carries its pin and every build response carries the constructed Server's identity (`build_pin`). -/
theorem designated_sym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (clean : NoBundleFailure final.1.transcript) (handle : Handle)
    (target : Nat × Nat)
    (designated : designate setup.source.crypto codec setup.serverKeyId final.1.transcript handle = some target) :
    SymHandle setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native)
      (protectedBinding setup created).1 setup.serverKeyId handle := by
  have agree := PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit 0 bounds mode adversary
    runtime outcome member created output final found
  cases handle with
  | peer keyId =>
      obtain ⟨response, raw, accepted, keys, linked, rawFound, acceptedFound, keysFound, _, published, publishedFound,
        identityEq, _⟩ := PqxdhDeploymentTranscript.designate_peer setup.source.crypto codec setup.serverKeyId keyId
          final.1.transcript target.1 target.2 designated
      obtain ⟨owner, ownerFound, identity⟩ := bundle_identity setup codec phase1 _ _ _ agree target.2 published
        publishedFound
      refine ⟨target.1, response, raw, accepted, keys.1, keys.2, target.2, linked, rawFound, acceptedFound, keysFound,
        ?_, clean target.2⟩
      have encoded := PqxdhDeploymentHeadlineGap.acceptedKeys_identity _ accepted keys.1 keys.2 keysFound
      rw [← identityEq, identity] at encoded
      simp [ownerIdentities, ownerFound, encodedIdentity_injective _ _ encoded]
  | owner c =>
      obtain ⟨_, established, pin, _, _, _, _, binding, _, _, _, _, _, linked⟩ :=
        PqxdhDeploymentTranscript.designate_owner setup.source.crypto codec setup.serverKeyId final.1.transcript c
          target.1 target.2 designated
      obtain ⟨response, _, _, built, _, pinned, _, _, _⟩ := linked
      obtain ⟨payload, responseMember⟩ := PqxdhDeploymentKeyMatch.buildOf_mem _ _ response built
      have pinFound := PqxdhDeploymentServerAuth.build_pin setup codec checks route ensureInit 0 phase2 bounds mode
        adversary runtime outcome member created output final found _ payload response responseMember
      rw [pinned, Option.some.injEq] at pinFound
      rw [pinFound] at binding
      exact ⟨established, binding, clean c⟩

end Support

/-! ### The two containments of `symbolic_lor` -/

section Containments
open PqxdhDeploymentHeadlineEvents (LorElig)

/-- The inclusion `e_CE ∧ NBF ⊆ e_sym ∧ NBF` (design-v2 section 7.5) on every outcome of the experiment of a budget-respecting adversary: CE-LOR eligibility with the NoBundleFailure filter gives symbolic eligibility of every admitted test handle (`designated_sym`). -/
theorem lor_inclusion (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (g : Fin budget.accept × Fin budget.capacity)
    (eligible : LorElig setup.source.crypto codec setup.serverKeyId budget nbfFilter g (output, final.1, final.2.produced)) :
    LorEligSym setup codec outcome := by
  obtain ⟨tested, filtered, _, admitted⟩ := eligible
  have clean := (nbfFilter_iff final.1.transcript).mp filtered
  refine ⟨created, output, final, found, tested, clean, fun before entry after handle left right split query admits => ?_⟩
  exact designated_sym setup codec checks route ensureInit phase1 phase2 bounds mode adversary runtime outcome member
    created output final found clean handle _ (PqxdhDeploymentKemTransfer.designateIn_some _ codec _ budget _ _ g
      (admitted before entry after handle left right split query admits))

/-- The difference `(e_sym ∧ NBF) ∖ e_CE` (design-v2 section 7.5) on every outcome of the experiment of a budget-respecting adversary: symbolic eligibility without CE-LOR eligibility (NoBundleFailure filter) is a Server-side or Beacon-side gap (some admitted handle undesignated) or a movement of designation after a test's admission, which is an identity collision (`IdentityCollision`, two owners published one identity field) or a ciphertext collision (`CtColl`, a smaller session became linked). Admitted tests share the first test's session at admission (`SameSession`), the first admissible test is the ledger's test session (`ledgerInv_game`), and designations of a prefix move only as `moves` describes. -/
theorem lor_difference (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (holds : LorEligSym setup codec outcome) :
    happens (PqxdhDeploymentHeadlineEvents.lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter)
        outcome = true ∨
      ServerGap setup codec budget outcome ∨ BeaconGap setup codec budget outcome ∨ IdentityCollision setup outcome ∨
      happens (PqxdhDeploymentHeadlineCollision.ctCollEvent setup.source.crypto codec) outcome = true := by
  classical
  obtain ⟨created, output, final, found, tested, clean, symbolic⟩ := holds
  have observed : observeGame outcome.1 = some (output, final.1, final.2.produced) := by
    rw [found]
    rfl
  by_cases gaps : ServerGap setup codec budget outcome ∨ BeaconGap setup codec budget outcome
  · rcases gaps with gap | gap
    · exact Or.inr (Or.inl gap)
    · exact Or.inr (Or.inr (Or.inl gap))
  by_cases collision : IdentityCollision setup outcome
  · exact Or.inr (Or.inr (Or.inr (Or.inl collision)))
  by_cases coll : ∃ k i j, CtCollAt setup.source.crypto codec final.1.transcript k i j
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    simp only [happens, observed, Option.any_some, PqxdhDeploymentHeadlineCollision.ctCollEvent, decide_eq_true_eq]
    exact coll
  left
  have designatedOf : ∀ handle, SymHandle setup.source.crypto codec final.1.transcript
      (ownerIdentities setup final.2.native) (protectedBinding setup created).1 setup.serverKeyId handle →
      ∃ g, designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript handle = some g := by
    intro handle sym
    cases designatedFound : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript handle with
    | none =>
        exact absurd (PqxdhDeploymentHeadlineSymbolic.undesignated_gap setup codec budget outcome created output final
          found handle sym designatedFound) gaps
    | some g => exact ⟨g, rfl⟩
  have stays : ∀ (before rest : List Entry), final.1.transcript = before ++ rest → ∀ handle early late,
      designate setup.source.crypto codec setup.serverKeyId before handle = some early →
      designate setup.source.crypto codec setup.serverKeyId final.1.transcript handle = some late → late = early := by
    intro before rest split handle early late earlyFound lateFound
    rw [split] at lateFound
    rcases moves setup.source.crypto codec setup.serverKeyId before rest handle early late earlyFound lateFound with
      same | ⟨k, k', field⟩ | ⟨c, i, j, collAt⟩
    · exact same
    · rw [← split] at field
      exact absurd (field_collision setup codec checks route ensureInit phase1 bounds mode adversary runtime outcome
        member created output final found k k' field) collision
    · rw [← split] at collAt
      exact absurd ⟨c, i, j, collAt⟩ coll
  have inv := ledgerInv_game setup codec checks route ensureInit 0 bounds mode adversary runtime outcome member created
    output final found
  obtain ⟨state, stateFound⟩ := Option.isSome_iff_exists.mp tested
  have firstFound : firstTest final.1.transcript = some state.first := by
    unfold PqxdhRecordLiftFlat.LedgerInv at inv
    rw [← inv, stateFound]
    rfl
  obtain ⟨pre, entry₀, post, split₀, admissible₀, noneBefore⟩ := List.findSome?_eq_some_iff.mp firstFound
  have firstNone : firstTest pre = none := List.findSome?_eq_none_iff.mpr noneBefore
  have entryTest : ∃ left right, entry₀.query = .inr (.test state.first left right) ∧
      PqxdhDeploymentSecrecy.Admissible left right := by
    rcases entry₀ with ⟨query, reply⟩
    rcases query with (coin | command) | (⟨handle, left, right⟩ | ⟨handle, length⟩)
    · cases admissible₀
    · cases admissible₀
    · simp only [admissibleTest] at admissible₀
      split at admissible₀
      · rename_i good
        simp only [Option.some.injEq] at admissible₀
        exact ⟨left, right, by rw [admissible₀], good⟩
      · cases admissible₀
    · cases admissible₀
  obtain ⟨left₀, right₀, query₀, good₀⟩ := entryTest
  have admitted₀ : AdmittedTest setup.source.crypto codec setup.serverKeyId pre state.first left₀ right₀ :=
    ⟨good₀, fun first found => by rw [firstNone] at found; cases found⟩
  obtain ⟨g, gFound⟩ := designatedOf _ (symbolic pre entry₀ post state.first left₀ right₀ split₀ query₀ admitted₀)
  simp only [happens, observed, Option.any_some, PqxdhDeploymentHeadlineEvents.lorEligEvent, decide_eq_true_eq]
  refine ⟨g, tested, (nbfFilter_iff _).mpr clean, ⟨state.first, firstFound, gFound⟩, ?_⟩
  intro before entry after handle left right split query admits
  obtain ⟨gh, ghFound⟩ := designatedOf _ (symbolic before entry after handle left right split query admits)
  rw [ghFound]
  cases firstBefore : firstTest before with
  | none =>
      have firstIs : firstTest final.1.transcript = some handle := by
        rw [split, firstTest, List.findSome?_append, List.findSome?_cons]
        rw [firstTest] at firstBefore
        rw [firstBefore]
        simp [admissibleTest, query, admits.1]
      rw [firstFound, Option.some.injEq] at firstIs
      rw [← firstIs] at ghFound
      rw [gFound] at ghFound
      exact ghFound.symm
  | some first =>
      have firstStable : firstTest final.1.transcript = some first := by
        rw [split, firstTest]
        exact findSome_prefix _ before _ first firstBefore
      rw [firstFound, Option.some.injEq] at firstStable
      rcases admits.2 first firstBefore with same | ⟨target, firstAt, handleAt⟩
      · rw [same, ← firstStable] at ghFound
        rw [gFound] at ghFound
        exact ghFound.symm
      · have early₀ : designate setup.source.crypto codec setup.serverKeyId before state.first = some target := by
          rw [firstStable]
          exact firstAt
        have late₀ := stays before (entry :: after) split _ target _ early₀
          (PqxdhDeploymentKemTransfer.designateIn_some _ codec _ budget _ _ g gFound)
        have lateH := stays before (entry :: after) split _ target _ handleAt
          (PqxdhDeploymentKemTransfer.designateIn_some _ codec _ budget _ _ gh ghFound)
        rw [← lateH] at late₀
        simp only [Prod.mk.injEq] at late₀
        congr 1
        exact Prod.ext (Fin.ext late₀.1.symm) (Fin.ext late₀.2.symm)

/-- The Server-side difference (design-v2 section 7.5 restricted to Server-peer tests) on every outcome of the experiment: the Server-side symbolic eligibility without the Server-side CE-LOR eligibility (NoBundleFailure filter) is a Server-side gap (some admitted peer undesignated) or an identity collision (`IdentityCollision`: a peer's designated owner moved after an admission, `peer_moves`, `field_collision`). Neither the Beacon-side gap nor a ciphertext collision arises, because every admitted test handle is a Server peer. -/
theorem lor_difference_peer (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (holds : LorEligPeerSym setup codec outcome) :
    happens (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget
        nbfFilter) outcome = true ∨
      ServerGap setup codec budget outcome ∨ IdentityCollision setup outcome := by
  classical
  obtain ⟨⟨created, output, final, found, tested, clean, symbolic⟩, created', output', final', found', peers⟩ := holds
  rw [found, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found'
  obtain ⟨rfl, rfl, rfl⟩ := found'
  have observed : observeGame outcome.1 = some (output, final.1, final.2.produced) := by
    rw [found]
    rfl
  by_cases gap : ServerGap setup codec budget outcome
  · exact Or.inr (Or.inl gap)
  by_cases collision : IdentityCollision setup outcome
  · exact Or.inr (Or.inr collision)
  left
  have designatedOf : ∀ before entry after handle left right, final.1.transcript = before ++ entry :: after →
      entry.query = .inr (.test handle left right) →
      AdmittedTest setup.source.crypto codec setup.serverKeyId before handle left right →
      (∃ keyId, handle = .peer keyId) ∧
        ∃ g, designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript handle = some g := by
    intro before entry after handle left right split query admits
    obtain ⟨keyId, rfl⟩ := peers before entry after handle left right split query admits
    refine ⟨⟨keyId, rfl⟩, ?_⟩
    cases designatedFound : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript
        (.peer keyId) with
    | none =>
        exact absurd ⟨created, output, final, found, keyId,
          symbolic before entry after (.peer keyId) left right split query admits, designatedFound⟩ gap
    | some g => exact ⟨g, rfl⟩
  have stays : ∀ (before rest : List Entry), final.1.transcript = before ++ rest → ∀ handle early late,
      (∃ keyId, handle = .peer keyId) →
      designate setup.source.crypto codec setup.serverKeyId before handle = some early →
      designate setup.source.crypto codec setup.serverKeyId final.1.transcript handle = some late → late = early := by
    intro before rest split handle early late isPeer earlyFound lateFound
    obtain ⟨keyId, rfl⟩ := isPeer
    rw [split] at lateFound
    obtain ⟨sessionEq, same | field⟩ := peer_moves setup.source.crypto codec setup.serverKeyId before rest keyId
      early.1 late.1 early.2 late.2 earlyFound lateFound
    · exact Prod.ext sessionEq same
    · rw [← split] at field
      exact absurd (field_collision setup codec checks route ensureInit phase1 bounds mode adversary runtime outcome
        member created output final found _ _ field) collision
  have inv := ledgerInv_game setup codec checks route ensureInit 0 bounds mode adversary runtime outcome member created
    output final found
  obtain ⟨state, stateFound⟩ := Option.isSome_iff_exists.mp tested
  have firstFound : firstTest final.1.transcript = some state.first := by
    unfold PqxdhRecordLiftFlat.LedgerInv at inv
    rw [← inv, stateFound]
    rfl
  obtain ⟨pre, entry₀, post, split₀, admissible₀, noneBefore⟩ := List.findSome?_eq_some_iff.mp firstFound
  have firstNone : firstTest pre = none := List.findSome?_eq_none_iff.mpr noneBefore
  have entryTest : ∃ left right, entry₀.query = .inr (.test state.first left right) ∧
      PqxdhDeploymentSecrecy.Admissible left right := by
    rcases entry₀ with ⟨query, reply⟩
    rcases query with (coin | command) | (⟨handle, left, right⟩ | ⟨handle, length⟩)
    · cases admissible₀
    · cases admissible₀
    · simp only [admissibleTest] at admissible₀
      split at admissible₀
      · rename_i good
        simp only [Option.some.injEq] at admissible₀
        exact ⟨left, right, by rw [admissible₀], good⟩
      · cases admissible₀
    · cases admissible₀
  obtain ⟨left₀, right₀, query₀, good₀⟩ := entryTest
  have admitted₀ : AdmittedTest setup.source.crypto codec setup.serverKeyId pre state.first left₀ right₀ :=
    ⟨good₀, fun first found => by rw [firstNone] at found; cases found⟩
  obtain ⟨isPeer₀, g, gFound⟩ := designatedOf pre entry₀ post state.first left₀ right₀ split₀ query₀ admitted₀
  simp only [happens, observed, Option.any_some, PqxdhDeploymentHeadlineEvents.lorEligPeerEvent, decide_eq_true_eq]
  refine ⟨⟨g, tested, (nbfFilter_iff _).mpr clean, ⟨state.first, firstFound, gFound⟩, ?_⟩, peers⟩
  intro before entry after handle left right split query admits
  obtain ⟨isPeerH, gh, ghFound⟩ := designatedOf before entry after handle left right split query admits
  rw [ghFound]
  cases firstBefore : firstTest before with
  | none =>
      have firstIs : firstTest final.1.transcript = some handle := by
        rw [split, firstTest, List.findSome?_append, List.findSome?_cons]
        rw [firstTest] at firstBefore
        rw [firstBefore]
        simp [admissibleTest, query, admits.1]
      rw [firstFound, Option.some.injEq] at firstIs
      rw [← firstIs] at ghFound
      rw [gFound] at ghFound
      exact ghFound.symm
  | some first =>
      have firstStable : firstTest final.1.transcript = some first := by
        rw [split, firstTest]
        exact findSome_prefix _ before _ first firstBefore
      rw [firstFound, Option.some.injEq] at firstStable
      rcases admits.2 first firstBefore with same | ⟨target, firstAt, handleAt⟩
      · rw [same, ← firstStable] at ghFound
        rw [gFound] at ghFound
        exact ghFound.symm
      · have early₀ : designate setup.source.crypto codec setup.serverKeyId before state.first = some target := by
          rw [firstStable]
          exact firstAt
        have late₀ := stays before (entry :: after) split _ target _ isPeer₀ early₀
          (PqxdhDeploymentKemTransfer.designateIn_some _ codec _ budget _ _ g gFound)
        have lateH := stays before (entry :: after) split _ target _ isPeerH handleAt
          (PqxdhDeploymentKemTransfer.designateIn_some _ codec _ budget _ _ gh ghFound)
        rw [← lateH] at late₀
        simp only [Prod.mk.injEq] at late₀
        congr 1
        exact Prod.ext (Fin.ext late₀.1.symm) (Fin.ext late₀.2.symm)

end Containments

/-! ### `symbolic_lor` -/

section Bound
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)

/-- The real-number core of `symbolic_lor`: for nested events with `0 ≤ dW ≤ d`, the two advantages differ by `dW − d/2`, at most `d/2` in absolute value. -/
theorem nested_arith (wS eS wC eC dW d : ℝ) (splitW : wS = wC + dW) (splitE : eS = eC + d) (nonneg : 0 ≤ dW)
    (below : dW ≤ d) : |(wS - (1 / 2) * eS) - (wC - (1 / 2) * eC)| ≤ (1 / 2) * d := by
  rw [splitW, splitE, abs_le]
  constructor <;> linarith

/-- Equal probabilities for Boolean events that agree on the support. -/
theorem chance_eq_support {α : Type} (run : ProbComp α) (first second : α → Bool)
    (same : ∀ a ∈ support run, first a = true ↔ second a = true) :
    𝒟[first <$> run] {true} = 𝒟[second <$> run] {true} :=
  le_antisymm (chance_le_support run first second fun a member => (same a member).mp)
    (chance_le_support run second first fun a member => (same a member).mpr)

/-- `symbolic_lor` in event form (design-v2 section 7.5): the symbolic LOR advantage (eligibility `e_sym`: a test session, no rejected bundle call in Fresh, every admitted test handle symbolically eligible) and CE-LOR's advantage with the NoBundleFailure filter differ by at most half the probability of the difference event `e_sym ∧ ¬e_CE`, because `e_CE ⊆ e_sym` on the support (`lor_inclusion`) and the nested-set advantages differ by `Pr[W ∧ D] − ½Pr[D]`. Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem symbolic_lor_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (budget : Budget) (runtime : A) (guess : X → Bool) :
    ENNReal.ofReal |((𝒟[lorWinSym setup codec guess <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[lorEligSym setup codec <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal) -
      ((𝒟[(fun outcome => happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter)
          outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget
          nbfFilter) outcome) <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal)| ≤
      2⁻¹ * 𝒟[(fun outcome => lorEligSym setup codec outcome &&
          !happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} := by
  classical
  set run := (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime
  set eCE := fun outcome => happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome
  set wCE := fun outcome => happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter)
    outcome
  have unpackElig : ∀ outcome, eCE outcome = true → ∃ created output final, outcome.1 = some (created, output, final) ∧
      ∃ g, LorElig setup.source.crypto codec setup.serverKeyId budget nbfFilter g (output, final.1, final.2.produced) := by
    intro outcome held
    simp only [eCE, happens] at held
    rcases found : outcome.1 with _ | ⟨created, output, final⟩
    · simp [observeGame, found] at held
    · simp only [observeGame, found, Option.map_some, Option.any_some, lorEligEvent, decide_eq_true_eq] at held
      exact ⟨created, output, final, rfl, held⟩
  have splitW := PqxdhDeploymentHeadlineLor.chance_split run (lorWinSym setup codec guess) (fun outcome => eCE outcome = true)
  have splitE := PqxdhDeploymentHeadlineLor.chance_split run (lorEligSym setup codec) (fun outcome => eCE outcome = true)
  have winSame : 𝒟[(fun outcome => decide (lorWinSym setup codec guess outcome = true ∧ eCE outcome = true)) <$> run]
      {true} = 𝒟[wCE <$> run] {true} := by
    refine chance_eq_support run _ _ fun outcome member => ?_
    simp only [decide_eq_true_eq, lorWinSym, wCE, eCE]
    constructor
    · rintro ⟨⟨_, created, output, final, found, bit⟩, elig⟩
      obtain ⟨created', output', final', found', g, eligible⟩ := unpackElig outcome elig
      rw [found] at found'
      simp only [Option.some.injEq, Prod.mk.injEq] at found'
      obtain ⟨rfl, rfl, rfl⟩ := found'
      simp only [happens, observeGame, found, Option.map_some, Option.any_some, lorWinEvent, decide_eq_true_eq]
      exact ⟨g, eligible, bit⟩
    · intro won
      simp only [happens] at won
      rcases found : outcome.1 with _ | ⟨created, output, final⟩
      · simp [observeGame, found] at won
      · simp only [observeGame, found, Option.map_some, Option.any_some, lorWinEvent, decide_eq_true_eq] at won
        obtain ⟨g, eligible, bit⟩ := won
        refine ⟨⟨lor_inclusion setup codec checks route ensureInit phase1 phase2 bounds .P adversary budget runtime
          outcome member created output final found g eligible, created, output, final, found, bit⟩, ?_⟩
        simp only [happens, observeGame, found, Option.map_some, Option.any_some, lorEligEvent, decide_eq_true_eq]
        exact ⟨g, eligible⟩
  have eligSame : 𝒟[(fun outcome => decide (lorEligSym setup codec outcome = true ∧ eCE outcome = true)) <$> run]
      {true} = 𝒟[eCE <$> run] {true} := by
    refine chance_eq_support run _ _ fun outcome member => ?_
    simp only [decide_eq_true_eq]
    constructor
    · exact fun held => held.2
    · intro elig
      refine ⟨?_, elig⟩
      obtain ⟨created, output, final, found, g, eligible⟩ := unpackElig outcome elig
      simp only [lorEligSym, decide_eq_true_eq]
      exact lor_inclusion setup codec checks route ensureInit phase1 phase2 bounds .P adversary budget runtime outcome
        member created output final found g eligible
  have dBelow : 𝒟[(fun outcome => decide (lorWinSym setup codec guess outcome = true ∧ ¬eCE outcome = true)) <$> run]
      {true} ≤ 𝒟[(fun outcome => decide (lorEligSym setup codec outcome = true ∧ ¬eCE outcome = true)) <$> run]
        {true} := by
    refine chance_le_support run _ _ fun outcome _ held => ?_
    simp only [decide_eq_true_eq, lorWinSym, lorEligSym] at held ⊢
    exact ⟨held.1.1, held.2⟩
  have dSame : 𝒟[(fun outcome => decide (lorEligSym setup codec outcome = true ∧ ¬eCE outcome = true)) <$> run]
      {true} = 𝒟[(fun outcome => lorEligSym setup codec outcome && !eCE outcome) <$> run] {true} := by
    refine chance_eq_support run _ _ fun outcome _ => ?_
    simp
  have finite : ∀ f : _ → Bool, 𝒟[f <$> run] {true} ≠ ⊤ := fun f => UniformTargetSelection.chance_ne_top run f
  rw [winSame] at splitW
  rw [eligSame] at splitE
  have core := nested_arith _ _ _ _ _ _
    (congrArg ENNReal.toReal splitW |>.trans (ENNReal.toReal_add (finite _) (finite _)))
    (congrArg ENNReal.toReal splitE |>.trans (ENNReal.toReal_add (finite _) (finite _)))
    ENNReal.toReal_nonneg (ENNReal.toReal_mono (finite _) dBelow)
  refine (ENNReal.ofReal_le_ofReal core).trans ?_
  rw [PqxdhDeploymentHeadlineLor.ofReal_half, ENNReal.ofReal_toReal (finite _), dSame]

/-- The difference event of `symbolic_lor` is bounded by `ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ctCollTerm` (`lor_difference`, `sym_gap`, `identity_collision_game`). -/
theorem lor_difference_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => lorEligSym setup codec outcome &&
          !happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
        ordinaryFallback +
      ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback) +
      ctGapTerm setup codec checks route ensureInit bounds .P adversary runtime +
      injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P adversary runtime := by
  classical
  refine (chance_le_add_support _ _
    (fun outcome => serverGap setup codec budget outcome || beaconGap setup codec budget outcome)
    (fun outcome => @decide (IdentityCollision setup outcome) (Classical.propDecidable _) ||
      happens (PqxdhDeploymentHeadlineCollision.ctCollEvent setup.source.crypto codec) outcome)
    fun outcome member held => ?_).trans ?_
  · simp only [Bool.and_eq_true, Bool.not_eq_true', lorEligSym, decide_eq_true_eq] at held
    rcases lor_difference setup codec checks route ensureInit phase1 bounds .P adversary budget runtime outcome member
      held.1 with elig | gap | gap | collision | coll
    · rw [elig] at held
      cases held.2
    · left
      simp [serverGap, gap]
    · left
      simp [beaconGap, gap]
    · right
      simp [collision]
    · right
      simp [coll]
  · have rest : 𝒟[(fun outcome => @decide (IdentityCollision setup outcome) (Classical.propDecidable _) ||
          happens (PqxdhDeploymentHeadlineCollision.ctCollEvent setup.source.crypto codec) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P adversary runtime := by
      refine (chance_le_add_support _ _ (fun outcome => @decide (IdentityCollision setup outcome)
        (Classical.propDecidable _)) (fun outcome => happens (PqxdhDeploymentHeadlineCollision.ctCollEvent
          setup.source.crypto codec) outcome) fun outcome _ held => by simpa using held).trans ?_
      exact add_le_add (PqxdhDeploymentHeadlineCollision.identity_collision_game setup codec checks route ensureInit
        phase1 phase2 bounds .P adversary budget respects runtime) le_rfl
    refine (add_le_add (PqxdhDeploymentHeadlineGap.sym_gap setup codec checks caps bounded shortRejects route ensureInit
      phase1 phase2 frameBack writable law spread correct adapter bounds .P adversary budget respects runtime
      identityFallback ordinaryFallback a1Fallback signatureFallback) rest).trans (le_of_eq ?_)
    ring

/-- The triangle inequality for `ENNReal.ofReal` of absolute values: a bound on `|a − b|` and one on `|b|` bound `|a|`. -/
theorem ofReal_abs_triangle (a b : ℝ) (first second : ℝ≥0∞) (close : ENNReal.ofReal |a - b| ≤ first)
    (base : ENNReal.ofReal |b| ≤ second) : ENNReal.ofReal |a| ≤ second + first := by
  have split : |a| ≤ |b| + |a - b| := by
    have := abs_sub_abs_le_abs_sub a b
    linarith
  exact (ENNReal.ofReal_le_ofReal split).trans (ENNReal.ofReal_add_le.trans (add_le_add base close))

/-- `symbolic_lor` (design-v2 section 7.5; VC rows SSX-b2s, SS-b2s, 167/173 on symbolic eligibility, with any admitted test handles; the Server-side rows SSX-s2b, SS-s2b, whose tests are on Server peers, use `symbolic_lor_server` with `½(ε_A2pub + ε_inj)`; mode P): the symbolic LOR advantage (eligibility `e_sym`: a test session, no rejected bundle call in Fresh, every admitted test handle symbolically eligible, `SymServer` or `SymBeacon`) differs from CE-LOR's advantage with the public NoBundleFailure filter (`nbfFilter`) by at most `½(ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ctCollTerm)`. `ctGapTerm` is F-ct2's explicit term (D-ct deferred) and `ctCollTerm` the explicit ciphertext-collision term (design-v2 section 7.4's `ε_ctcoll` needs the unproved game-level `ct_collision_game`). Premises: the approved Phase 1, Phase 2 and frame read-back contracts, `KemBound`, `shortRejects`, and CE-A1's (`ReadWritable`, `X25519ClassLaw`, `X25519ScalarSpread`, `SourceFullCorrect`, `HasAttachedVerificationAdapter`), and the budget. -/
theorem symbolic_lor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (guess : X → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[lorWinSym setup codec guess <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[lorEligSym setup codec <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal) -
      ((𝒟[(fun outcome => happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter)
          outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget
          nbfFilter) outcome) <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P adversary runtime +
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P adversary runtime) :=
  (symbolic_lor_le setup codec checks route ensureInit phase1 phase2 bounds adversary budget runtime guess).trans
    (mul_le_mul_right (lor_difference_bound setup codec checks caps bounded shortRejects route ensureInit phase1
      phase2 frameBack writable law spread correct adapter bounds adversary budget respects runtime identityFallback
      ordinaryFallback a1Fallback signatureFallback) _)

/-- `symbolic_lor` with CE-LOR's bound (`PqxdhDeploymentHeadlineLor.ce_lor` at the NoBundleFailure filter): the symbolic LOR advantage is at most CE-LOR's bound plus `½(ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ctCollTerm)`. Premises: those of `ce_lor` and of `symbolic_lor`. -/
theorem symbolic_lor_bound (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[lorWinSym setup codec guess <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[lorEligSym setup codec <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
              caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P adversary runtime +
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P adversary runtime) := by
  have ce := PqxdhDeploymentHeadlineLor.ce_lor setup functional codec checks route ensureInit phase1 phase2 correct caps
    bounded qInit initBound bounds adversary budget respects runtime fallback guess nbfFilter
  have sym := symbolic_lor setup codec checks caps bounded shortRejects route ensureInit phase1 phase2 frameBack writable
    law spread correct adapter bounds adversary budget respects runtime guess identityFallback ordinaryFallback a1Fallback
    signatureFallback
  exact ofReal_abs_triangle _ _ _ _ sym ce

/-- `symbolic_lor_server` in event form: the Server-side symbolic LOR advantage (eligibility `LorEligPeerSym`: `e_sym` with every admitted test handle a Server peer) and the Server-side CE-LOR advantage with the NoBundleFailure filter (`lorEligPeerEvent`, `lorWinPeerEvent`) differ by at most half the probability of the Server-side difference event, because the Server-side CE eligibility is contained in the Server-side symbolic eligibility on the support (`lor_inclusion` with the same `PeerTests`). Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem symbolic_lor_server_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (budget : Budget) (runtime : A) (guess : X → Bool) :
    ENNReal.ofReal |((𝒟[lorWinPeerSym setup codec guess <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[lorEligPeerSym setup codec <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal) -
      ((𝒟[(fun outcome => happens (PqxdhDeploymentHeadlineEvents.lorWinPeerEvent setup.source.crypto codec
          setup.serverKeyId budget guess nbfFilter) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto
          codec setup.serverKeyId budget nbfFilter) outcome) <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal)| ≤
      2⁻¹ * 𝒟[(fun outcome => lorEligPeerSym setup codec outcome &&
          !happens (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget
            nbfFilter) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} := by
  classical
  set run := (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime
  set eCE := fun outcome => happens (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto codec
    setup.serverKeyId budget nbfFilter) outcome
  set wCE := fun outcome => happens (PqxdhDeploymentHeadlineEvents.lorWinPeerEvent setup.source.crypto codec
    setup.serverKeyId budget guess nbfFilter) outcome
  have unpackElig : ∀ outcome, eCE outcome = true → ∃ created output final, outcome.1 = some (created, output, final) ∧
      (∃ g, LorElig setup.source.crypto codec setup.serverKeyId budget nbfFilter g (output, final.1, final.2.produced)) ∧
      PqxdhDeploymentHeadlineEvents.PeerTests setup.source.crypto codec setup.serverKeyId
        (output, final.1, final.2.produced) := by
    intro outcome held
    simp only [eCE, happens] at held
    rcases found : outcome.1 with _ | ⟨created, output, final⟩
    · simp [observeGame, found] at held
    · simp only [observeGame, found, Option.map_some, Option.any_some,
        PqxdhDeploymentHeadlineEvents.lorEligPeerEvent, decide_eq_true_eq] at held
      exact ⟨created, output, final, rfl, held⟩
  have symOf : ∀ outcome ∈ support run, ∀ created output final, outcome.1 = some (created, output, final) →
      (∃ g, LorElig setup.source.crypto codec setup.serverKeyId budget nbfFilter g (output, final.1, final.2.produced)) →
      PqxdhDeploymentHeadlineEvents.PeerTests setup.source.crypto codec setup.serverKeyId
        (output, final.1, final.2.produced) →
      LorEligPeerSym setup codec outcome := by
    intro outcome member created output final found ⟨g, eligible⟩ peers
    exact ⟨lor_inclusion setup codec checks route ensureInit phase1 phase2 bounds .P adversary budget runtime outcome
      member created output final found g eligible, created, output, final, found, peers⟩
  have splitW := PqxdhDeploymentHeadlineLor.chance_split run (lorWinPeerSym setup codec guess)
    (fun outcome => eCE outcome = true)
  have splitE := PqxdhDeploymentHeadlineLor.chance_split run (lorEligPeerSym setup codec)
    (fun outcome => eCE outcome = true)
  have winSame : 𝒟[(fun outcome => decide (lorWinPeerSym setup codec guess outcome = true ∧ eCE outcome = true)) <$>
      run] {true} = 𝒟[wCE <$> run] {true} := by
    refine chance_eq_support run _ _ fun outcome member => ?_
    simp only [decide_eq_true_eq, lorWinPeerSym, wCE]
    constructor
    · rintro ⟨⟨_, created, output, final, found, bit⟩, elig⟩
      obtain ⟨created', output', final', found', ⟨g, eligible⟩, peers⟩ := unpackElig outcome elig
      rw [found] at found'
      simp only [Option.some.injEq, Prod.mk.injEq] at found'
      obtain ⟨rfl, rfl, rfl⟩ := found'
      simp only [happens, observeGame, found, Option.map_some, Option.any_some,
        PqxdhDeploymentHeadlineEvents.lorWinPeerEvent, decide_eq_true_eq]
      exact ⟨⟨g, eligible, bit⟩, peers⟩
    · intro won
      simp only [happens] at won
      rcases found : outcome.1 with _ | ⟨created, output, final⟩
      · simp [observeGame, found] at won
      · simp only [observeGame, found, Option.map_some, Option.any_some,
          PqxdhDeploymentHeadlineEvents.lorWinPeerEvent, decide_eq_true_eq] at won
        obtain ⟨⟨g, eligible, bit⟩, peers⟩ := won
        refine ⟨⟨symOf outcome member created output final found ⟨g, eligible⟩ peers, created, output, final, found,
          bit⟩, ?_⟩
        simp only [eCE, happens, observeGame, found, Option.map_some, Option.any_some,
          PqxdhDeploymentHeadlineEvents.lorEligPeerEvent, decide_eq_true_eq]
        exact ⟨⟨g, eligible⟩, peers⟩
  have eligSame : 𝒟[(fun outcome => decide (lorEligPeerSym setup codec outcome = true ∧ eCE outcome = true)) <$> run]
      {true} = 𝒟[eCE <$> run] {true} := by
    refine chance_eq_support run _ _ fun outcome member => ?_
    simp only [decide_eq_true_eq]
    constructor
    · exact fun held => held.2
    · intro elig
      refine ⟨?_, elig⟩
      obtain ⟨created, output, final, found, eligible, peers⟩ := unpackElig outcome elig
      simp only [lorEligPeerSym, decide_eq_true_eq]
      exact symOf outcome member created output final found eligible peers
  have dBelow : 𝒟[(fun outcome => decide (lorWinPeerSym setup codec guess outcome = true ∧ ¬eCE outcome = true)) <$>
      run] {true} ≤ 𝒟[(fun outcome => decide (lorEligPeerSym setup codec outcome = true ∧ ¬eCE outcome = true)) <$>
        run] {true} := by
    refine chance_le_support run _ _ fun outcome _ held => ?_
    simp only [decide_eq_true_eq, lorWinPeerSym, lorEligPeerSym] at held ⊢
    exact ⟨held.1.1, held.2⟩
  have dSame : 𝒟[(fun outcome => decide (lorEligPeerSym setup codec outcome = true ∧ ¬eCE outcome = true)) <$> run]
      {true} = 𝒟[(fun outcome => lorEligPeerSym setup codec outcome && !eCE outcome) <$> run] {true} := by
    refine chance_eq_support run _ _ fun outcome _ => ?_
    simp
  have finite : ∀ f : _ → Bool, 𝒟[f <$> run] {true} ≠ ⊤ := fun f => UniformTargetSelection.chance_ne_top run f
  rw [winSame] at splitW
  rw [eligSame] at splitE
  have core := nested_arith _ _ _ _ _ _
    (congrArg ENNReal.toReal splitW |>.trans (ENNReal.toReal_add (finite _) (finite _)))
    (congrArg ENNReal.toReal splitE |>.trans (ENNReal.toReal_add (finite _) (finite _)))
    ENNReal.toReal_nonneg (ENNReal.toReal_mono (finite _) dBelow)
  refine (ENNReal.ofReal_le_ofReal core).trans ?_
  rw [PqxdhDeploymentHeadlineLor.ofReal_half, ENNReal.ofReal_toReal (finite _), dSame]

/-- The Server-side difference event of `symbolic_lor_server` is bounded by `ε_A2pub + ε_inj` (`lor_difference_peer`, `server_gap_bound`, `identity_collision_game`); no `ε_A1`, `ctGapTerm` or `ctCollTerm`. -/
theorem lor_difference_server_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => lorEligPeerSym setup codec outcome &&
          !happens (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget
            nbfFilter) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
        ordinaryFallback +
      injTerm setup budget := by
  classical
  refine (chance_le_add_support _ _ (serverGap setup codec budget)
    (fun outcome => @decide (IdentityCollision setup outcome) (Classical.propDecidable _))
    fun outcome member held => ?_).trans ?_
  · simp only [Bool.and_eq_true, Bool.not_eq_true', lorEligPeerSym, decide_eq_true_eq] at held
    rcases lor_difference_peer setup codec checks route ensureInit phase1 bounds .P adversary budget runtime outcome
      member held.1 with elig | gap | collision
    · rw [elig] at held
      cases held.2
    · left
      simp [serverGap, gap]
    · right
      simp [collision]
  · exact add_le_add (PqxdhDeploymentHeadlineGap.server_gap_bound setup codec checks shortRejects route ensureInit
      phase1 phase2 bounds .P adversary budget respects runtime identityFallback ordinaryFallback)
      (PqxdhDeploymentHeadlineCollision.identity_collision_game setup codec checks route ensureInit phase1 phase2 bounds
        .P adversary budget respects runtime)

/-- `symbolic_lor_server` (design-v2 section 7.5 restricted to Server-peer tests; VC rows SSX-s2b, SS-s2b on Server-side symbolic eligibility, mode P): the Server-side symbolic LOR advantage (eligibility `LorEligPeerSym`: a test session, no rejected bundle call in Fresh, every admitted test handle a Server peer with `SymServer`) differs from the Server-side CE-LOR advantage with the public NoBundleFailure filter (`ce_lor_server`'s events at `nbfFilter`) by at most `½(ε_A2pub + ε_inj)`; no `ε_A1`, `ctGapTerm` or `ctCollTerm`. Premises: the approved Phase 1 and Phase 2 read-back contracts, `shortRejects` and the budget. -/
theorem symbolic_lor_server (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (guess : X → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[lorWinPeerSym setup codec guess <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[lorEligPeerSym setup codec <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal) -
      ((𝒟[(fun outcome => happens (PqxdhDeploymentHeadlineEvents.lorWinPeerEvent setup.source.crypto codec
          setup.serverKeyId budget guess nbfFilter) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto
          codec setup.serverKeyId budget nbfFilter) outcome) <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        injTerm setup budget) :=
  (symbolic_lor_server_le setup codec checks route ensureInit phase1 phase2 bounds adversary budget runtime guess).trans
    (mul_le_mul_right (lor_difference_server_bound setup codec checks shortRejects route ensureInit phase1 phase2 bounds
      adversary budget respects runtime identityFallback ordinaryFallback) _)

/-- `symbolic_lor_server` with CE-LOR's Server-side bound (`PqxdhDeploymentHeadlineLor.ce_lor_server` at the NoBundleFailure filter, no `β_g`): the Server-side symbolic LOR advantage is at most `ce_lor_server`'s bound plus `½(ε_A2pub + ε_inj)`. Premises: those of `ce_lor_server` and of `symbolic_lor_server`. -/
theorem symbolic_lor_server_bound (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[lorWinPeerSym setup codec guess <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[lorEligPeerSym setup codec <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (PqxdhDeploymentHeadlineEvents.lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess
              nbfFilter) lorClaim (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (PqxdhDeploymentHeadlineEvents.lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess
              nbfFilter) lorClaim (g.1, g.2.castSucc) runtime) +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (serverSlotted setup codec budget
              (PqxdhDeploymentHeadlineEvents.lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess
                nbfFilter) lorClaim (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
              (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget
                nbfFilter) lorClaim (g.1, g.2.castSucc) runtime) +
            ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
              (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget
                nbfFilter) lorClaim (g.1, g.2.castSucc) runtime) +
            recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
              caps qInit (serverSlotted setup codec budget
                (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget
                  nbfFilter) lorClaim (g.1, g.2.castSucc))))) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        injTerm setup budget) := by
  have ce := PqxdhDeploymentHeadlineLor.ce_lor_server setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds adversary budget respects runtime fallback guess nbfFilter
  have sym := symbolic_lor_server setup codec checks shortRejects route ensureInit phase1 phase2 bounds adversary budget
    respects runtime guess identityFallback ordinaryFallback
  exact ofReal_abs_triangle _ _ _ _ sym ce

end Bound

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.findSome_prefix' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.findSome_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.owners_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.owners_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.acceptCount_prefix' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.acceptCount_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.publishes_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.publishes_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.linked_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.linked_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.linked_carries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.linked_carries

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.owner_moves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.owner_moves

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.peer_moves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.peer_moves

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.moves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.moves

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.nbfFilter_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.nbfFilter_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.ledgerInv_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.ledgerInv_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.encodedIdentity_injective' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.encodedIdentity_injective

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.bundle_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.bundle_identity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.field_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.field_collision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.designated_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.designated_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.lor_inclusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.lor_inclusion

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.lor_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.lor_difference

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.lor_difference_peer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.lor_difference_peer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.nested_arith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.nested_arith

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.chance_eq_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.chance_eq_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.lor_difference_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.lor_difference_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.ofReal_abs_triangle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.ofReal_abs_triangle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_server_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_server_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.lor_difference_server_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.lor_difference_server_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_server_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_server_bound
