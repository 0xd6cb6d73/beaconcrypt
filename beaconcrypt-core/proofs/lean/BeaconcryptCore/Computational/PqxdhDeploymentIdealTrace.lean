-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealFrame
import BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch
import BeaconcryptCore.Computational.PqxdhRecordLiftOrigins

/-!
# Public transcript functions and key facts for the provenance of the ideal environment (CE-11b, unit U4)

The definitions of design-v2 section 7.1 and the key facts of U6's trace invariant carried to the record world:

- Public functions of the transcript: `acceptReplies`, `sessionAt` (the session returned by the raw accept attempt of an ordinal), `peerOf` (the key ID built by the target's session), `FinishBefore` (owner `k` finished before the selected raw accept), `BeaconLinked` (owner `k` designates the target), `Anomaly` (both), `IdealSlots` (C5 restated: restriction and converse for a handle-to-slot map), with their transcript lemmas (`sessionAt_other`, `sessionAt_before`, `sessionAt_accept`, `acceptCount_other`, `acceptCount_accept`, `buildOf_other`, `buildOf_build`, `buildOf_some`).
- `KeyFacts`, the two transcript conjuncts of `PqxdhDeploymentIdealKeymatch.KeyTrace`; `split_keyFacts` on every outcome of the final split game (U6's `game_trace` along `ideal_to_split`), `world_keyFacts` on every outcome of the record world with `envGD` (along `c1_split`), and `keyFacts_marked`, the key match of `ideal_keymatch` from the key facts alone.
- The slot maps `originSlots` (of a provenance annotation) and `ghostOrigins` (of the ideal environment's install ghosts).
- The KEM ciphertext guess quantities `ctGuess` (design-v2 section 7.1) and `ctGuessPk` (its restriction to guesses of the public key alone), with `ctGuessPk_le`. They are definitions, not assumptions. Both are suprema over all guess functions, including inefficient ones, so they are information-theoretic quantities of the scheme; the guesser-parametrized form that CE-12a's IND-CCA reduction consumes (plan section 49, Q2) is `PqxdhDeploymentIdealAnomaly.ctGuessBy`.

These are definitions and support facts; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry Handle)
open PqxdhDeploymentTranscript (designate buildOf acceptCount)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (IdealCore)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhRegistrationJointKemSecondEntry (Alloc)
open PqxdhRecordLiftInterface (Slot)
open PqxdhLiveKemReservation (Pair)

variable {KemSK Reader Response : Type}

/-! ### Public functions of the transcript (design-v2 section 7.1) -/

section Transcript

/-- The replies of the raw accept attempts of a transcript, oldest first. -/
def acceptReplies (transcript : List Entry) : List (Option ℕ) :=
  transcript.filterMap fun entry => match entry with
    | ⟨.inl (.inr (.accept _)), reply⟩ => some reply
    | _ => none

/-- The session returned by the raw accept attempt of ordinal `i` (counted from zero), if that attempt exists and returned one. -/
def sessionAt (transcript : List Entry) (i : ℕ) : Option ℕ := ((acceptReplies transcript)[i]?).bind id

/-- The key ID of the Server peer of the target's session: the key ID of the first successful build of the session that the selected raw accept returned. -/
def peerOf {count : ℕ} (t : Target count) (transcript : List Entry) : Option Std.U64 :=
  (sessionAt transcript t.accept).bind fun s => (buildOf transcript s).map (·.keyId)

/-- A successful finish of owner `k` (the target's KEM creation index) made before the selected raw accept: fewer than `t.accept + 1` accept attempts precede it. -/
def FinishBefore {count : ℕ} (t : Target count) (transcript : List Entry) : Prop :=
  ∃ (before : List Entry) (raw reply : Pqxdh.Bytes) (after : List Entry),
    transcript = before ++ (⟨.inl (.inr (.finish t.kem.val raw)), some reply⟩ : Entry) :: after ∧
      acceptCount before ≤ t.accept

/-- Owner `k` designates the target: the public designation of owner `k`'s handle is `(t.accept, k)`. -/
def BeaconLinked {count : ℕ} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (t : Target count) (transcript : List Entry) : Prop :=
  designate crypto codec serverKid transcript (.owner t.kem.val) = some (t.accept, t.kem.val)

/-- The Beacon-side anomaly of a target (design-v2 sections 7.1 and 7.3): owner `k` designates the target through a finish made before the selected raw accept. It is a public event (a function of the transcript). -/
def Anomaly {count : ℕ} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (t : Target count) (transcript : List Entry) : Prop :=
  BeaconLinked crypto codec serverKid t transcript ∧ FinishBefore t transcript

/-- C5 restated (design-v2 section 7.1, `IdealSlots`) for a handle-to-slot map: restriction (a Server peer holding a slot holds slot 0 and is the target's peer; an owner holding a slot is owner `k`) and converse (a Server peer designating the target holds slot 0; when owner `k` designates the target, its handle holds a slot). -/
def IdealSlots {count : ℕ} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (t : Target count) (slots : Handle → Option (Slot 2)) (transcript : List Entry) : Prop :=
  (∀ keyId slot, slots (.peer keyId) = some slot → slot = 0 ∧ peerOf t transcript = some keyId) ∧
    (∀ owner slot, slots (.owner owner) = some slot → owner = t.kem.val) ∧
    (∀ keyId, designate crypto codec serverKid transcript (.peer keyId) = some (t.accept, t.kem.val) →
      slots (.peer keyId) = some 0) ∧
    (BeaconLinked crypto codec serverKid t transcript → (slots (.owner t.kem.val)).isSome)

end Transcript

/-! ### Transcript lemmas -/

section TranscriptFacts

/-- Appending an entry appends its reply to the accept replies exactly when it is a raw accept. -/
theorem acceptReplies_append (transcript : List Entry) (entry : Entry) :
    acceptReplies (transcript ++ [entry]) = acceptReplies transcript ++ acceptReplies [entry] := by
  simp only [acceptReplies, List.filterMap_append]

/-- The accept replies of one non-accept entry are empty. -/
theorem acceptReplies_other (entry : Entry) (other : ∀ raw reply, entry ≠ ⟨.inl (.inr (.accept raw)), reply⟩) :
    acceptReplies [entry] = [] := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command with
    | accept raw => exact absurd rfl (other raw reply)
    | _ => rfl
  · rfl

/-- One accept entry contributes its reply. -/
theorem acceptReplies_accept (raw : Pqxdh.Bytes) (reply : Option ℕ) :
    acceptReplies [(⟨.inl (.inr (.accept raw)), reply⟩ : Entry)] = [reply] := rfl

/-- There is one accept reply per raw accept attempt. -/
theorem acceptReplies_length (transcript : List Entry) : (acceptReplies transcript).length = acceptCount transcript := by
  induction transcript with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨(coin | command) | secrecy, reply⟩
      · simpa [acceptReplies, acceptCount] using ih
      · cases command <;> simpa [acceptReplies, acceptCount, List.countP_cons] using ih
      · simpa [acceptReplies, acceptCount] using ih

/-- An entry that is not a raw accept keeps every accept ordinal's session. -/
theorem sessionAt_other (transcript : List Entry) (entry : Entry)
    (other : ∀ raw reply, entry ≠ ⟨.inl (.inr (.accept raw)), reply⟩) (i : ℕ) :
    sessionAt (transcript ++ [entry]) i = sessionAt transcript i := by
  simp only [sessionAt, acceptReplies_append, acceptReplies_other entry other, List.append_nil]

/-- An entry keeps the session of every accept ordinal that already happened. -/
theorem sessionAt_before (transcript : List Entry) (entry : Entry) (i : ℕ) (before : i < acceptCount transcript) :
    sessionAt (transcript ++ [entry]) i = sessionAt transcript i := by
  rw [← acceptReplies_length] at before
  simp only [sessionAt, acceptReplies_append, List.getElem?_append_left before]

/-- The accept attempt of the next ordinal returns its reply. -/
theorem sessionAt_accept (transcript : List Entry) (raw : Pqxdh.Bytes) (reply : Option ℕ) :
    sessionAt (transcript ++ [⟨.inl (.inr (.accept raw)), reply⟩]) (acceptCount transcript) = reply := by
  simp only [sessionAt, acceptReplies_append, acceptReplies_accept, ← acceptReplies_length,
    List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.bind_some, id]

/-- An entry that is not a raw accept keeps the number of accept attempts. -/
theorem acceptCount_other (transcript : List Entry) (entry : Entry)
    (other : ∀ raw reply, entry ≠ ⟨.inl (.inr (.accept raw)), reply⟩) :
    acceptCount (transcript ++ [entry]) = acceptCount transcript := by
  rw [← acceptReplies_length, ← acceptReplies_length, acceptReplies_append, acceptReplies_other entry other,
    List.append_nil]

/-- A raw accept entry adds one accept attempt. -/
theorem acceptCount_accept (transcript : List Entry) (raw : Pqxdh.Bytes) (reply : Option ℕ) :
    acceptCount (transcript ++ [⟨.inl (.inr (.accept raw)), reply⟩]) = acceptCount transcript + 1 := by
  rw [← acceptReplies_length, ← acceptReplies_length, acceptReplies_append, acceptReplies_accept, List.length_append,
    List.length_singleton]

/-- An entry that is not a successful build of a session keeps the session's first build response. -/
theorem buildOf_other (transcript : List Entry) (entry : Entry) (session : ℕ)
    (other : ∀ payload response, entry ≠ ⟨.inl (.inr (.build session payload)), some response⟩) :
    buildOf (transcript ++ [entry]) session = buildOf transcript session := by
  unfold buildOf
  rw [List.findSome?_append]
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · simp
  · cases command with
    | build index payload =>
        rcases reply with _ | response
        · simp
        · by_cases same : index = session
          · subst same
            exact absurd rfl (other payload response)
          · simp [same]
    | _ => simp
  · simp

/-- A successful build of a session without an earlier successful build gives the session's first build response. -/
theorem buildOf_build (transcript : List Entry) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response) (first : buildOf transcript session = none) :
    buildOf (transcript ++ [⟨.inl (.inr (.build session payload)), some response⟩]) session = some response := by
  unfold buildOf at first ⊢
  rw [List.findSome?_append, first]
  simp

/-- A later entry never changes a session's first build response once there is one. -/
theorem buildOf_some (transcript : List Entry) (entry : Entry) (session : ℕ)
    (response : PqxdhServerRegistrationPublication.Response) (found : buildOf transcript session = some response) :
    buildOf (transcript ++ [entry]) session = some response := by
  unfold buildOf at found ⊢
  rw [List.findSome?_append, found, Option.some_or]

end TranscriptFacts

/-! ### The key facts of U6 on the record world with `envGD` -/

section KeyFacts
variable {ι : Type} {baseSpec : OracleSpec ι} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) {count : ℕ}

/-- The two transcript conjuncts of U6's trace invariant `PqxdhDeploymentIdealKeymatch.KeyTrace` (they read only the transcript and the ideal backend): the accept that returned the selected ordinal has bytes that pass the native verification prefix and, when they verify to the selected PQ key, the selected session is marked; every published bundle carries the pool key at its index. -/
structure KeyFacts (t : Target count) (p : Params KemSK count) (transcript : List Entry) (core : IdealCore) : Prop where
  selected : ∀ raw, (⟨.inl (.inr (.accept raw)), some t.accept⟩ : Entry) ∈ transcript →
    ∃ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
      (value.keys.pqKey = p.chosen.1 → core.marks.isSome)
  bundles : ∀ k bytes, (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ transcript →
    PqxdhDeploymentIdealKeymatch.BundleKey codec (p.pool t) k bytes

/-- On every outcome of the final split game, the key facts hold: U6's `game_trace` on the ideal game, carried along `ideal_to_split` (equal laws through `splitView`, which keeps the ledger and the ideal backend) by `PqxdhDeploymentIdealFrame.lawEq_support`. -/
theorem split_keyFacts {A X : Type} (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A) :
    ∀ outcome ∈ support ((PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
          adversary).run runtime),
      ∀ value, outcome.1 = some value →
        KeyFacts setup codec checks t p value.2.2.1.transcript value.2.2.2.backend.2.2 := by
  intro outcome member value found
  have law := PqxdhDeploymentIdealDefer.ideal_to_split setup codec route checks t p ensureInit identityIndex bounds mode
    adversary runtime
  have viewed : PqxdhDeploymentFinishErasure.outcomeMap PqxdhDeploymentIdealKeys.splitView outcome ∈
      support (PqxdhDeploymentFinishErasure.outcomeMap PqxdhDeploymentIdealKeys.splitView <$>
        (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
          (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
            adversary).run runtime) := by
    rw [support_map]
    exact ⟨outcome, member, rfl⟩
  rw [← PqxdhDeploymentIdealFrame.lawEq_support law, support_map] at viewed
  obtain ⟨ideal, idealMember, same⟩ := viewed
  rcases idealFound : ideal.1 with _ | ⟨created, output, ledger, final⟩
  · have firsts := congrArg Prod.fst same
    simp only [PqxdhDeploymentFinishErasure.outcomeMap, idealFound, found, Option.map_none, Option.map_some,
      reduceCtorEq] at firsts
  · have firsts := congrArg Prod.fst same
    simp only [PqxdhDeploymentFinishErasure.outcomeMap, idealFound, found, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at firsts
    obtain ⟨-, -, ledgerEq, viewEq⟩ := firsts
    have core : final.backend.2.2 = value.2.2.2.backend.2.2 :=
      congrArg (fun view => view.2.1.2) viewEq
    have trace := PqxdhDeploymentIdealKeymatch.game_trace setup codec route checks t p ensureInit identityIndex bounds
      mode adversary runtime ideal idealMember created output ledger final idealFound
    rw [← ledgerEq, ← core]
    exact ⟨trace.selected, trace.bundles⟩

/-- On every outcome of the record world with the ideal environment of a target (`envGD`), the key facts hold at the drawn parameters held in the backend, for the final transcript and the final ideal backend: `split_keyFacts` carried along `PqxdhDeploymentIdealEnv.c1_split` by `PqxdhDeploymentIdealFrame.lawEq_support`. -/
theorem world_keyFacts {A X : Type} (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ)
    (runtime : A) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary),
      ∀ value, result.1 = some value →
        KeyFacts setup codec checks t value.2.2.backend.1 value.2.1.2.transcript value.2.2.backend.2.2.2 := by
  intro result member value found
  have law := PqxdhDeploymentIdealEnv.c1_split setup codec route checks t ensureInit identityIndex runtime bounds mode
    adversary
  have joinedMember : PqxdhDeploymentEnvironmentJoin.joined result ∈ support (PqxdhDeploymentEnvironmentJoin.joined <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary) := by
    rw [support_map]
    exact ⟨result, member, rfl⟩
  rw [← PqxdhDeploymentIdealFrame.lawEq_support law, mem_support_bind_iff] at joinedMember
  obtain ⟨p, -, splitMember⟩ := joinedMember
  rw [support_map] at splitMember
  obtain ⟨outcome, outcomeMember, same⟩ := splitMember
  rw [StateT.run'_eq, support_map] at outcomeMember
  obtain ⟨full, fullMember, rfl⟩ := outcomeMember
  rcases fullFound : full.1 with _ | v
  · simp only [fullFound, Option.map_none, PqxdhDeploymentEnvironmentJoin.joined, found, Option.map_some,
      reduceCtorEq] at same
  · simp only [fullFound, Option.map_some, PqxdhDeploymentEnvironmentJoin.joined, found, Option.some.injEq,
      Prod.mk.injEq] at same
    obtain ⟨-, -, ledgerEq, stateEq⟩ := same
    have backend := congrArg PqxdhDeploymentBackend.XState.backend stateEq
    simp only [PqxdhDeploymentEnvironmentDraw.withX, PqxdhDeploymentEnvironmentJoin.merge] at backend
    have facts := split_keyFacts setup codec route checks t p ensureInit identityIndex bounds mode adversary runtime full
      fullMember v fullFound
    rw [← ledgerEq, ← backend]
    exact facts

/-- The key match from the key facts (the argument of `PqxdhDeploymentIdealKeymatch.ideal_keymatch`): under `Phase1ReadBack`, a designation of the target's raw-accept ordinal and KEM creation index on the transcript implies that the selected session is marked. -/
theorem keyFacts_marked (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (serverKid : Std.U64)
    (t : Target count) (p : Params KemSK count) (transcript : List Entry) (core : IdealCore)
    (facts : KeyFacts setup codec checks t p transcript core) (handle : Handle)
    (designated : designate setup.source.crypto codec serverKid transcript handle = some (t.accept, t.kem.val)) :
    core.marks.isSome := by
  obtain ⟨raw, accepted, keys, published, rawFound, candidateFound, keysFound, publishedFound, pqFound⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys setup.source.crypto codec serverKid transcript handle t.accept
      t.kem.val designated
  obtain ⟨value, verified, marked⟩ := facts.selected raw
    (PqxdhDeploymentKemTransfer.acceptOf_mem transcript t.accept raw rawFound)
  obtain ⟨candidateEq, keysEq⟩ := PqxdhDeploymentKeyMatch.verified_keys setup codec checks raw value verified
  rw [candidateFound, Option.some.injEq] at candidateEq
  subst candidateEq
  rw [keysFound, Option.some.injEq] at keysEq
  subst keysEq
  obtain ⟨bytes, bytesFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨identity, tuple, s1, s2, s3, written, pooled⟩ := facts.bundles t.kem.val bytes
    (PqxdhDeploymentKeyMatch.bundleOf_mem transcript t.kem.val bytes bytesFound)
  rw [PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at publishedRead
  subst publishedRead
  rw [PqxdhDeploymentKeyMatch.publishedPq_candidate, Option.some.injEq] at pqFound
  apply marked
  rw [← pqFound]
  exact pooled p.chosen (PqxdhDeploymentIdealParams.pool_kem t p)

end KeyFacts

/-! ### Slot maps -/

section Slots

/-- The handle-to-slot map of a provenance annotation of the record world (`PqxdhRecordLiftOrigins`). -/
def originSlots (o : PqxdhRecordLiftOrigins.Origins 2) : Handle → Option (Slot 2)
  | .peer keyId => o.peers keyId
  | .owner index => o.owners index

/-- The provenance annotation that the ideal environment's install ghosts determine: the Server peer of the Server ghost holds the slot allocated to its coordinates, owner `k` holds the slot allocated to the Beacon ghost's coordinates, and no other handle holds a slot. -/
def ghostOrigins {count : ℕ} (t : Target count) (alloc : Alloc Coord 2) (core : IdealCore) :
    PqxdhRecordLiftOrigins.Origins 2 :=
  ⟨fun keyId => match core.peer with
      | some (kid, c) => if keyId = kid then alloc.1 c else none
      | none => none,
    fun index => if index = t.kem.val then core.beacon.bind alloc.1 else none⟩

end Slots

/-! ### The KEM ciphertext guess quantities (design-v2 section 7.1, plan section 49 Q2) -/

section Guess
variable {ι : Type} {baseSpec : OracleSpec ι} (setup : Setup baseSpec KemSK)

/-- The best probability of guessing the challenge ciphertext from the key pair (design-v2 section 7.1, `ctGuess`): the supremum over guess functions of the key pair of the probability that an encapsulation to the public key has the guessed ciphertext. A definition, like `PqxdhRegistrationJointKemRawGame.correctnessError`, not an assumption. -/
noncomputable def ctGuess : ENNReal :=
  ⨆ guess : Pair KemSK → PqxdhKemIndCca.MlKem768Ciphertext,
    𝒟[simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (do
      let pair ← setup.kem.keygen
      let encapsulated ← setup.kem.encaps pair.1
      pure (decide (encapsulated.1 = guess pair)))] {true}

/-- The restriction of `ctGuess` to guesses of the public key alone: the supremum over all functions of the public key, including inefficient ones, of the probability that an encapsulation to the public key has the guessed ciphertext. An information-theoretic quantity of the scheme, not the form that CE-12a's IND-CCA reduction consumes (plan section 49, Q2): that reduction needs a guesser program constructed from the adversary, `PqxdhDeploymentIdealAnomaly.ctGuessBy`, which is at most `ctGuessPk` (`PqxdhDeploymentIdealAnomaly.ctGuessBy_le`). -/
noncomputable def ctGuessPk : ENNReal :=
  ⨆ guess : PqxdhKemIndCca.MlKem768PublicKey → PqxdhKemIndCca.MlKem768Ciphertext,
    𝒟[simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (do
      let pair ← setup.kem.keygen
      let encapsulated ← setup.kem.encaps pair.1
      pure (decide (encapsulated.1 = guess pair.1)))] {true}

/-- A guess of the public key alone is a guess of the key pair. -/
theorem ctGuessPk_le : ctGuessPk setup ≤ ctGuess setup :=
  iSup_le fun guess => le_iSup_of_le (fun pair : Pair KemSK => guess pair.1) le_rfl

end Guess

end BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptReplies_append' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptReplies_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptReplies_other' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptReplies_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptReplies_accept' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptReplies_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptReplies_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptReplies_length

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.sessionAt_other' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.sessionAt_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.sessionAt_before' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.sessionAt_before

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.sessionAt_accept' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.sessionAt_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptCount_other' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptCount_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptCount_accept' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.acceptCount_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.buildOf_other' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.buildOf_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.buildOf_build' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.buildOf_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.buildOf_some' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.buildOf_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.split_keyFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.split_keyFacts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.world_keyFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.world_keyFacts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.keyFacts_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.keyFacts_marked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.ctGuessPk_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace.ctGuessPk_le
