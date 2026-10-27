-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts

/-!
# The Beacon converse and the full C5 restated for the ideal environment (CE-11b, unit U4)

The Beacon converse of C5 (design-v2 section 7.2, L4) and with it the full `ideal_slots` on the record world with the ideal environment of a target, through a second invariant of the provenance-annotated record world kept beside `PqxdhDeploymentIdealProvenance.Prov`:

- Transcript facts: `LateFinish` (a successful finish of owner `k` made after the selected raw accept) with `lateFinish_append`, `lateFinish_count` and `finish_split` (every successful finish of owner `k` is made before the selected raw accept, `PqxdhDeploymentIdealTrace.FinishBefore`, or late); `finishOf_mem`.
- The challenge ciphertext in public bytes: `ChallengeRead` (a finish input whose Phase 2 reader gives a ciphertext with the challenge ciphertext's bytes) and `ChallengeWritten` (a build response written by the Phase 2 writer on the fields of a candidate carrying the challenge ciphertext); under `Phase2ReadBack` the reader gives the challenge ciphertext back (`written_read`).
- `BeaconProv codec t p`, the Beacon provenance invariant between the transcript and the environment state: a mark comes only with the active flag; the marked session's pending token carries the challenge ciphertext; every successful build of the marked session is written with it; the Beacon install ghost's coordinates hold a slot; after every late finish of owner `k` whose input reads the challenge ciphertext, either no session is marked or the Beacon install ghost is set. Startup (`beacon_initial`), entries that are not registration commands (`beacon_quiet`), every command of the ideal step (`beacon_rStep`, through the state-level lemmas `beacon_realQuiet`, `beacon_acceptOther`, `beacon_selected`, `beacon_realBuild`, `beacon_markedBuild`, `beacon_challenge` and the native facts of `PqxdhDeploymentIdealBeaconFacts`), and so every outcome of the annotated record world with `envGD` together with `Prov` (`world_beacon`).
- At a state: the key match for a designation on a prefix of the transcript (`keyFacts_marked_prefix`), L3 on a prefix (`trace_designated_prefix`) and L4 on a prefix (`beacon_converse`: when owner `k` designates the target, the Beacon install ghost is set at coordinates holding a slot, or the designating finish was made before the selected raw accept).
- On every outcome of the provenance-annotated record world with `envGD`, under `Phase1ReadBack` and `Phase2ReadBack`: `ideal_slots_prefix` (the converses for designations computed on any prefix of the final transcript, with the final provenance annotation), `ideal_beacon` (L4) and `ideal_slots` (`IdealSlots ∨ Anomaly`, C5 restated).

The annotation is the World-level provenance annotation of `PqxdhRecordLiftOrigins`; its relation to the record lift's own handle-to-slot map is design-v2's `run_origins` (unit U7), not proved here. These are support facts; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry Handle)
open PqxdhDeploymentTranscript (designate buildOf acceptCount)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk initSentAt)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhRecordLiftOrigins (Origins)
open PqxdhDeploymentIdealTrace (FinishBefore BeaconLinked)
open PqxdhDeploymentIdealProvenance (Prov BuiltIn builtIn_append)
open PqxdhDeploymentIdealOrigins (QuietEntry)
open PqxdhServerRegistrationPublication (responseFields)

variable {KemSK : Type}

/-! ### Late finishes of owner k -/

section Late
variable {count : ℕ}

/-- A successful finish of owner `k` with input `raw` made after the selected raw accept: more than `t.accept` raw accept attempts precede it. -/
def LateFinish (t : Target count) (transcript : List Entry) (raw : Pqxdh.Bytes) : Prop :=
  ∃ (before : List Entry) (reply : Pqxdh.Bytes) (after : List Entry),
    transcript = before ++ (⟨.inl (.inr (.finish t.kem.val raw)), some reply⟩ : Entry) :: after ∧
      t.accept < acceptCount before

/-- The accept attempts of a prefix are at most those of the whole transcript. -/
theorem acceptCount_prefix (before after : List Entry) : acceptCount before ≤ acceptCount (before ++ after) := by
  unfold acceptCount
  rw [List.countP_append]
  exact Nat.le_add_right _ _

/-- A late finish comes after the selected raw accept. -/
theorem lateFinish_count (t : Target count) (transcript : List Entry) (raw : Pqxdh.Bytes)
    (late : LateFinish t transcript raw) : t.accept < acceptCount transcript := by
  obtain ⟨before, reply, after, rfl, count⟩ := late
  exact lt_of_lt_of_le count (acceptCount_prefix before _)

/-- A late finish of an extended transcript is one of the transcript or the new entry, made after the selected raw accept. -/
theorem lateFinish_append (t : Target count) (transcript : List Entry) (entry : Entry) (raw : Pqxdh.Bytes)
    (late : LateFinish t (transcript ++ [entry]) raw) :
    LateFinish t transcript raw ∨
      ((∃ reply, entry = ⟨.inl (.inr (.finish t.kem.val raw)), some reply⟩) ∧ t.accept < acceptCount transcript) := by
  obtain ⟨before, reply, after, split, count⟩ := late
  rcases List.eq_nil_or_concat after with rfl | ⟨after', last, rfl⟩
  · obtain ⟨rfl, entryEq⟩ := List.append_inj' split rfl
    exact Or.inr ⟨⟨reply, (List.singleton_inj.mp entryEq)⟩, count⟩
  · rw [List.concat_eq_append, show before ++ (⟨.inl (.inr (.finish t.kem.val raw)), some reply⟩ : Entry) :: (after' ++ [last]) =
      (before ++ (⟨.inl (.inr (.finish t.kem.val raw)), some reply⟩ : Entry) :: after') ++ [last] by simp] at split
    obtain ⟨rfl, -⟩ := List.append_inj' split rfl
    exact Or.inl ⟨before, reply, after', rfl, count⟩

/-- A successful finish entry of owner `k` in a transcript is made before the selected raw accept or late. -/
theorem finish_split (t : Target count) (transcript : List Entry) (raw reply : Pqxdh.Bytes)
    (member : (⟨.inl (.inr (.finish t.kem.val raw)), some reply⟩ : Entry) ∈ transcript) :
    FinishBefore t transcript ∨ LateFinish t transcript raw := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp member
  by_cases early : acceptCount before ≤ t.accept
  · exact Or.inl ⟨before, raw, reply, after, rfl, early⟩
  · exact Or.inr ⟨before, reply, after, rfl, Nat.lt_of_not_le early⟩

end Late

/-! ### The challenge ciphertext in public bytes -/

section Codec
variable {Reader Response : Type} (codec : Codec Reader Response)

/-- A finish input whose Phase 2 reader gives a ciphertext with the challenge ciphertext's bytes. -/
def ChallengeRead (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) : Prop :=
  ∃ ciphertext, (codec.read2 raw).bind codec.ciphertext = some ciphertext ∧
    PqxdhPhase2InputBytes.ciphertext ciphertext = challenge

/-- A build response written by the Phase 2 writer on the fields of a candidate that carries the challenge ciphertext. -/
def ChallengeWritten (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (response : PqxdhServerRegistrationPublication.Response) : Prop :=
  ∃ candidate encrypted, candidate.kem_ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧
    codec.write2 (responseFields candidate encrypted) = some response.serialized

/-- Under `Phase2ReadBack`, the ciphertext that the Phase 2 reader gives on a response written with the challenge ciphertext has the challenge ciphertext's bytes. -/
theorem written_read (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (response : PqxdhServerRegistrationPublication.Response)
    (written : ChallengeWritten codec challenge response) (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (found : (codec.read2 response.serialized).bind codec.ciphertext = some ciphertext) :
    PqxdhPhase2InputBytes.ciphertext ciphertext = challenge := by
  obtain ⟨candidate, encrypted, carried, write⟩ := written
  obtain ⟨parsed, readEq, ciphertextEq, -⟩ := phase2 _ _ write
  rw [readEq, Option.bind_some, ciphertextEq, Option.some.injEq] at found
  change candidate.kem_ciphertext = ciphertext at found
  rw [← found, carried]
  exact (PqxdhPhase2InputBytes.ciphertext_roundtrip ciphertext challenge).2

end Codec

/-! ### The Beacon provenance invariant -/

section Invariant
variable {Reader Response : Type} (codec : Codec Reader Response) {count : ℕ} (t : Target count)
  (p : Params KemSK count)

/-- The Beacon provenance invariant of the ideal environment at a target and the challenger's parameters, between the transcript and the environment state: a mark comes only with the active flag; the marked session's pending token carries the challenge ciphertext; every successful build of the marked session is written with the challenge ciphertext; the Beacon install ghost's coordinates hold a slot; and after every late finish of owner `k` whose input reads the challenge ciphertext, either no session is marked or the Beacon install ghost is set. -/
structure BeaconProv (transcript : List Entry) (e : EnvState KemSK SplitBk) : Prop where
  active : ∀ s c, e.backend.2.2.marks = some (s, c) → e.backend.2.2.active = true
  token : ∀ s c token, e.backend.2.2.marks = some (s, c) → e.native.shared.2.pending s = some token →
    token.pending.kem_ciphertext = PqxdhAcceptedRegistration.ciphertextArray p.challenge
  built : ∀ s c response, e.backend.2.2.marks = some (s, c) → BuiltIn transcript s response →
    ChallengeWritten codec p.challenge response
  slot : ∀ c, e.backend.2.2.beacon = some c → (e.backend.2.1.1 c).isSome = true
  finishes : ∀ raw, LateFinish t transcript raw → ChallengeRead codec p.challenge raw →
    e.backend.2.2.marks = none ∨ e.backend.2.2.beacon.isSome = true

/-- The Beacon provenance invariant holds at the startup: the empty transcript and the initial environment state of a constructed Server with the split form's initial backend. -/
theorem beacon_initial (created : PqxdhLiveServerConstruction.Created Unit) :
    BeaconProv codec t p [] (PqxdhDeploymentEnvironment.envInitial (KemSK := KemSK) created
      (PqxdhDeploymentIdealSteps.splitInit created)) := by
  refine ⟨fun _ _ marked => ?_, fun _ _ _ marked => ?_, fun _ _ _ marked => ?_, fun _ beacon => ?_,
    fun _ late => ?_⟩
  all_goals try (simp [PqxdhDeploymentEnvironment.envInitial, PqxdhDeploymentIdealSteps.splitInit, IdealCore.initial]
    at marked)
  · simp [PqxdhDeploymentEnvironment.envInitial, PqxdhDeploymentIdealSteps.splitInit, IdealCore.initial] at beacon
  · obtain ⟨before, reply, after, split, -⟩ := late
    simp at split

/-- An entry that is not a registration command is neither a build nor a finish. -/
theorem quiet_finish (entry : Entry) (quiet : QuietEntry entry) (owner : ℕ) (raw : Pqxdh.Bytes)
    (reply : Option Pqxdh.Bytes) : entry ≠ ⟨.inl (.inr (.finish owner raw)), reply⟩ :=
  fun same => quiet ⟨.finish owner raw, trivial⟩ reply same

/-- The Beacon provenance invariant survives an entry that is not a registration command. -/
theorem beacon_quiet (transcript : List Entry) (e : EnvState KemSK SplitBk) (entry : Entry) (quiet : QuietEntry entry)
    (holds : BeaconProv codec t p transcript e) : BeaconProv codec t p (transcript ++ [entry]) e := by
  obtain ⟨_, notBuild⟩ := PqxdhDeploymentIdealProvenance.quiet_kinds entry quiet
  refine ⟨holds.active, holds.token, fun s c response marked built => ?_, holds.slot, fun raw late read => ?_⟩
  · rcases builtIn_append transcript entry s response built with old | ⟨payload, same⟩
    · exact holds.built s c response marked old
    · exact absurd same (notBuild s payload _)
  · rcases lateFinish_append t transcript entry raw late with old | ⟨⟨reply, same⟩, -⟩
    · exact holds.finishes raw old read
    · exact absurd same (quiet_finish entry quiet t.kem.val raw (some reply))

end Invariant

/-! ### Preservation by the commands, at the level of states -/

section Moves
variable {Reader Response : Type} (codec : Codec Reader Response) {count : ℕ} (t : Target count)
  (p : Params KemSK count)

/-- A command that is not a build, keeps the backend and the pending tokens, and is not a late finish of owner `k` reading the challenge ciphertext while a session is marked, keeps the Beacon provenance invariant. -/
theorem beacon_realQuiet (transcript : List Entry) (e e' : EnvState KemSK SplitBk) (entry : Entry)
    (holds : BeaconProv codec t p transcript e) (backend : e'.backend = e.backend)
    (pending : e'.native.shared.2.pending = e.native.shared.2.pending)
    (notBuild : ∀ session payload reply, entry ≠ ⟨.inl (.inr (.build session payload)), reply⟩)
    (notLate : ∀ raw reply, entry = ⟨.inl (.inr (.finish t.kem.val raw)), some reply⟩ →
      t.accept < acceptCount transcript → ChallengeRead codec p.challenge raw → e.backend.2.2.marks = none) :
    BeaconProv codec t p (transcript ++ [entry]) e' := by
  refine ⟨fun s c marked => ?_, fun s c token marked found => ?_, fun s c response marked built => ?_,
    fun c beacon => ?_, fun raw late read => ?_⟩
  · rw [backend] at marked ⊢; exact holds.active s c marked
  · rw [backend] at marked; rw [pending] at found; exact holds.token s c token marked found
  · rw [backend] at marked
    rcases builtIn_append transcript entry s response built with old | ⟨payload, same⟩
    · exact holds.built s c response marked old
    · exact absurd same (notBuild s payload _)
  · rw [backend] at beacon ⊢; exact holds.slot c beacon
  · rw [backend]
    rcases lateFinish_append t transcript entry raw late with old | ⟨⟨reply, same⟩, count⟩
    · exact holds.finishes raw old read
    · exact Or.inl (notLate raw reply same count read)

/-- A raw accept other than the selected ordinal, run on the backend with the accept counter advanced, which publishes at most one token at the session counter, keeps the Beacon provenance invariant. -/
theorem beacon_acceptOther (transcript : List Entry) (e e' : EnvState KemSK SplitBk) (raw : Pqxdh.Bytes)
    (reply : Option ℕ) (w : PqxdhRecordLiftWorld.State 2) (holds : BeaconProv codec t p transcript e)
    (inv : PqxdhDeploymentIdealEnv.IdealInv t e w)
    (backend : e'.backend = PqxdhDeploymentIdealEnvStep.bump e.backend)
    (pending : e'.native.shared.2.pending = e.native.shared.2.pending ∨ ∃ token,
      e'.native.shared.2.pending = Function.update e.native.shared.2.pending e.native.shared.2.sessions (some token)) :
    BeaconProv codec t p (transcript ++ [⟨.inl (.inr (.accept raw)), reply⟩]) e' := by
  have notBuild : ∀ session payload reply', (⟨.inl (.inr (.accept raw)), reply⟩ : Entry) ≠
      ⟨.inl (.inr (.build session payload)), reply'⟩ := fun session payload reply' =>
    PqxdhDeploymentIdealProvenance.accept_notBuild raw reply session payload reply'
  refine ⟨fun s c marked => ?_, fun s c token marked found => ?_, fun s c response marked built => ?_,
    fun c beacon => ?_, fun raw' late read => ?_⟩
  · rw [backend] at marked ⊢; exact holds.active s c marked
  · rw [backend] at marked
    have below := (inv.markedSession s c marked).1
    rcases pending with same | ⟨token', same⟩
    · rw [same] at found; exact holds.token s c token marked found
    · rw [same, Function.update_of_ne (Nat.ne_of_lt below)] at found
      exact holds.token s c token marked found
  · rw [backend] at marked
    rcases builtIn_append transcript _ s response built with old | ⟨payload, same⟩
    · exact holds.built s c response marked old
    · exact absurd same (notBuild s payload _)
  · rw [backend] at beacon ⊢; exact holds.slot c beacon
  · rw [backend]
    rcases lateFinish_append t transcript _ raw' late with old | ⟨⟨reply', same⟩, -⟩
    · exact holds.finishes raw' old read
    · simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same

/-- The selected raw accept, with the facts of `PqxdhDeploymentIdealBeaconFacts.acceptSelected_token` and `PqxdhDeploymentIdealEnvFacts.acceptSelected_move`, keeps the Beacon provenance invariant. -/
theorem beacon_selected (transcript : List Entry) (e e' : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (o : Origins 2) (raw : Pqxdh.Bytes) (reply : Option ℕ) (prov : Prov t transcript e w o)
    (inv : PqxdhDeploymentIdealEnv.IdealInv t e w) (selected : e.backend.2.2.accepts = t.accept)
    (marks : ∀ i c, e'.backend.2.2.marks = some (i, c) → i = e.native.shared.2.sessions)
    (beacon : e'.backend.2.2.beacon = e.backend.2.2.beacon)
    (tokenFact : e'.backend.2.2.marks.isSome = true → e'.backend.2.2.active = true ∧
      ((reply = none ∧ e'.native.shared.2.pending = e.native.shared.2.pending) ∨
        ∃ token, token.pending.kem_ciphertext = PqxdhAcceptedRegistration.ciphertextArray p.challenge ∧
          reply = some e.native.shared.2.sessions ∧
          e'.native.shared.2.pending = Function.update e.native.shared.2.pending e.native.shared.2.sessions
            (some token))) :
    BeaconProv codec t p (transcript ++ [⟨.inl (.inr (.accept raw)), reply⟩]) e' := by
  obtain ⟨_, _, _, beaconNone, _⟩ := inv.before (le_of_eq selected)
  obtain ⟨_, pendingBelow, builds⟩ := prov.early (le_of_eq selected)
  have count : acceptCount transcript = t.accept := by rw [prov.accepts, selected]
  refine ⟨fun s c marked => (tokenFact (by rw [marked]; rfl)).1, fun s c token marked found => ?_,
    fun s c response marked built => ?_, fun c found => ?_, fun raw' late read => ?_⟩
  · have atCounter := marks s c marked
    subst atCounter
    rcases (tokenFact (by rw [marked]; rfl)).2 with ⟨_, same⟩ | ⟨token', carried, _, same⟩
    · rw [same] at found
      have below := pendingBelow _ (by rw [found]; rfl)
      exact absurd below (lt_irrefl _)
    · rw [same, Function.update_self, Option.some.injEq] at found
      rw [← found]
      exact carried
  · have atCounter := marks s c marked
    have below := builds s response (PqxdhDeploymentIdealProvenance.builtIn_accept transcript raw reply s response built)
    rw [atCounter] at below
    exact absurd below (lt_irrefl _)
  · rw [beacon, beaconNone] at found; cases found
  · rcases lateFinish_append t transcript _ raw' late with old | ⟨⟨reply', same⟩, -⟩
    · have later := lateFinish_count t transcript raw' old
      rw [count] at later
      exact absurd later (lt_irrefl _)
    · simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same

/-- A real build of a session that is not the marked session with a pending token, which consumes the session's token, returns a response only from a pending token and keeps the backend, keeps the Beacon provenance invariant. -/
theorem beacon_realBuild (transcript : List Entry) (e e' : EnvState KemSK SplitBk) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (reply : Option PqxdhServerRegistrationPublication.Response)
    (holds : BeaconProv codec t p transcript e) (backend : e'.backend = e.backend)
    (pending : e'.native.shared.2.pending = Function.update e.native.shared.2.pending session none)
    (tokened : reply.isSome = true → (e.native.shared.2.pending session).isSome = true)
    (notMarked : ∀ c, e.backend.2.2.marks = some (session, c) → (e.native.shared.2.pending session).isSome = false) :
    BeaconProv codec t p (transcript ++ [⟨.inl (.inr (.build session payload)), reply⟩]) e' := by
  refine ⟨fun s c marked => ?_, fun s c token marked found => ?_, fun s c response marked built => ?_,
    fun c beacon => ?_, fun raw late read => ?_⟩
  · rw [backend] at marked ⊢; exact holds.active s c marked
  · rw [backend] at marked
    rw [pending] at found
    by_cases same : s = session
    · subst same; simp at found
    · rw [Function.update_of_ne same] at found
      exact holds.token s c token marked found
  · rw [backend] at marked
    rcases builtIn_append transcript _ s response built with old | ⟨payload', same⟩
    · exact holds.built s c response marked old
    · simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
        PqxdhDeploymentInterface.Command.build.injEq] at same
      obtain ⟨⟨rfl, -⟩, same⟩ := same
      have open_ := tokened (by rw [eq_of_heq same]; rfl)
      rw [notMarked c marked] at open_
      cases open_
  · rw [backend] at beacon ⊢; exact holds.slot c beacon
  · rw [backend]
    rcases lateFinish_append t transcript _ raw late with old | ⟨⟨reply', same⟩, -⟩
    · exact holds.finishes raw old read
    · simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same

/-- The marked build of the marked session with its pending token, which consumes the token, changes only the Server install ghost of the backend and writes every response with the challenge ciphertext, keeps the Beacon provenance invariant. -/
theorem beacon_markedBuild (transcript : List Entry) (e e' : EnvState KemSK SplitBk) (session : ℕ)
    (coords : PqxdhDeploymentIdealSlots.Coord) (payload : Option Pqxdh.Bytes)
    (reply : Option PqxdhServerRegistrationPublication.Response) (holds : BeaconProv codec t p transcript e)
    (marked : e.backend.2.2.marks = some (session, coords)) (alloc : e'.backend.2.1 = e.backend.2.1)
    (core : e'.backend.2.2 = { e.backend.2.2 with peer := e'.backend.2.2.peer })
    (consumed : e'.native.shared.2.pending session = none)
    (written : ∀ response, reply = some response → ChallengeWritten codec p.challenge response) :
    BeaconProv codec t p (transcript ++ [⟨.inl (.inr (.build session payload)), reply⟩]) e' := by
  have marks' : e'.backend.2.2.marks = e.backend.2.2.marks := by rw [core]
  have active' : e'.backend.2.2.active = e.backend.2.2.active := by rw [core]
  have beacon' : e'.backend.2.2.beacon = e.backend.2.2.beacon := by rw [core]
  refine ⟨fun s c marked' => ?_, fun s c token marked' found => ?_, fun s c response marked' built => ?_,
    fun c found => ?_, fun raw late read => ?_⟩
  · rw [marks'] at marked'; rw [active']; exact holds.active s c marked'
  · rw [marks', marked, Option.some.injEq, Prod.mk.injEq] at marked'
    obtain ⟨rfl, -⟩ := marked'
    rw [consumed] at found; cases found
  · rw [marks'] at marked'
    rcases builtIn_append transcript _ s response built with old | ⟨payload', same⟩
    · exact holds.built s c response marked' old
    · simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
        PqxdhDeploymentInterface.Command.build.injEq] at same
      obtain ⟨⟨rfl, -⟩, same⟩ := same
      exact written response (eq_of_heq same)
  · rw [beacon'] at found; rw [alloc]; exact holds.slot c found
  · rw [marks', beacon']
    rcases lateFinish_append t transcript _ raw late with old | ⟨⟨reply', same⟩, -⟩
    · exact holds.finishes raw old read
    · simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same

open PqxdhDeploymentIdealEnvFacts (AllocMove) in
/-- Owner k's challenge finish, which keeps the pending tokens, moves the allocator, changes only the Beacon install ghost of the backend (keeping it, or setting it at coordinates that hold a slot), and sets the ghost when it returns bytes on an input reading the challenge ciphertext, keeps the Beacon provenance invariant. -/
theorem beacon_challenge (transcript : List Entry) (e e' : EnvState KemSK SplitBk) (raw : Pqxdh.Bytes)
    (reply : Option Pqxdh.Bytes) (holds : BeaconProv codec t p transcript e)
    (pending : e'.native.shared.2.pending = e.native.shared.2.pending)
    (alloc : AllocMove e.backend.2.1 e'.backend.2.1)
    (core : e'.backend.2.2 = { e.backend.2.2 with beacon := e'.backend.2.2.beacon })
    (beaconMove : e'.backend.2.2.beacon = e.backend.2.2.beacon ∨
      ∃ c j, e'.backend.2.2.beacon = some c ∧ e'.backend.2.1.1 c = some j)
    (hidden : ∀ bytes, reply = some bytes → ChallengeRead codec p.challenge raw → e'.backend.2.2.beacon.isSome = true) :
    BeaconProv codec t p (transcript ++ [⟨.inl (.inr (.finish t.kem.val raw)), reply⟩]) e' := by
  have marks' : e'.backend.2.2.marks = e.backend.2.2.marks := by rw [core]
  have active' : e'.backend.2.2.active = e.backend.2.2.active := by rw [core]
  have kept : e.backend.2.2.beacon.isSome = true → e'.backend.2.2.beacon.isSome = true := fun found => by
    rcases beaconMove with same | ⟨c, j, same, _⟩
    · rw [same]; exact found
    · rw [same]; rfl
  refine ⟨fun s c marked => ?_, fun s c token marked found => ?_, fun s c response marked built => ?_,
    fun c found => ?_, fun raw' late read => ?_⟩
  · rw [marks'] at marked; rw [active']; exact holds.active s c marked
  · rw [marks'] at marked; rw [pending] at found; exact holds.token s c token marked found
  · rw [marks'] at marked
    rcases builtIn_append transcript _ s response built with old | ⟨payload, same⟩
    · exact holds.built s c response marked old
    · simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same
  · rcases beaconMove with same | ⟨c', j, same', slotted⟩
    · rw [same] at found
      obtain ⟨j, slot⟩ := Option.isSome_iff_exists.mp (holds.slot c found)
      rw [alloc.keeps c j slot]; rfl
    · rw [same', Option.some.injEq] at found
      subst found
      rw [slotted]; rfl
  · rw [marks']
    rcases lateFinish_append t transcript _ raw' late with old | ⟨⟨reply', same⟩, -⟩
    · rcases holds.finishes raw' old read with none | some
      · exact Or.inl none
      · exact Or.inr (kept some)
    · simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, PqxdhDeploymentInterface.Command.finish.injEq,
        true_and] at same
      obtain ⟨rfl, same⟩ := same
      exact Or.inr (hidden reply' (eq_of_heq same) read)

end Moves

/-! ### Preservation by every command of the ideal step -/

section Programs
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealOrigins (aEffects)

/-- Every registration command of the ideal step, interpreted by the provenance-annotated World from an admissible joint state with the provenance invariant, keeps the Beacon provenance invariant with its entry appended. -/
theorem beacon_rStep (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (transcript : List Entry) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2) (good : PqxdhDeploymentEnvironmentJoin.Good created e w)
    (inv : PqxdhDeploymentIdealEnv.IdealInv t e w) (prov : Prov t transcript e w o)
    (holds : BeaconProv codec t p transcript e) :
    ∀ result ∈ support ((simulateQ (aEffects setup codec route)
        ((PqxdhDeploymentIdealEnv.idealStep setup codec checks t p query).run e)).run (w, o)),
      BeaconProv codec t p (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2 := by
  intro result member
  have notFinish : ∀ (entry : Entry) (other : ∀ owner raw reply, entry ≠ ⟨.inl (.inr (.finish owner raw)), reply⟩),
      ∀ raw reply, entry = ⟨.inl (.inr (.finish t.kem.val raw)), some reply⟩ →
        t.accept < acceptCount transcript → ChallengeRead codec p.challenge raw → e.backend.2.2.marks = none :=
    fun entry other raw reply same => absurd same (other _ _ _)
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      change result ∈ support ((simulateQ (aEffects setup codec route)
        ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := 2) setup (p.pool t) pin keyId).run e)).run (w, o)) at member
      have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
      obtain ⟨_, pending⟩ := PqxdhDeploymentIdealSessions.createPool_game setup (p.pool t) pin keyId e _ value
      have backend := (PqxdhDeploymentIdealEnvFacts.createPool_move setup t.kem.val (p.pool t) pin keyId e _ value).backend
      exact beacon_realQuiet codec t p transcript e _ _ holds backend pending
        (fun _ _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
        (notFinish _ fun _ _ _ wrong => by
          simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
  | bundle owner =>
      change result ∈ support ((simulateQ (aEffects setup codec route)
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.bundle owner, allowed⟩).run e)).run
          (w, o)) at member
      have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
      obtain ⟨_, pending⟩ := PqxdhDeploymentIdealSessions.realStep_quiet setup codec checks _
        (fun _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong) e _ value
      have backend := (PqxdhDeploymentIdealEnvFacts.realStep_move setup codec checks t.kem.val _ e _ value).backend
      exact beacon_realQuiet codec t p transcript e _ _ holds backend pending
        (fun _ _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
        (notFinish _ fun _ _ _ wrong => by
          simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
  | accept raw =>
      by_cases selected : e.backend.2.2.accepts = t.accept
      · rw [PqxdhDeploymentIdealEnv.idealStep_selected setup codec checks t p raw allowed e selected] at member
        have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
        obtain ⟨_, _, _, marks, _, _, beacon, _, _⟩ :=
          PqxdhDeploymentIdealEnvFacts.acceptSelected_move setup codec checks p raw e _ value
        exact beacon_selected codec t p transcript e _ w o raw _ prov inv selected
          (fun i c found => (marks i c found).1) beacon
          (PqxdhDeploymentIdealBeaconFacts.acceptSelected_token setup codec checks p raw e _ value)
      · rw [PqxdhDeploymentIdealEnv.idealStep_accept_other setup codec checks t p raw allowed e selected] at member
        have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
        obtain ⟨_, pending⟩ := PqxdhDeploymentIdealSessions.realStep_accept setup codec checks raw _ _ value
        have backend := (PqxdhDeploymentIdealEnvFacts.realStep_move setup codec checks t.kem.val _ _ _ value).backend
        exact beacon_acceptOther codec t p transcript e _ raw _ w holds inv backend pending
  | build session payload =>
      rcases PqxdhDeploymentIdealEnv.idealStep_build setup codec checks t p session payload allowed e with
        ⟨coords, marked, tokened, step⟩ | ⟨notMarked, step⟩
      · rw [step] at member
        obtain ⟨_, j, allocated, unused, cachedSome⟩ :=
          PqxdhDeploymentIdealEnv.idealInv_build_ready t e w inv session coords marked tokened
        obtain ⟨token, tokenFound⟩ := Option.isSome_iff_exists.mp tokened
        obtain ⟨material, cached⟩ := Option.isSome_iff_exists.mp cachedSome
        obtain ⟨alloc, core, consumed, _⟩ := PqxdhDeploymentIdealProvenance.buildCached_reply setup codec checks created
          session payload coords e w good j token material allocated tokenFound cached unused _
          (PqxdhDeploymentIdealProvenance.erase_member setup codec route _ w o result member)
        have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
        refine beacon_markedBuild codec t p transcript e _ session coords payload _ holds marked alloc core consumed
          fun response replied => ?_
        obtain ⟨candidate, encrypted, carried, written⟩ := PqxdhDeploymentIdealBeaconFacts.buildCached_written setup codec
          checks session payload coords e j token material allocated tokenFound cached _ value response replied
        exact ⟨candidate, encrypted, by rw [carried]; exact holds.token session coords token marked tokenFound, written⟩
      · rw [step] at member
        have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
        obtain ⟨_, pending, tokenedReply⟩ :=
          PqxdhDeploymentIdealSessions.realStep_build setup codec checks session payload e _ value
        have backend := (PqxdhDeploymentIdealEnvFacts.realStep_move setup codec checks t.kem.val _ e _ value).backend
        refine beacon_realBuild codec t p transcript e _ session payload _ holds backend pending tokenedReply
          fun c marked => ?_
        cases found : (e.native.shared.2.pending session).isSome
        · rfl
        · exact absurd ⟨rfl, found⟩ (notMarked session c marked)
  | finish owner raw =>
      by_cases chosen : e.backend.2.2.active = true ∧ owner = t.kem.val ∧
          PqxdhDeploymentIdealSteps.initSentAt e.native.owners owner = true
      · rw [PqxdhDeploymentIdealEnv.idealStep_challenge setup codec checks t p owner raw allowed e chosen] at member
        obtain ⟨_, rfl, initSent⟩ := chosen
        obtain ⟨_, _, unused⟩ := PqxdhDeploymentIdealEnv.idealInv_finish_ready t e w inv initSent
        obtain ⟨_, pending, _, alloc, _, core, beaconMove, _⟩ := PqxdhDeploymentIdealEnvFacts.finishChallenge_move setup
          codec created p t.kem.val raw e w good initSent unused _
          (PqxdhDeploymentIdealProvenance.erase_member setup codec route _ w o result member)
        have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
        refine beacon_challenge codec t p transcript e _ raw _ holds pending alloc core
          (beaconMove.imp (fun same => same.1) (fun ⟨c, j, found, slot, _⟩ => ⟨c, j, found, slot⟩))
          fun bytes replied read => ?_
        obtain ⟨ciphertext, readFound, same⟩ := read
        obtain ⟨c, j, found, _⟩ := PqxdhDeploymentIdealBeaconFacts.finishChallenge_beacon setup codec p t.kem.val raw e
          ciphertext readFound same _ value bytes replied
        rw [found]; rfl
      · rw [PqxdhDeploymentIdealEnv.idealStep_finish_real setup codec checks t p owner raw allowed e chosen] at member
        have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
        obtain ⟨_, pending⟩ := PqxdhDeploymentIdealSessions.realStep_quiet setup codec checks _
          (fun _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong) e _ value
        have backend := (PqxdhDeploymentIdealEnvFacts.realStep_move setup codec checks t.kem.val _ e _ value).backend
        refine beacon_realQuiet codec t p transcript e _ _ holds backend pending
          (fun _ _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
          fun raw' reply' same _ _ => ?_
        simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, PqxdhDeploymentInterface.Command.finish.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, replied⟩ := same
        rcases marked : e.backend.2.2.marks with _ | ⟨s, c⟩
        · rfl
        · have active := holds.active s c marked
          have notInitSent : PqxdhDeploymentIdealSteps.initSentAt e.native.owners t.kem.val = false := by
            cases found : PqxdhDeploymentIdealSteps.initSentAt e.native.owners t.kem.val
            · rfl
            · exact absurd ⟨active, rfl, found⟩ chosen
          have none := PqxdhDeploymentIdealBeaconFacts.realFinish_none setup codec checks t.kem.val raw allowed e
            notInitSent _ value
          rw [eq_of_heq replied] at none
          cases none
  | hmac key message =>
      change result ∈ support ((simulateQ (aEffects setup codec route)
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.hmac key message, allowed⟩).run e)).run
          (w, o)) at member
      have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
      obtain ⟨_, pending⟩ := PqxdhDeploymentIdealSessions.realStep_quiet setup codec checks _
        (fun _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong) e _ value
      have backend := (PqxdhDeploymentIdealEnvFacts.realStep_move setup codec checks t.kem.val _ e _ value).backend
      exact beacon_realQuiet codec t p transcript e _ _ holds backend pending
        (fun _ _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
        (notFinish _ fun _ _ _ wrong => by
          simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

end Programs

/-! ### Consequences at a state: the converse on every prefix of the transcript -/

section Consequences
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}

/-- The input of an owner's first successful finish comes from a successful finish entry of the transcript. -/
theorem finishOf_mem (transcript : List Entry) (owner : ℕ) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.finishOf transcript owner = some raw) :
    ∃ reply, (⟨.inl (.inr (.finish owner raw)), some reply⟩ : Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · cases value
  · cases command with
    | finish index input =>
        cases reply with
        | none => cases value
        | some other =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact ⟨other, member⟩
            · cases value
    | _ => cases value
  · cases value

/-- The key match from the key facts of the whole transcript and a designation on a prefix of it (`PqxdhDeploymentIdealTrace.keyFacts_marked` for prefixes): under `Phase1ReadBack`, a designation of the target's raw-accept ordinal and KEM creation index on a prefix implies that the selected session is marked. The designation's accept and bundle entries persist in the whole transcript. -/
theorem keyFacts_marked_prefix (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (serverKid : Std.U64)
    (t : Target count) (p : Params KemSK count) (transcript pre rest : List Entry) (split : transcript = pre ++ rest)
    (core : IdealCore) (facts : PqxdhDeploymentIdealTrace.KeyFacts setup codec checks t p transcript core)
    (handle : Handle) (designated : designate setup.source.crypto codec serverKid pre handle = some (t.accept, t.kem.val)) :
    core.marks.isSome := by
  obtain ⟨raw, accepted, keys, published, rawFound, candidateFound, keysFound, publishedFound, pqFound⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys setup.source.crypto codec serverKid pre handle t.accept
      t.kem.val designated
  obtain ⟨value, verified, marked⟩ := facts.selected raw (by
    rw [split]; exact List.mem_append_left rest (PqxdhDeploymentKemTransfer.acceptOf_mem pre t.accept raw rawFound))
  obtain ⟨candidateEq, keysEq⟩ := PqxdhDeploymentKeyMatch.verified_keys setup codec checks raw value verified
  rw [candidateFound, Option.some.injEq] at candidateEq
  subst candidateEq
  rw [keysFound, Option.some.injEq] at keysEq
  subst keysEq
  obtain ⟨bytes, bytesFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨identity, tuple, s1, s2, s3, written, pooled⟩ := facts.bundles t.kem.val bytes (by
    rw [split]; exact List.mem_append_left rest (PqxdhDeploymentKeyMatch.bundleOf_mem pre t.kem.val bytes bytesFound))
  rw [PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at publishedRead
  subst publishedRead
  rw [PqxdhDeploymentKeyMatch.publishedPq_candidate, Option.some.injEq] at pqFound
  apply marked
  rw [← pqFound]
  exact pooled p.chosen (PqxdhDeploymentIdealParams.pool_kem t p)

/-- L3 on a prefix: under `Phase1ReadBack` and the key facts of the whole transcript, a Server peer that designates the target on a prefix of the transcript is the Server install ghost's key ID. -/
theorem trace_designated_prefix (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (serverKid : Std.U64)
    (t : Target count) (p : Params KemSK count) (transcript pre rest : List Entry) (split : transcript = pre ++ rest)
    (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2) (prov : Prov t transcript e w o)
    (facts : PqxdhDeploymentIdealTrace.KeyFacts setup codec checks t p transcript e.backend.2.2) (keyId : Std.U64)
    (designated : designate setup.source.crypto codec serverKid pre (.peer keyId) = some (t.accept, t.kem.val)) :
    ∃ c, e.backend.2.2.peer = some (keyId, c) := by
  have marked := keyFacts_marked_prefix setup codec checks phase1 serverKid t p transcript pre rest split
    e.backend.2.2 facts (.peer keyId) designated
  obtain ⟨⟨s, c⟩, marks⟩ := Option.isSome_iff_exists.mp marked
  obtain ⟨response, _, _, _, linked, _⟩ := PqxdhDeploymentTranscript.designate_peer setup.source.crypto codec serverKid
    keyId pre t.accept t.kem.val designated
  obtain ⟨⟨payload, built⟩, keyEq⟩ := PqxdhDeploymentIdealProvenance.linkOf_built pre keyId t.accept response linked
  have selected := (prov.marked s c marks).1
  subst selected
  refine ⟨c, ?_⟩
  rw [← keyEq]
  exact prov.built _ c response marks ⟨payload, by rw [split]; exact List.mem_append_left rest built⟩

/-- L4, the Beacon converse, on a prefix of the transcript (design-v2 section 7.2): under `Phase1ReadBack` and `Phase2ReadBack`, with the provenance invariants and the key facts of the whole transcript, when owner `k` designates the target on a prefix, either the Beacon install ghost is set at coordinates holding a slot or owner `k`'s designating finish was made before the selected raw accept. The designation gives the marked session (`keyFacts_marked_prefix`); its build response is written with the challenge ciphertext, so owner `k`'s first successful finish reads it back (`written_read`); a late such finish set the ghost (`BeaconProv.finishes`). -/
theorem beacon_converse (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (serverKid : Std.U64) (t : Target count)
    (p : Params KemSK count) (transcript pre rest : List Entry) (split : transcript = pre ++ rest)
    (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2) (prov : Prov t transcript e w o)
    (holds : BeaconProv codec t p transcript e)
    (facts : PqxdhDeploymentIdealTrace.KeyFacts setup codec checks t p transcript e.backend.2.2)
    (linked : BeaconLinked setup.source.crypto codec serverKid t pre) :
    (∃ c j, e.backend.2.2.beacon = some c ∧ e.backend.2.1.1 c = some j) ∨ FinishBefore t pre := by
  have marked := keyFacts_marked_prefix setup codec checks phase1 serverKid t p transcript pre rest split
    e.backend.2.2 facts (.owner t.kem.val) linked
  obtain ⟨⟨s, c⟩, marks⟩ := Option.isSome_iff_exists.mp marked
  have selected := (prov.marked s c marks).1
  subst selected
  obtain ⟨-, -, pin, raw, ciphertext, published, pqKey, -, rawFound, ciphertextFound, -, -, -, link⟩ :=
    PqxdhDeploymentTranscript.designate_owner setup.source.crypto codec serverKid pre t.kem.val _ _ linked
  obtain ⟨response, -, -, builtFound, responseCiphertext, -⟩ := link
  obtain ⟨payload, built⟩ := PqxdhDeploymentKeyMatch.buildOf_mem pre _ response builtFound
  have written := holds.built _ c response marks ⟨payload, by rw [split]; exact List.mem_append_left rest built⟩
  have read : ChallengeRead codec p.challenge raw :=
    ⟨ciphertext, ciphertextFound, written_read codec phase2 p.challenge response written ciphertext responseCiphertext⟩
  obtain ⟨reply, member⟩ := finishOf_mem pre t.kem.val raw rawFound
  rcases finish_split t pre raw reply member with early | late
  · exact Or.inr early
  · obtain ⟨before, reply', after, preSplit, count⟩ := late
    have lateAll : LateFinish t transcript raw := ⟨before, reply', after ++ rest, by rw [split, preSplit]; simp, count⟩
    rcases holds.finishes raw lateAll read with none | some
    · rw [marks] at none; cases none
    · obtain ⟨c', found⟩ := Option.isSome_iff_exists.mp some
      obtain ⟨j, slot⟩ := Option.isSome_iff_exists.mp (holds.slot c' found)
      exact Or.inl ⟨c', j, found, slot⟩

end Consequences

/-! ### On every outcome of the annotated record world -/

section Outcomes
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentEnvironmentDraw (dropE withE paramInv)
open PqxdhDeploymentEnvironmentJoin (Good)
open PqxdhDeploymentIdealTrace (originSlots IdealSlots Anomaly)

/-- The provenance invariant and the Beacon provenance invariant (at the drawn parameters held in the backend) on every outcome of the provenance-annotated record world with the ideal environment of a target (`envGD`), together with `Good` and `IdealInv`: `PqxdhDeploymentIdealOrigins.world_keeps_origins` with `PqxdhDeploymentIdealProvenance.ideal_rStep` and `beacon_rStep`. -/
theorem world_beacon (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) serverKid bounds mode
          adversary),
      ∀ value, result.1 = some value → ∃ created, Good created value.2.2 result.2.1 ∧
        PqxdhDeploymentIdealEnv.IdealInv t (dropE value.2.2) result.2.1 ∧
        Prov t value.2.1.2.transcript (dropE value.2.2) result.2.1 result.2.2 ∧
        BeaconProv codec t value.2.2.backend.1 value.2.1.2.transcript (dropE value.2.2) := by
  have keeps := PqxdhDeploymentIdealOrigins.world_keeps_origins setup codec route
    (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime)
    (fun created => PqxdhDeploymentEnvironmentDraw.paramReg
      (fun p => PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created))
    (paramInv (fun _ => PqxdhDeploymentIdealEnv.IdealInv t))
    (PqxdhDeploymentEnvironmentDraw.stable_param _ (fun _ => PqxdhDeploymentIdealEnv.idealInv_stable t))
    (fun created => PqxdhDeploymentEnvironmentDraw.splits_param created _ _ _
      (fun p => PqxdhDeploymentIdealEnv.ideal_splits setup codec route checks t p created))
    (fun transcript e w o => Prov t transcript (dropE e) w o ∧ BeaconProv codec t e.backend.1 transcript (dropE e))
    (fun transcript e w w' o view holds =>
      ⟨PqxdhDeploymentIdealProvenance.prov_view t transcript (dropE e) w w' o view holds.1, holds.2⟩)
    (fun transcript e w o entry quiet holds =>
      ⟨PqxdhDeploymentIdealProvenance.prov_quiet t transcript (dropE e) w o entry quiet holds.1,
        beacon_quiet codec t e.backend.1 transcript (dropE e) entry quiet holds.2⟩)
    (fun created query transcript e w o good inv holds result member => ?_) ?_ serverKid bounds mode adversary
  · intro result member value found
    obtain ⟨created, good, inv, prov, beacon⟩ := keeps result member value found
    exact ⟨created, good, inv, prov, beacon⟩
  · change result ∈ support ((simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup codec route)
      (Prod.map id (withE e.backend.1) <$> (PqxdhDeploymentIdealEnv.idealStep setup codec checks t e.backend.1 query).run
        (dropE e))).run (w, o)) at member
    rw [simulateQ_map, StateT.run_map, support_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    have good' := (PqxdhDeploymentEnvironmentDraw.good_withE created e.backend.1 (dropE e) w).mp good
    exact ⟨PqxdhDeploymentIdealProvenance.ideal_rStep setup codec route checks t e.backend.1 created query transcript
        (dropE e) w o good' inv holds.1 inner innerMember,
      beacon_rStep setup codec route checks t e.backend.1 created query transcript (dropE e) w o good' inv holds.1
        holds.2 inner innerMember⟩
  · intro created start started
    change some (created, start) ∈ support (PqxdhDeploymentIdealParams.drawParams setup count >>= fun p =>
      PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime
        (fun created => (p, PqxdhDeploymentIdealSteps.splitInit created))) at started
    rw [mem_support_bind_iff] at started
    obtain ⟨p, _, startedAt⟩ := started
    have initial := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime _ created start
      startedAt
    subst initial
    exact ⟨_, rfl, PqxdhDeploymentIdealEnv.idealInv_start t created,
      PqxdhDeploymentIdealProvenance.prov_initial t created, beacon_initial codec t p created⟩

/-- `ideal_slots_prefix` (design-v2 section 7.1, the prefix-closed form of the converse): under `Phase1ReadBack` and `Phase2ReadBack`, on every outcome of the provenance-annotated record world with the ideal environment of a target and for every prefix of its final transcript, a Server peer that designates the target on the prefix holds slot 0 in the final provenance annotation (L3 on the prefix), and when owner `k` designates the target on the prefix, it holds a slot in the final provenance annotation or its designating finish was made before the selected raw accept (L4 on the prefix). The designation's transcript facts (accept, bundle, build and finish entries) persist in the final transcript, where the provenance invariants and the key facts hold; designation itself is not monotone in the transcript (a smaller owner or session can become eligible later), so the statement is about the designation computed on the prefix. -/
theorem ideal_slots_prefix (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary),
      ∀ value, result.1 = some value → ∀ pre rest, value.2.1.2.transcript = pre ++ rest →
        (∀ keyId, designate setup.source.crypto codec serverKid pre (.peer keyId) = some (t.accept, t.kem.val) →
          originSlots result.2.2 (.peer keyId) = some 0) ∧
        (BeaconLinked setup.source.crypto codec serverKid t pre →
          (originSlots result.2.2 (.owner t.kem.val)).isSome = true ∨ FinishBefore t pre) := by
  intro result member value found pre rest split
  obtain ⟨_, _, inv, prov, holds⟩ := world_beacon setup codec route checks t ensureInit identityIndex runtime
    setup.serverKeyId bounds mode adversary result member value found
  have ghost := PqxdhDeploymentIdealProvenance.origins_eq_ghost t _ _ _ _ prov inv
  have erased : (result.1, result.2.1) ∈ support (PqxdhRecordLiftWorld.run setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode
        adversary) := by
    rw [← PqxdhDeploymentIdealOrigins.annotatedRun_erase, support_map]
    exact ⟨result, member, rfl⟩
  have facts := PqxdhDeploymentIdealTrace.world_keyFacts setup codec route checks t ensureInit identityIndex runtime
    bounds mode adversary _ erased value found
  refine ⟨fun keyId designated => ?_, fun linked => ?_⟩
  · obtain ⟨c, peer⟩ := trace_designated_prefix setup codec checks phase1 serverKid t _ _ pre rest split _ _ _ prov facts
      keyId designated
    obtain ⟨zero, _⟩ := PqxdhDeploymentIdealProvenance.trace_peer t _ _ _ _ prov inv keyId c peer
    change result.2.2.peers keyId = some 0
    rw [ghost]
    simp only [PqxdhDeploymentIdealTrace.ghostOrigins, peer, ite_true, zero]
  · rcases beacon_converse setup codec checks phase1 phase2 serverKid t _ _ pre rest split _ _ _ prov holds facts linked
      with ⟨c, j, beacon, slot⟩ | early
    · left
      change (result.2.2.owners t.kem.val).isSome = true
      rw [ghost]
      simp only [PqxdhDeploymentIdealTrace.ghostOrigins, ite_true, beacon, Option.bind_some, slot, Option.isSome_some]
    · exact Or.inr early

/-- L4, the Beacon converse (design-v2 section 7.2), on every outcome of the provenance-annotated record world with the ideal environment of a target: under `Phase1ReadBack` and `Phase2ReadBack`, when owner `k` designates the target, it holds a slot in the provenance annotation or its designating finish was made before the selected raw accept (`FinishBefore`). -/
theorem ideal_beacon (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary),
      ∀ value, result.1 = some value → BeaconLinked setup.source.crypto codec serverKid t value.2.1.2.transcript →
        (originSlots result.2.2 (.owner t.kem.val)).isSome = true ∨ FinishBefore t value.2.1.2.transcript := by
  intro result member value found linked
  exact (ideal_slots_prefix setup codec route checks phase1 phase2 t ensureInit identityIndex runtime serverKid bounds
    mode adversary result member value found _ [] (List.append_nil _).symm).2 linked

/-- `ideal_slots` (design-v2 section 7.2, item 5; C5 restated): under `Phase1ReadBack` and `Phase2ReadBack`, on every outcome of the provenance-annotated record world with the ideal environment of a target, the provenance annotation satisfies `IdealSlots` (both restrictions and both converses) or the transcript has the Beacon-side anomaly (`Anomaly`: owner `k` designates the target through a finish made before the selected raw accept). From `PqxdhDeploymentIdealProvenance.ideal_slots_server` and `ideal_beacon`. -/
theorem ideal_slots (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary),
      ∀ value, result.1 = some value →
        IdealSlots setup.source.crypto codec setup.serverKeyId t (originSlots result.2.2) value.2.1.2.transcript ∨
          Anomaly setup.source.crypto codec setup.serverKeyId t value.2.1.2.transcript := by
  intro result member value found
  obtain ⟨restriction, beacon, converse⟩ := PqxdhDeploymentIdealProvenance.ideal_slots_server setup codec route checks
    phase1 t ensureInit identityIndex runtime bounds mode adversary result member value found
  by_cases linked : BeaconLinked setup.source.crypto codec setup.serverKeyId t value.2.1.2.transcript
  · rcases ideal_beacon setup codec route checks phase1 phase2 t ensureInit identityIndex runtime setup.serverKeyId bounds
      mode adversary result member value found linked with slotted | early
    · exact Or.inl ⟨restriction, beacon, converse, fun _ => slotted⟩
    · exact Or.inr ⟨linked, early⟩
  · exact Or.inl ⟨restriction, beacon, converse, fun linked' => absurd linked' linked⟩

end Outcomes

end BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.acceptCount_prefix' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.acceptCount_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.lateFinish_count' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.lateFinish_count

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.lateFinish_append' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.lateFinish_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.finish_split' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.finish_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.written_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.written_read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.quiet_finish' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.quiet_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_realQuiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_realQuiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_acceptOther' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_acceptOther

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_realBuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_realBuild

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_markedBuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_markedBuild

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_rStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_rStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.finishOf_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.finishOf_mem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.keyFacts_marked_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.keyFacts_marked_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.trace_designated_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.trace_designated_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_converse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.beacon_converse

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.world_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.world_beacon

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.ideal_slots_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.ideal_slots_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.ideal_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.ideal_beacon

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.ideal_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon.ideal_slots
