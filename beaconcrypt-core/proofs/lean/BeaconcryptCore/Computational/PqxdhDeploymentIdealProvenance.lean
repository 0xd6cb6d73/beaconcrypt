-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace
import BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins
import BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions

/-!
# Provenance of the ideal environment (CE-11b, unit U4)

C5 restated (design-v2 section 7, plan section 47 A3) on the record world with the ideal environment, through one invariant of the provenance-annotated record world with the ledger (an implementation-level replacement of design-v2 section 7.2's split-game `ideal_trace` followed by a transfer; the split-game form is derived here as well):

- `Prov t`, the provenance invariant between the transcript, the environment state, the World and the provenance annotation: the annotation invariant (`PqxdhDeploymentIdealOrigins.AnnInv`); every Server origin is at the Server install ghost's key ID and every Beacon origin at owner `k`; the accept counter counts the transcript's raw accepts; up to the selected ordinal the session counter is the accept counter and every pending token and successful build is below it; the mark is the selected ordinal's session at coordinates holding slot 0, and while its token is pending the selected accept returned it and it has no successful build; every successful build of the marked session published the Server install ghost's peer; the ghost's key ID is the target's peer in the transcript (`peerOf`).
- Preservation: by every entry that is not a registration command (`prov_quiet`), by the World's fixed steps (`prov_view`) and by every registration command of the ideal step (`ideal_rStep`), through the state-level lemmas `prov_realQuiet`, `prov_realBuild`, `prov_acceptOther`, `prov_selected`, `prov_markedBuild` and `prov_challenge` with the session facts of `PqxdhDeploymentIdealSessions`, the marked build's annotated form (`buildCached_program`, `buildCached_origins`, `buildCached_reply`) and the challenge finish's hidden installs (`finishChallenge_owner`). Startup: `prov_initial`.
- On every outcome of the provenance-annotated record world: `world_provG` (fixed parameters, `envG`) and `world_prov` (`envGD`); the annotation is the slot map of the install ghosts (`origins_eq_ghost`, `origins_ghost`).
- L1 and L3 of design-v2 section 7.2: the Server install ghost is at slot 0 and its key ID is the target's peer (`trace_peer`); under `Phase1ReadBack`, a Server peer designating the target is the ghost's key ID (`trace_designated`, with U6's key match through `PqxdhDeploymentIdealTrace.keyFacts_marked`). On the record world with `envGD` (`ideal_trace_world`) and on the final split game's own support for every parameter (`ideal_trace`, through CE-11a's `join` at `envG t p`).
- `ideal_slots_server`: three of the four conjuncts of `PqxdhDeploymentIdealTrace.IdealSlots` (the Server restriction with slot 0, the Beacon restriction, and under `Phase1ReadBack` the Server converse) on every outcome of the provenance-annotated record world with `envGD`.

Not here: the Beacon converse (L4, with the anomaly as its alternative) and hence the full `ideal_slots`, L2, `ideal_slots_prefix` and `anomaly_le` (see the CE-11b unit U4 guide). These are support facts; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry Handle)
open PqxdhDeploymentTranscript (designate buildOf acceptCount)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhRecordLiftOrigins (Origins)
open PqxdhDeploymentIdealTrace (sessionAt peerOf)
open PqxdhDeploymentIdealOrigins (AnnInv QuietEntry)

variable {KemSK : Type}

/-! ### Transcript facts -/

section Transcript

/-- A successful build entry of a session with its response. -/
def BuiltIn (transcript : List Entry) (session : ℕ) (response : PqxdhServerRegistrationPublication.Response) : Prop :=
  ∃ payload, (⟨.inl (.inr (.build session payload)), some response⟩ : Entry) ∈ transcript

/-- A successful build entry of an extended transcript is one of the transcript or the new entry. -/
theorem builtIn_append (transcript : List Entry) (entry : Entry) (session : ℕ)
    (response : PqxdhServerRegistrationPublication.Response) (built : BuiltIn (transcript ++ [entry]) session response) :
    BuiltIn transcript session response ∨ ∃ payload, entry = ⟨.inl (.inr (.build session payload)), some response⟩ := by
  obtain ⟨payload, member⟩ := built
  rcases List.mem_append.mp member with old | new
  · exact Or.inl ⟨payload, old⟩
  · exact Or.inr ⟨payload, (List.mem_singleton.mp new).symm⟩

/-- Without a successful build entry of a session, the session has no first build response. -/
theorem buildOf_none (transcript : List Entry) (session : ℕ)
    (unbuilt : ∀ response, ¬ BuiltIn transcript session response) : buildOf transcript session = none := by
  unfold buildOf
  rw [List.findSome?_eq_none_iff]
  intro entry member
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command with
    | build index payload =>
        rcases reply with _ | response
        · rfl
        · by_cases same : index = session
          · subst same
            exact absurd ⟨payload, member⟩ (unbuilt response)
          · simp [same]
    | _ => rfl
  · rfl

/-- An accept ordinal with a session is below the number of accept attempts. -/
theorem sessionAt_lt (transcript : List Entry) (i s : ℕ) (found : sessionAt transcript i = some s) :
    i < acceptCount transcript := by
  rw [← PqxdhDeploymentIdealTrace.acceptReplies_length]
  unfold sessionAt at found
  rcases h : (PqxdhDeploymentIdealTrace.acceptReplies transcript)[i]? with _ | reply
  · rw [h] at found; cases found
  · exact (List.getElem?_eq_some_iff.mp h).1

/-- A later entry keeps the session of an accept ordinal that has one. -/
theorem sessionAt_keep (transcript : List Entry) (entry : Entry) (i s : ℕ) (found : sessionAt transcript i = some s) :
    sessionAt (transcript ++ [entry]) i = some s := by
  rw [PqxdhDeploymentIdealTrace.sessionAt_before transcript entry i (sessionAt_lt transcript i s found), found]

/-- A later entry keeps the target's peer once it has one. -/
theorem peerOf_keep {count : ℕ} (t : Target count) (transcript : List Entry) (entry : Entry) (keyId : Std.U64)
    (found : peerOf t transcript = some keyId) : peerOf t (transcript ++ [entry]) = some keyId := by
  unfold peerOf at found ⊢
  obtain ⟨s, sFound, built⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨response, responseFound, rfl⟩ := Option.map_eq_some_iff.mp built
  rw [sessionAt_keep transcript entry t.accept s sFound, Option.bind_some,
    PqxdhDeploymentIdealTrace.buildOf_some transcript entry s response responseFound, Option.map_some]

/-- An entry that is not a registration command is neither a raw accept nor a build. -/
theorem quiet_kinds (entry : Entry) (quiet : QuietEntry entry) :
    (∀ raw reply, entry ≠ ⟨.inl (.inr (.accept raw)), reply⟩) ∧
      ∀ session payload reply, entry ≠ ⟨.inl (.inr (.build session payload)), reply⟩ :=
  ⟨fun raw reply same => quiet ⟨.accept raw, trivial⟩ reply same,
    fun session payload reply same => quiet ⟨.build session payload, trivial⟩ reply same⟩

end Transcript

/-! ### The provenance invariant -/

section Invariant

/-- The provenance invariant of the ideal environment at a target (design-v2 section 7.2, items 2 and 4, as one relation between the transcript, the environment state, the World and the provenance annotation): the annotation invariant; every Server origin is at the Server install ghost's key ID and every Beacon origin at owner `k`; the accept counter counts the transcript's raw accepts; up to the selected ordinal, the session counter is the accept counter and every pending token and every successful build is of a session below it; the mark is the selected ordinal's session, at coordinates holding slot 0, and while its token is pending the selected accept returned it and it has no successful build; every successful build of the marked session published the Server install ghost's peer; and the Server install ghost's key ID is the target's peer in the transcript. -/
structure Prov {count : ℕ} (t : Target count) (transcript : List Entry) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2) : Prop where
  ann : AnnInv w o
  peerKey : ∀ keyId j, o.peers keyId = some j → ∃ c, e.backend.2.2.peer = some (keyId, c)
  ownerKey : ∀ owner j, o.owners owner = some j → owner = t.kem.val
  accepts : acceptCount transcript = e.backend.2.2.accepts
  early : e.backend.2.2.accepts ≤ t.accept → e.native.shared.2.sessions = e.backend.2.2.accepts ∧
    (∀ s, (e.native.shared.2.pending s).isSome = true → s < e.native.shared.2.sessions) ∧
    (∀ s response, BuiltIn transcript s response → s < e.native.shared.2.sessions)
  marked : ∀ s c, e.backend.2.2.marks = some (s, c) → s = t.accept ∧ e.backend.2.1.1 c = some 0 ∧
    ((e.native.shared.2.pending s).isSome = true → sessionAt transcript t.accept = some s ∧
      ∀ response, ¬ BuiltIn transcript s response)
  built : ∀ s c response, e.backend.2.2.marks = some (s, c) → BuiltIn transcript s response →
    e.backend.2.2.peer = some (response.keyId, c)
  peerOf : ∀ keyId c, e.backend.2.2.peer = some (keyId, c) → peerOf t transcript = some keyId

/-- The provenance invariant reads the World only through its fixed view. -/
theorem prov_view {count : ℕ} (t : Target count) (transcript : List Entry) (e : EnvState KemSK SplitBk)
    (w w' : PqxdhRecordLiftWorld.State 2) (o : Origins 2)
    (view : PqxdhDeploymentEnvironmentJoin.fixedView w' = PqxdhDeploymentEnvironmentJoin.fixedView w)
    (holds : Prov t transcript e w o) : Prov t transcript e w' o :=
  { holds with ann := PqxdhDeploymentIdealOrigins.annInv_view w w' o view holds.ann }

/-- The provenance invariant survives an entry that is not a registration command. -/
theorem prov_quiet {count : ℕ} (t : Target count) (transcript : List Entry) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2) (entry : Entry) (quiet : QuietEntry entry)
    (holds : Prov t transcript e w o) : Prov t (transcript ++ [entry]) e w o := by
  obtain ⟨notAccept, notBuild⟩ := quiet_kinds entry quiet
  have builtOld : ∀ s response, BuiltIn (transcript ++ [entry]) s response → BuiltIn transcript s response := by
    intro s response built
    rcases builtIn_append transcript entry s response built with old | ⟨payload, same⟩
    · exact old
    · exact absurd same (notBuild s payload _)
  have sessionSame : ∀ i, sessionAt (transcript ++ [entry]) i = sessionAt transcript i := fun i =>
    PqxdhDeploymentIdealTrace.sessionAt_other transcript entry (fun raw reply => notAccept raw reply) i
  refine ⟨holds.ann, holds.peerKey, holds.ownerKey, ?_, fun before => ?_, fun s c marked => ?_,
    fun s c response marked built => holds.built s c response marked (builtOld s response built),
    fun keyId c peer => peerOf_keep t transcript entry keyId (holds.peerOf keyId c peer)⟩
  · rw [PqxdhDeploymentIdealTrace.acceptCount_other transcript entry (fun raw reply => notAccept raw reply)]
    exact holds.accepts
  · obtain ⟨sessions, pending, builds⟩ := holds.early before
    exact ⟨sessions, pending, fun s response built => builds s response (builtOld s response built)⟩
  · obtain ⟨selected, slot, open_⟩ := holds.marked s c marked
    refine ⟨selected, slot, fun tokened => ?_⟩
    obtain ⟨returned, unbuilt⟩ := open_ tokened
    exact ⟨by rw [sessionSame]; exact returned, fun response built => unbuilt response (builtOld s response built)⟩

end Invariant

/-! ### Preservation by the commands, at the level of states -/

section Moves
variable {count : ℕ} (t : Target count)

/-- A command that is neither a raw accept nor a build, keeps the backend, the session counter, the pending tokens and the annotation, and ends in a World with the annotation invariant, keeps the provenance invariant. -/
theorem prov_realQuiet (transcript : List Entry) (e e' : EnvState KemSK SplitBk) (w w' : PqxdhRecordLiftWorld.State 2)
    (o : Origins 2) (entry : Entry) (holds : Prov t transcript e w o) (ann : AnnInv w' o)
    (backend : e'.backend = e.backend) (sessions : e'.native.shared.2.sessions = e.native.shared.2.sessions)
    (pending : e'.native.shared.2.pending = e.native.shared.2.pending)
    (notAccept : ∀ raw reply, entry ≠ ⟨.inl (.inr (.accept raw)), reply⟩)
    (notBuild : ∀ session payload reply, entry ≠ ⟨.inl (.inr (.build session payload)), reply⟩) :
    Prov t (transcript ++ [entry]) e' w' o := by
  have builtOld : ∀ s response, BuiltIn (transcript ++ [entry]) s response → BuiltIn transcript s response := by
    intro s response built
    rcases builtIn_append transcript entry s response built with old | ⟨payload, same⟩
    · exact old
    · exact absurd same (notBuild s payload _)
  have sessionSame : ∀ i, sessionAt (transcript ++ [entry]) i = sessionAt transcript i := fun i =>
    PqxdhDeploymentIdealTrace.sessionAt_other transcript entry (fun raw reply => notAccept raw reply) i
  refine ⟨ann, fun keyId j found => ?_, holds.ownerKey, ?_, fun before => ?_, fun s c marked => ?_,
    fun s c response marked built => ?_, fun keyId c peer => ?_⟩
  · rw [backend]; exact holds.peerKey keyId j found
  · rw [PqxdhDeploymentIdealTrace.acceptCount_other transcript entry (fun raw reply => notAccept raw reply), backend]
    exact holds.accepts
  · rw [backend] at before ⊢
    obtain ⟨sessionsEq, pendingBelow, builds⟩ := holds.early before
    refine ⟨by rw [sessions]; exact sessionsEq, fun s found => ?_, fun s response built => ?_⟩
    · rw [pending] at found; rw [sessions]; exact pendingBelow s found
    · rw [sessions]; exact builds s response (builtOld s response built)
  · rw [backend] at marked ⊢
    obtain ⟨selected, slot, open_⟩ := holds.marked s c marked
    refine ⟨selected, slot, fun tokened => ?_⟩
    rw [pending] at tokened
    obtain ⟨returned, unbuilt⟩ := open_ tokened
    exact ⟨by rw [sessionSame]; exact returned, fun response built => unbuilt response (builtOld s response built)⟩
  · rw [backend] at marked ⊢
    exact holds.built s c response marked (builtOld s response built)
  · rw [backend] at peer
    exact peerOf_keep t transcript entry keyId (holds.peerOf keyId c peer)

/-- A real build of a session that is not the marked session with a pending token, which consumes the session's token, returns a response only from a pending token and keeps the backend, the session counter and the annotation, keeps the provenance invariant. -/
theorem prov_realBuild (transcript : List Entry) (e e' : EnvState KemSK SplitBk) (w w' : PqxdhRecordLiftWorld.State 2)
    (o : Origins 2) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (reply : Option PqxdhServerRegistrationPublication.Response) (holds : Prov t transcript e w o) (ann : AnnInv w' o)
    (backend : e'.backend = e.backend) (sessions : e'.native.shared.2.sessions = e.native.shared.2.sessions)
    (pending : e'.native.shared.2.pending = Function.update e.native.shared.2.pending session none)
    (tokened : reply.isSome = true → (e.native.shared.2.pending session).isSome = true)
    (notMarked : ∀ c, e.backend.2.2.marks = some (session, c) → (e.native.shared.2.pending session).isSome = false) :
    Prov t (transcript ++ [⟨.inl (.inr (.build session payload)), reply⟩]) e' w' o := by
  have entryBuilt : ∀ s response, BuiltIn (transcript ++ [⟨.inl (.inr (.build session payload)), reply⟩]) s response →
      BuiltIn transcript s response ∨ (s = session ∧ reply = some response) := by
    intro s response built
    rcases builtIn_append transcript _ s response built with old | ⟨payload', same⟩
    · exact Or.inl old
    · simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
        PqxdhDeploymentInterface.Command.build.injEq] at same
      obtain ⟨⟨rfl, -⟩, same⟩ := same
      exact Or.inr ⟨rfl, eq_of_heq same⟩
  have notAccept : ∀ raw reply', (⟨.inl (.inr (.build session payload)), reply⟩ : Entry) ≠
      ⟨.inl (.inr (.accept raw)), reply'⟩ := fun raw reply' same => by
    simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same
  have sessionSame : ∀ i, sessionAt (transcript ++ [⟨.inl (.inr (.build session payload)), reply⟩]) i =
      sessionAt transcript i := fun i =>
    PqxdhDeploymentIdealTrace.sessionAt_other transcript _ (fun raw reply' => notAccept raw reply') i
  have pendingAt : ∀ s, (e'.native.shared.2.pending s).isSome = true →
      s ≠ session ∧ (e.native.shared.2.pending s).isSome = true := by
    intro s found
    rw [pending] at found
    by_cases same : s = session
    · subst same; simp at found
    · rw [Function.update_of_ne same] at found
      exact ⟨same, found⟩
  refine ⟨ann, fun keyId j found => ?_, holds.ownerKey, ?_, fun before => ?_, fun s c marked => ?_,
    fun s c response marked built => ?_, fun keyId c peer => ?_⟩
  · rw [backend]; exact holds.peerKey keyId j found
  · rw [PqxdhDeploymentIdealTrace.acceptCount_other transcript _ (fun raw reply' => notAccept raw reply'), backend]
    exact holds.accepts
  · rw [backend] at before ⊢
    obtain ⟨sessionsEq, pendingBelow, builds⟩ := holds.early before
    refine ⟨by rw [sessions]; exact sessionsEq, fun s found => ?_, fun s response built => ?_⟩
    · rw [sessions]; exact pendingBelow s (pendingAt s found).2
    · rw [sessions]
      rcases entryBuilt s response built with old | ⟨rfl, replied⟩
      · exact builds s response old
      · exact pendingBelow s (tokened (by rw [replied]; rfl))
  · rw [backend] at marked ⊢
    obtain ⟨selected, slot, open_⟩ := holds.marked s c marked
    refine ⟨selected, slot, fun found => ?_⟩
    obtain ⟨ne, old⟩ := pendingAt s found
    obtain ⟨returned, unbuilt⟩ := open_ old
    refine ⟨by rw [sessionSame]; exact returned, fun response built => ?_⟩
    rcases entryBuilt s response built with old' | ⟨same, -⟩
    · exact unbuilt response old'
    · exact ne same
  · rw [backend] at marked ⊢
    rcases entryBuilt s response built with old | ⟨rfl, replied⟩
    · exact holds.built s c response marked old
    · have open_ := tokened (by rw [replied]; rfl)
      rw [notMarked c marked] at open_
      cases open_
  · rw [backend] at peer
    exact peerOf_keep t transcript _ keyId (holds.peerOf keyId c peer)

/-- A raw accept entry is not a build entry. -/
theorem accept_notBuild (raw : Pqxdh.Bytes) (reply : Option ℕ) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (response : Option PqxdhServerRegistrationPublication.Response) :
    (⟨.inl (.inr (.accept raw)), reply⟩ : Entry) ≠ ⟨.inl (.inr (.build session payload)), response⟩ := fun same => by
  simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same

/-- The successful builds after a raw accept entry are those before it. -/
theorem builtIn_accept (transcript : List Entry) (raw : Pqxdh.Bytes) (reply : Option ℕ) (s : ℕ)
    (response : PqxdhServerRegistrationPublication.Response)
    (built : BuiltIn (transcript ++ [⟨.inl (.inr (.accept raw)), reply⟩]) s response) : BuiltIn transcript s response := by
  rcases builtIn_append transcript _ s response built with old | ⟨payload, same⟩
  · exact old
  · exact absurd same (accept_notBuild raw reply s payload _)

/-- A raw accept other than the selected ordinal, run on the backend with the accept counter advanced, which raises the session counter by one, publishes at most one token at the old counter and keeps the annotation, keeps the provenance invariant. -/
theorem prov_acceptOther (transcript : List Entry) (e e' : EnvState KemSK SplitBk) (w w' : PqxdhRecordLiftWorld.State 2)
    (o : Origins 2) (raw : Pqxdh.Bytes) (reply : Option ℕ) (holds : Prov t transcript e w o)
    (inv : PqxdhDeploymentIdealEnv.IdealInv t e w) (ann : AnnInv w' o)
    (backend : e'.backend = PqxdhDeploymentIdealEnvStep.bump e.backend)
    (sessions : e'.native.shared.2.sessions = e.native.shared.2.sessions + 1)
    (pending : e'.native.shared.2.pending = e.native.shared.2.pending ∨ ∃ token,
      e'.native.shared.2.pending = Function.update e.native.shared.2.pending e.native.shared.2.sessions (some token)) :
    Prov t (transcript ++ [⟨.inl (.inr (.accept raw)), reply⟩]) e' w' o := by
  have pendingAt : ∀ s, (e'.native.shared.2.pending s).isSome = true →
      (e.native.shared.2.pending s).isSome = true ∨ s = e.native.shared.2.sessions := by
    intro s found
    rcases pending with same | ⟨token, same⟩
    · rw [same] at found; exact Or.inl found
    · rw [same] at found
      by_cases at_ : s = e.native.shared.2.sessions
      · exact Or.inr at_
      · rw [Function.update_of_ne at_] at found; exact Or.inl found
  refine ⟨ann, fun keyId j found => ?_, holds.ownerKey, ?_, fun before => ?_, fun s c marked => ?_,
    fun s c response marked built => ?_, fun keyId c peer => ?_⟩
  · rw [backend]; exact holds.peerKey keyId j found
  · rw [PqxdhDeploymentIdealTrace.acceptCount_accept, backend, holds.accepts]; rfl
  · rw [backend] at before ⊢
    change e.backend.2.2.accepts + 1 ≤ t.accept at before
    obtain ⟨sessionsEq, pendingBelow, builds⟩ := holds.early (by omega)
    refine ⟨by rw [sessions, sessionsEq]; rfl, fun s found => ?_, fun s response built => ?_⟩
    · rw [sessions]
      rcases pendingAt s found with old | rfl
      · exact Nat.lt_succ_of_lt (pendingBelow s old)
      · exact Nat.lt_succ_self _
    · rw [sessions]; exact Nat.lt_succ_of_lt (builds s response (builtIn_accept transcript raw reply s response built))
  · rw [backend] at marked ⊢
    change e.backend.2.2.marks = some (s, c) at marked
    obtain ⟨selected, slot, open_⟩ := holds.marked s c marked
    refine ⟨selected, slot, fun found => ?_⟩
    have below := (inv.markedSession s c marked).1
    have old : (e.native.shared.2.pending s).isSome = true := by
      rcases pendingAt s found with old | same
      · exact old
      · exact absurd same (Nat.ne_of_lt below)
    obtain ⟨returned, unbuilt⟩ := open_ old
    exact ⟨sessionAt_keep transcript _ t.accept s returned,
      fun response built => unbuilt response (builtIn_accept transcript raw reply s response built)⟩
  · rw [backend] at marked ⊢
    exact holds.built s c response marked (builtIn_accept transcript raw reply s response built)
  · rw [backend] at peer
    exact peerOf_keep t transcript _ keyId (holds.peerOf keyId c peer)

open PqxdhDeploymentIdealEnvFacts (AllocMove) in
/-- The selected raw accept, with the facts of `PqxdhDeploymentIdealEnvFacts.acceptSelected_move` and `PqxdhDeploymentIdealSessions.acceptSelected_pending`, keeping the annotation, keeps the provenance invariant. -/
theorem prov_selected (transcript : List Entry) (e e' : EnvState KemSK SplitBk) (w w' : PqxdhRecordLiftWorld.State 2)
    (o : Origins 2) (raw : Pqxdh.Bytes) (reply : Option ℕ) (holds : Prov t transcript e w o)
    (inv : PqxdhDeploymentIdealEnv.IdealInv t e w) (ann : AnnInv w' o)
    (selected : e.backend.2.2.accepts = t.accept)
    (alloc : AllocMove e.backend.2.1 e'.backend.2.1) (counter : e'.backend.2.1.2 ≤ e.backend.2.1.2 + 1)
    (marks : ∀ i c, e'.backend.2.2.marks = some (i, c) → i = e.native.shared.2.sessions ∧
      ((e'.backend.2.1.1 c).isSome = true ∨ 2 ≤ e'.backend.2.1.2))
    (accepts : e'.backend.2.2.accepts = e.backend.2.2.accepts + 1) (peer : e'.backend.2.2.peer = e.backend.2.2.peer)
    (pendingFact : e'.backend.2.2.marks.isSome = true →
      (reply = none ∧ e'.native.shared.2.pending = e.native.shared.2.pending) ∨
        ∃ token, reply = some e.native.shared.2.sessions ∧
          e'.native.shared.2.pending = Function.update e.native.shared.2.pending e.native.shared.2.sessions (some token)) :
    Prov t (transcript ++ [⟨.inl (.inr (.accept raw)), reply⟩]) e' w' o := by
  obtain ⟨_, _, peerNone, _, counterZero⟩ := inv.before (le_of_eq selected)
  obtain ⟨sessionsEq, pendingBelow, builds⟩ := holds.early (le_of_eq selected)
  refine ⟨ann, fun keyId j found => ?_, holds.ownerKey, ?_, fun before => ?_, fun s c marked => ?_,
    fun s c response marked built => ?_, fun keyId c found => ?_⟩
  · rw [peer]; exact holds.peerKey keyId j found
  · rw [PqxdhDeploymentIdealTrace.acceptCount_accept, accepts, holds.accepts]
  · rw [accepts, selected] at before; omega
  · obtain ⟨atCounter, slotted⟩ := marks s c marked
    have sessionIs : s = t.accept := by rw [atCounter, sessionsEq, selected]
    have counterOne : e'.backend.2.1.2 ≤ 1 := by rw [counterZero] at counter; exact counter
    have slotSome : (e'.backend.2.1.1 c).isSome = true := by
      rcases slotted with some | full
      · exact some
      · omega
    obtain ⟨j, jFound⟩ := Option.isSome_iff_exists.mp slotSome
    have jBelow := alloc.below inv.allocBelow c j jFound
    have jZero : j = 0 := Fin.ext (by omega)
    subst jZero
    refine ⟨sessionIs, jFound, fun found => ?_⟩
    rcases pendingFact (by rw [marked]; rfl) with ⟨_, same⟩ | ⟨token, replied, _⟩
    · rw [same] at found
      have below := pendingBelow s found
      omega
    · refine ⟨?_, fun response built => ?_⟩
      · have count : acceptCount transcript = t.accept := by rw [holds.accepts, selected]
        rw [← count, PqxdhDeploymentIdealTrace.sessionAt_accept, replied, atCounter]
      · have below := builds s response (builtIn_accept transcript raw reply s response built)
        omega
  · obtain ⟨atCounter, _⟩ := marks s c marked
    have below := builds s response (builtIn_accept transcript raw reply s response built)
    omega
  · rw [peer, peerNone] at found; cases found

/-- The marked build of the marked session with its pending token, which consumes the token, changes only the Server install ghost of the backend (to the published peer at the marked coordinates when it returns a response, and not otherwise), and changes the annotation only at the ghost's key ID, keeps the provenance invariant. -/
theorem prov_markedBuild (transcript : List Entry) (e e' : EnvState KemSK SplitBk)
    (w w' : PqxdhRecordLiftWorld.State 2) (o o' : Origins 2) (session : ℕ) (coords : PqxdhDeploymentIdealSlots.Coord)
    (payload : Option Pqxdh.Bytes) (reply : Option PqxdhServerRegistrationPublication.Response)
    (holds : Prov t transcript e w o) (inv : PqxdhDeploymentIdealEnv.IdealInv t e w) (ann : AnnInv w' o')
    (marked : e.backend.2.2.marks = some (session, coords))
    (tokened : (e.native.shared.2.pending session).isSome = true)
    (alloc : e'.backend.2.1 = e.backend.2.1)
    (core : e'.backend.2.2 = { e.backend.2.2 with peer := e'.backend.2.2.peer })
    (consumed : e'.native.shared.2.pending session = none)
    (published : (reply = none ∧ e'.backend.2.2.peer = e.backend.2.2.peer) ∨
      ∃ response, reply = some response ∧ e'.backend.2.2.peer = some (response.keyId, coords))
    (owners : o'.owners = o.owners)
    (peers : ∀ keyId, o'.peers keyId ≠ o.peers keyId → e'.backend.2.2.peer = some (keyId, coords)) :
    Prov t (transcript ++ [⟨.inl (.inr (.build session payload)), reply⟩]) e' w' o' := by
  have peerNone := inv.pendingPeer session coords marked tokened
  obtain ⟨selected, slot, open_⟩ := holds.marked session coords marked
  obtain ⟨returned, unbuilt⟩ := open_ tokened
  have marks' : e'.backend.2.2.marks = some (session, coords) := by rw [core]; exact marked
  have accepts' : e'.backend.2.2.accepts = e.backend.2.2.accepts := by rw [core]
  have notAccept : ∀ raw reply', (⟨.inl (.inr (.build session payload)), reply⟩ : Entry) ≠
      ⟨.inl (.inr (.accept raw)), reply'⟩ := fun raw reply' same => by
    simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same
  have entryBuilt : ∀ s response, BuiltIn (transcript ++ [⟨.inl (.inr (.build session payload)), reply⟩]) s response →
      BuiltIn transcript s response ∨ (s = session ∧ reply = some response) := by
    intro s response built
    rcases builtIn_append transcript _ s response built with old | ⟨payload', same⟩
    · exact Or.inl old
    · simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
        PqxdhDeploymentInterface.Command.build.injEq] at same
      obtain ⟨⟨rfl, -⟩, same⟩ := same
      exact Or.inr ⟨rfl, eq_of_heq same⟩
  have late : ¬ e.backend.2.2.accepts ≤ t.accept := fun before => by
    rw [(inv.before before).1] at marked; cases marked
  refine ⟨ann, fun keyId j found => ?_, fun owner j found => holds.ownerKey owner j (by rw [← owners]; exact found),
    ?_, fun before => absurd (by rw [← accepts']; exact before) late, fun s c marked'' => ?_,
    fun s c response marked'' built => ?_, fun keyId c found => ?_⟩
  · by_cases changed : o'.peers keyId = o.peers keyId
    · rw [changed] at found
      obtain ⟨c, peer⟩ := holds.peerKey keyId j found
      rw [peerNone] at peer; cases peer
    · exact ⟨coords, peers keyId changed⟩
  · rw [PqxdhDeploymentIdealTrace.acceptCount_other transcript _ (fun raw reply' => notAccept raw reply'), accepts']
    exact holds.accepts
  · rw [marks'] at marked''
    simp only [Option.some.injEq, Prod.mk.injEq] at marked''
    obtain ⟨rfl, rfl⟩ := marked''
    refine ⟨selected, by rw [alloc]; exact slot, fun found => ?_⟩
    rw [consumed] at found; cases found
  · rw [marks'] at marked''
    simp only [Option.some.injEq, Prod.mk.injEq] at marked''
    obtain ⟨rfl, rfl⟩ := marked''
    rcases entryBuilt _ response built with old | ⟨-, replied⟩
    · exact absurd old (unbuilt response)
    · rcases published with ⟨none, -⟩ | ⟨response', replied', peer⟩
      · rw [replied] at none; cases none
      · rw [replied] at replied'
        cases replied'
        exact peer
  · rcases published with ⟨-, same⟩ | ⟨response, replied, peer⟩
    · rw [same, peerNone] at found; cases found
    · rw [peer] at found
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, -⟩ := found
      unfold peerOf
      rw [sessionAt_keep transcript _ t.accept session returned, Option.bind_some, replied,
        PqxdhDeploymentIdealTrace.buildOf_build transcript session payload response
          (buildOf_none transcript session unbuilt), Option.map_some]

open PqxdhDeploymentIdealEnvFacts (AllocMove) in
/-- Owner k's challenge finish after an active selected accept, which keeps the pending tokens, moves the allocator, changes only the Beacon install ghost of the backend and changes the annotation only at owner `k`, keeps the provenance invariant. -/
theorem prov_challenge (transcript : List Entry) (e e' : EnvState KemSK SplitBk)
    (w w' : PqxdhRecordLiftWorld.State 2) (o o' : Origins 2) (owner : ℕ) (raw : Pqxdh.Bytes)
    (reply : Option Pqxdh.Bytes) (holds : Prov t transcript e w o) (inv : PqxdhDeploymentIdealEnv.IdealInv t e w)
    (ann : AnnInv w' o') (active : e.backend.2.2.active = true)
    (pending : e'.native.shared.2.pending = e.native.shared.2.pending)
    (alloc : AllocMove e.backend.2.1 e'.backend.2.1)
    (core : e'.backend.2.2 = { e.backend.2.2 with beacon := e'.backend.2.2.beacon })
    (origins : PqxdhDeploymentIdealOrigins.OwnerRel t.kem.val o o') :
    Prov t (transcript ++ [⟨.inl (.inr (.finish owner raw)), reply⟩]) e' w' o' := by
  have notAccept : ∀ raw' reply', (⟨.inl (.inr (.finish owner raw)), reply⟩ : Entry) ≠
      ⟨.inl (.inr (.accept raw')), reply'⟩ := fun raw' reply' same => by
    simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same
  have notBuild : ∀ s payload reply', (⟨.inl (.inr (.finish owner raw)), reply⟩ : Entry) ≠
      ⟨.inl (.inr (.build s payload)), reply'⟩ := fun s payload reply' same => by
    simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same
  have builtOld : ∀ s response, BuiltIn (transcript ++ [⟨.inl (.inr (.finish owner raw)), reply⟩]) s response →
      BuiltIn transcript s response := by
    intro s response built
    rcases builtIn_append transcript _ s response built with old | ⟨payload, same⟩
    · exact old
    · exact absurd same (notBuild s payload _)
  have late : ¬ e.backend.2.2.accepts ≤ t.accept := fun before => by
    rw [(inv.before before).2.1] at active; cases active
  have marks' : e'.backend.2.2.marks = e.backend.2.2.marks := by rw [core]
  have peer' : e'.backend.2.2.peer = e.backend.2.2.peer := by rw [core]
  have accepts' : e'.backend.2.2.accepts = e.backend.2.2.accepts := by rw [core]
  refine ⟨ann, fun keyId j found => ?_, fun index j found => ?_, ?_,
    fun before => absurd (by rw [← accepts']; exact before) late, fun s c marked => ?_,
    fun s c response marked built => ?_, fun keyId c found => ?_⟩
  · rw [origins.1] at found
    rw [peer']
    exact holds.peerKey keyId j found
  · by_cases same : index = t.kem.val
    · exact same
    · rw [origins.2 index same] at found
      exact holds.ownerKey index j found
  · rw [PqxdhDeploymentIdealTrace.acceptCount_other transcript _ (fun raw' reply' => notAccept raw' reply'), accepts']
    exact holds.accepts
  · rw [marks'] at marked
    obtain ⟨selected, slot, open_⟩ := holds.marked s c marked
    refine ⟨selected, alloc.keeps c 0 slot, fun found => ?_⟩
    rw [pending] at found
    obtain ⟨returned, unbuilt⟩ := open_ found
    exact ⟨sessionAt_keep transcript _ t.accept s returned, fun response built => unbuilt response (builtOld s response built)⟩
  · rw [marks'] at marked
    rw [peer']
    exact holds.built s c response marked (builtOld s response built)
  · rw [peer'] at found
    exact peerOf_keep t transcript _ keyId (holds.peerOf keyId c found)

end Moves

/-! ### Hidden installs of the ideal environment's commands -/

section Programs
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealOrigins (hiddenEffect beaconAt)
open PqxdhRecordLiftInterface (EnvEffects effectKind)

/-- At two slots, the hidden install request of the annotation tools is that of `PqxdhDeploymentIdealEnvFacts`. -/
theorem hiddenEffect_two : (hiddenEffect (n := 2)) = PqxdhDeploymentIdealEnvFacts.isHidden := by
  funext query
  rcases query with coin | capability
  · rfl
  · cases capability with
    | installServer _ _ ref => cases ref <;> rfl
    | installBeacon _ _ ref => cases ref <;> rfl
    | _ => rfl

/-- A program without a hidden install has no hidden install other than a Beacon install at an owner. -/
theorem owner_of_free {α : Type} (owner : ℕ) (work : OracleComp (EnvEffects 2) α)
    (free : work.IsQueryBoundP (fun query => PqxdhDeploymentIdealEnvFacts.isHidden query = true) 0) :
    work.IsQueryBoundP (fun query => hiddenEffect query = true ∧ beaconAt owner query = false) 0 :=
  IsQueryBoundP.of_imp (fun query bad => by rw [hiddenEffect_two] at bad; exact bad.1) free

/-- A program without an administrative effect has no hidden install other than a Beacon install at an owner. -/
theorem owner_of_noAdmin {α : Type} (owner : ℕ) (work : OracleComp (EnvEffects 2) α)
    (noAdmin : work.IsQueryBoundP (fun effect => effectKind effect = .administrative) 0) :
    work.IsQueryBoundP (fun query => hiddenEffect query = true ∧ beaconAt owner query = false) 0 :=
  owner_of_free owner work (PqxdhDeploymentIdealEnvFacts.hiddenFree_of_noAdmin work noAdmin)

/-- The hidden owner effect at an owner issues only that owner's Beacon install or an advance. -/
theorem hiddenOwnerEffect_owner (j : PqxdhRecordLiftInterface.Slot 2) (owner : ℕ)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) :
    (PqxdhDeploymentEnvironment.hiddenOwnerEffect (n := 2) j owner before after).IsQueryBoundP
      (fun query => hiddenEffect query = true ∧ beaconAt owner query = false) 0 := by
  unfold PqxdhDeploymentEnvironment.hiddenOwnerEffect
  split
  · trivial
  · unfold PqxdhDeploymentEnvironment.issue PqxdhDeploymentEnvironment.request
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl fun bad => by simp [beaconAt] at bad, fun _ => trivial⟩
  · split
    · split
      · trivial
      · unfold PqxdhDeploymentEnvironment.issue PqxdhDeploymentEnvironment.request
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl fun bad => by simp [hiddenEffect] at bad, fun _ => trivial⟩
    · trivial

/-- The source commit of a finish issues no hidden install. -/
theorem commitEnv_owner (e : EnvState KemSK SplitBk) (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (shared : PqxdhServerAuthNative.NativeState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (PqxdhDeploymentIdealEnvFinish.commitEnv e owner control before shared staged).IsQueryBoundP
      (fun query => hiddenEffect query = true ∧ beaconAt owner query = false) 0 := by
  unfold PqxdhDeploymentIdealEnvFinish.commitEnv
  rw [show (0 : ℕ) = 0 + 0 from rfl]
  exact isQueryBoundP_bind (owner_of_free owner _ (PqxdhDeploymentIdealEnvFacts.ownerEffect_free owner before _))
    fun _ _ => trivial

/-- Owner k's challenge finish issues no hidden install other than the finished owner's Beacon install. -/
theorem finishChallenge_owner (p : Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) :
    ((PqxdhDeploymentIdealEnvFinish.finishChallengeEnv setup codec p owner raw).run e).IsQueryBoundP
      (fun query => hiddenEffect query = true ∧ beaconAt owner query = false) 0 := by
  unfold PqxdhDeploymentIdealEnvFinish.finishChallengeEnv
  simp only [StateT.run]
  split
  · rename_i before _
    split
    · rename_i control prekey oneTime kem _
      rw [show (0 : ℕ) = 0 + 0 from rfl]
      refine isQueryBoundP_bind (owner_of_noAdmin owner _ (PqxdhDeploymentEnvironmentReal.coins_noAdmin _))
        fun prepared _ => ?_
      split
      · exact commitEnv_owner e owner control before _ none
      · unfold PqxdhDeploymentIdealEnvFinish.groupEnv
        split
        · split
          · rw [show (0 : ℕ) = 0 + 0 from rfl]
            refine isQueryBoundP_bind (owner_of_noAdmin owner _ (PqxdhDeploymentEnvironmentReal.coins_noAdmin _))
              fun read _ => ?_
            split
            · rename_i j _
              rw [isQueryBoundP_map_iff]
              unfold PqxdhDeploymentEnvironment.finishSplitEnv
              rw [show (0 : ℕ) = 0 + 0 from rfl]
              refine isQueryBoundP_bind (owner_of_noAdmin owner _
                (PqxdhDeploymentIdealEnvFinish.finishSplitFwd_noAdmin setup codec _ _)) fun staged _ => ?_
              rw [show (0 : ℕ) = 0 + 0 from rfl]
              exact isQueryBoundP_bind (hiddenOwnerEffect_owner j owner before _) fun _ _ => trivial
            · exact commitEnv_owner e owner control before _ none
          · exact commitEnv_owner e owner control before _ none
        · rw [show (0 : ℕ) = 0 + 0 from rfl]
          refine isQueryBoundP_bind (owner_of_noAdmin owner _ (PqxdhDeploymentEnvironmentReal.coins_noAdmin _))
            fun r _ => ?_
          split
          · exact commitEnv_owner e owner control before _ none
          · rw [show (0 : ℕ) = 0 + 0 from rfl]
            exact isQueryBoundP_bind (owner_of_noAdmin owner _
              (PqxdhDeploymentIdealEnvFinish.knownFwd_noAdmin setup codec _)) fun staged _ =>
                commitEnv_owner e owner control before _ staged
    all_goals trivial
  · trivial

/-- The marked build reading the cached material, at an allocated slot with a pending token and a cached material: the forwarded split build, then the hidden install of the settled build, then the built environment state. -/
theorem buildCached_program (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : PqxdhDeploymentIdealSlots.Coord)
    (e : EnvState KemSK SplitBk) (j : PqxdhRecordLiftInterface.Slot 2) (token : PqxdhServerRelatedRootConsumer.Returned)
    (material : PqxdhDeploymentHiddenLayout.Material) (allocated : e.backend.2.1.1 coords = some j)
    (pending : e.native.shared.2.pending session = some token) (cached : e.backend.1 j = some material) :
    (PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e =
      (PqxdhDeploymentEnvironment.buildSplitFwd (n := 2) setup codec checks material token payload
        e.native.shared.2.server).run [] >>= fun value =>
        PqxdhDeploymentEnvironment.hiddenServerEffect j
          (PqxdhServerAuthExperiment.settle e.native.shared.2.server value.1) >>= fun _ =>
            pure ((PqxdhServerAuthExperiment.settle e.native.shared.2.server value.1).1,
              PqxdhDeploymentIdealEnvBuild.builtEnv e session coords e.backend.1
                (PqxdhServerAuthExperiment.settle e.native.shared.2.server value.1, value.2)) := by
  change (match e.backend.2.1.1 coords, e.native.shared.2.pending session with
    | some j, some token => _
    | _, _ => _) = _
  rw [allocated, pending]
  change (match e.backend.1 j with
    | some material => _
    | none => _) = _
  rw [cached]
  simp only [PqxdhDeploymentEnvironment.buildSplitEnv, StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc,
    pure_bind]

/-- The marked build in the provenance-annotated World, at an allocated slot with a pending token and a cached material: the annotation invariant is kept, the Beacon origins are kept, and a Server origin changes only at the key ID of the Server install ghost set at the marked coordinates. -/
theorem buildCached_origins (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : PqxdhDeploymentIdealSlots.Coord)
    (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2) (holds : AnnInv w o)
    (j : PqxdhRecordLiftInterface.Slot 2) (token : PqxdhServerRelatedRootConsumer.Returned)
    (material : PqxdhDeploymentHiddenLayout.Material) (allocated : e.backend.2.1.1 coords = some j)
    (pending : e.native.shared.2.pending session = some token) (cached : e.backend.1 j = some material) :
    ∀ result ∈ support ((simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup codec route)
        ((PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e)).run (w, o)),
      AnnInv result.2.1 result.2.2 ∧ result.2.2.owners = o.owners ∧
        ∀ keyId, result.2.2.peers keyId ≠ o.peers keyId → result.1.2.backend.2.2.peer = some (keyId, coords) := by
  intro result member
  rw [buildCached_program setup codec checks session payload coords e j token material allocated pending cached,
    simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨value, valueMember, member⟩ := member
  have free : ((PqxdhDeploymentEnvironment.buildSplitFwd (n := 2) setup codec checks material token payload
      e.native.shared.2.server).run []).IsQueryBoundP (fun query => hiddenEffect query = true) 0 := by
    rw [hiddenEffect_two]
    exact PqxdhDeploymentIdealEnvFacts.hiddenFree_of_noAdmin _
      (PqxdhDeploymentIdealEnvBuild.buildSplitFwd_noAdmin setup codec checks material token payload _ [])
  obtain ⟨valueHolds, valueSame⟩ := PqxdhDeploymentIdealOrigins.aRun_free setup codec route _ free w o holds value
    valueMember
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨effected, effectedMember, member⟩ := member
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
  subst member
  dsimp only
  rw [← valueSame]
  unfold PqxdhDeploymentEnvironment.hiddenServerEffect at effectedMember
  split at effectedMember
  · rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at effectedMember
    subst effectedMember
    exact ⟨valueHolds, rfl, fun keyId changed => absurd rfl changed⟩
  · rename_i response found
    split at effectedMember
    · rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at effectedMember
      subst effectedMember
      exact ⟨valueHolds, rfl, fun keyId changed => absurd rfl changed⟩
    · rename_i peer present
      unfold PqxdhDeploymentEnvironment.issue PqxdhDeploymentEnvironment.request at effectedMember
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at effectedMember
      obtain ⟨installed, installedMember, effectedMember⟩ := effectedMember
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at effectedMember
      subst effectedMember
      rw [simulateQ_spec_query] at installedMember
      have keeps := (PqxdhDeploymentIdealOrigins.aEffects_keeps setup codec route
        (.inr (.installServer response.keyId peer.identity (.hidden j))) value.2.1 value.2.2 valueHolds
        installed installedMember).1
      rw [PqxdhDeploymentIdealOrigins.aEffects_run, support_map] at installedMember
      obtain ⟨inner, _, rfl⟩ := installedMember
      refine ⟨keeps, ?_, fun keyId changed => ?_⟩
      · dsimp only
        simp only [PqxdhRecordLiftOrigins.annotate]
        split <;> rfl
      · dsimp only at changed
        simp only [PqxdhRecordLiftOrigins.annotate] at changed
        split at changed
        · by_cases same : keyId = response.keyId
          · subst same
            simp only [PqxdhDeploymentIdealEnvBuild.builtEnv, PqxdhDeploymentIdealSteps.publishedKey, found, present,
              Option.map_some, Option.some_or]
          · simp [Function.update_of_ne same] at changed
        · exact absurd rfl changed

/-- An outcome of an annotated run of an environment program, with its annotation erased, is an outcome of its World run. -/
theorem erase_member {α : Type} (work : OracleComp (EnvEffects 2) α) (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2)
    (result : α × PqxdhRecordLiftOrigins.State 2)
    (member : result ∈ support ((simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup codec route) work).run (w, o))) :
    (result.1, result.2.1) ∈ support ((simulateQ PqxdhRecordLiftWorld.effects work).run w) := by
  rw [← PqxdhDeploymentIdealOrigins.aEffects_erase setup codec route work (w, o), support_map]
  exact ⟨result, member, rfl⟩

open PqxdhDeploymentEnvironmentJoin (Good uncount) in
/-- The marked build reading the cached material, run by the World from an admissible state at an allocated slot with a pending token, a cached material and an unused Server marker: the allocator and every ideal backend field but the Server install ghost are kept, the session's token is consumed, and either it returns nothing and keeps the ghost, or it returns a response and the ghost is the response's key ID at the marked coordinates. -/
theorem buildCached_reply (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (coords : PqxdhDeploymentIdealSlots.Coord) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w) (j : PqxdhRecordLiftInterface.Slot 2)
    (token : PqxdhServerRelatedRootConsumer.Returned) (material : PqxdhDeploymentHiddenLayout.Material)
    (allocated : e.backend.2.1.1 coords = some j) (pending : e.native.shared.2.pending session = some token)
    (cached : e.backend.1 j = some material) (unused : w.used j .server = false) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e)).run w),
      result.1.2.backend.2.1 = e.backend.2.1 ∧
        result.1.2.backend.2.2 = { e.backend.2.2 with peer := result.1.2.backend.2.2.peer } ∧
        result.1.2.native.shared.2.pending session = none ∧
        ((result.1.1 = none ∧ result.1.2.backend.2.2.peer = e.backend.2.2.peer) ∨
          ∃ response, result.1.1 = some response ∧ result.1.2.backend.2.2.peer = some (response.keyId, coords)) := by
  intro result member
  rw [PqxdhDeploymentIdealEnv.buildCached_hit setup codec checks session payload coords e j material allocated cached]
    at member
  obtain ⟨world, found, _⟩ := good.server
  have mapped : (result.1, uncount result.2) ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
      ((PqxdhDeploymentIdealEnvBuild.buildHiddenEnv setup codec checks session payload coords).run e)).run w) := by
    rw [support_map]
    exact ⟨result, member, rfl⟩
  obtain ⟨cache, log, _, ⟨replyNone, envEq, _⟩ | ⟨response, candidate, _, _, keyEq, _, _, _, _, replied, envEq, _⟩⟩ :=
    PqxdhDeploymentIdealEnvFacts.buildHidden_exact setup codec checks created session payload coords e w good j token
      allocated pending unused world found _ mapped
  · dsimp only at replyNone envEq
    rw [envEq]
    refine ⟨rfl, rfl, (PqxdhDeploymentIdealEnvFacts.builtEnv_move e session coords cache _).2, Or.inl ⟨replyNone, ?_⟩⟩
    simp [PqxdhDeploymentIdealEnvBuild.builtEnv, PqxdhDeploymentIdealSteps.publishedKey]
  · dsimp only at replied envEq
    rw [envEq]
    have peerAt := (PqxdhServerRegistrationPublication.publish_fields e.native.shared.2.server candidate
      PqxdhDeploymentHiddenSplit.placeholderKernel ()).1
    refine ⟨rfl, rfl, (PqxdhDeploymentIdealEnvFacts.builtEnv_move e session coords cache _).2,
      Or.inr ⟨response, replied, ?_⟩⟩
    simp [PqxdhDeploymentIdealEnvBuild.builtEnv, PqxdhDeploymentIdealSteps.publishedKey, keyEq, peerAt]

/-- Every registration command of the ideal step, interpreted by the provenance-annotated World from an admissible joint state, keeps the provenance invariant with its entry appended (the obligation `rStep` of `PqxdhDeploymentIdealOrigins.run_keeps_origins`). -/
theorem ideal_rStep (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (transcript : List Entry) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2) (good : PqxdhDeploymentEnvironmentJoin.Good created e w)
    (inv : PqxdhDeploymentIdealEnv.IdealInv t e w) (holds : Prov t transcript e w o) :
    ∀ result ∈ support ((simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup codec route)
        ((PqxdhDeploymentIdealEnv.idealStep setup codec checks t p query).run e)).run (w, o)),
      Prov t (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2 result.2.1 result.2.2 := by
  intro result member
  have realFree : ∀ (query' : PqxdhRecordLiftInterface.EnvQuery) (e' : EnvState KemSK SplitBk),
      ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks query').run e').IsQueryBoundP
        (fun effect => hiddenEffect effect = true) 0 := fun query' e' => by
    rw [hiddenEffect_two]; exact PqxdhDeploymentIdealEnvFacts.realStep_free setup codec checks query' e'
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      change result ∈ support ((simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup codec route)
        ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := 2) setup (p.pool t) pin keyId).run e)).run (w, o)) at member
      have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
      obtain ⟨sessions, pending⟩ := PqxdhDeploymentIdealSessions.createPool_game setup (p.pool t) pin keyId e _ value
      have backend := (PqxdhDeploymentIdealEnvFacts.createPool_move setup t.kem.val (p.pool t) pin keyId e _ value).backend
      obtain ⟨ann, same⟩ := PqxdhDeploymentIdealOrigins.aRun_free setup codec route _
        (by rw [hiddenEffect_two]; exact PqxdhDeploymentIdealEnvFacts.createPool_free setup (p.pool t) pin keyId e)
        w o holds.ann result member
      rw [same] at ann ⊢
      exact prov_realQuiet t transcript e _ w _ o _ holds ann backend sessions pending
        (fun _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
        (fun _ _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
  | bundle owner =>
      change result ∈ support ((simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup codec route)
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.bundle owner, allowed⟩).run e)).run
          (w, o)) at member
      have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
      obtain ⟨sessions, pending⟩ := PqxdhDeploymentIdealSessions.realStep_quiet setup codec checks _
        (fun _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong) e _ value
      have backend := (PqxdhDeploymentIdealEnvFacts.realStep_move setup codec checks t.kem.val _ e _ value).backend
      obtain ⟨ann, same⟩ := PqxdhDeploymentIdealOrigins.aRun_free setup codec route _ (realFree _ e) w o holds.ann
        result member
      rw [same] at ann ⊢
      exact prov_realQuiet t transcript e _ w _ o _ holds ann backend sessions pending
        (fun _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
        (fun _ _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
  | accept raw =>
      by_cases selected : e.backend.2.2.accepts = t.accept
      · rw [PqxdhDeploymentIdealEnv.idealStep_selected setup codec checks t p raw allowed e selected] at member
        have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
        obtain ⟨_, alloc, counter, marks, accepts, peer, _, _, _⟩ :=
          PqxdhDeploymentIdealEnvFacts.acceptSelected_move setup codec checks p raw e _ value
        have pendingFact := PqxdhDeploymentIdealSessions.acceptSelected_pending setup codec checks p raw e _ value
        obtain ⟨ann, same⟩ := PqxdhDeploymentIdealOrigins.aRun_free setup codec route _
          (by rw [hiddenEffect_two]; exact PqxdhDeploymentIdealEnvFacts.acceptSelected_free setup codec checks p raw e)
          w o holds.ann result member
        rw [same] at ann ⊢
        exact prov_selected t transcript e _ w _ o raw _ holds inv ann selected alloc counter
          (fun i c found => ⟨(marks i c found).1, (marks i c found).2.2⟩) accepts peer pendingFact
      · rw [PqxdhDeploymentIdealEnv.idealStep_accept_other setup codec checks t p raw allowed e selected] at member
        have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
        obtain ⟨sessions, pending⟩ := PqxdhDeploymentIdealSessions.realStep_accept setup codec checks raw _ _ value
        have backend := (PqxdhDeploymentIdealEnvFacts.realStep_move setup codec checks t.kem.val _ _ _ value).backend
        obtain ⟨ann, same⟩ := PqxdhDeploymentIdealOrigins.aRun_free setup codec route _ (realFree _ _) w o holds.ann
          result member
        rw [same] at ann ⊢
        exact prov_acceptOther t transcript e _ w _ o raw _ holds inv ann backend sessions pending
  | build session payload =>
      rcases PqxdhDeploymentIdealEnv.idealStep_build setup codec checks t p session payload allowed e with
        ⟨coords, marked, tokened, step⟩ | ⟨notMarked, step⟩
      · rw [step] at member
        obtain ⟨_, j, allocated, unused, cachedSome⟩ :=
          PqxdhDeploymentIdealEnv.idealInv_build_ready t e w inv session coords marked tokened
        obtain ⟨token, tokenFound⟩ := Option.isSome_iff_exists.mp tokened
        obtain ⟨material, cached⟩ := Option.isSome_iff_exists.mp cachedSome
        obtain ⟨ann, owners, peers⟩ := buildCached_origins setup codec route checks session payload coords e w o holds.ann
          j token material allocated tokenFound cached result member
        obtain ⟨alloc, core, consumed, published⟩ := buildCached_reply setup codec checks created session payload coords e w
          good j token material allocated tokenFound cached unused _ (erase_member setup codec route _ w o result member)
        exact prov_markedBuild t transcript e _ w _ o _ session coords payload _ holds inv ann marked tokened alloc core
          consumed published owners peers
      · rw [step] at member
        have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
        obtain ⟨sessions, pending, tokenedReply⟩ :=
          PqxdhDeploymentIdealSessions.realStep_build setup codec checks session payload e _ value
        have backend := (PqxdhDeploymentIdealEnvFacts.realStep_move setup codec checks t.kem.val _ e _ value).backend
        obtain ⟨ann, same⟩ := PqxdhDeploymentIdealOrigins.aRun_free setup codec route _ (realFree _ e) w o holds.ann
          result member
        rw [same] at ann ⊢
        refine prov_realBuild t transcript e _ w _ o session payload _ holds ann backend sessions pending tokenedReply
          fun c marked => ?_
        cases found : (e.native.shared.2.pending session).isSome
        · rfl
        · exact absurd ⟨rfl, found⟩ (notMarked session c marked)
  | finish owner raw =>
      by_cases chosen : e.backend.2.2.active = true ∧ owner = t.kem.val ∧
          PqxdhDeploymentIdealSteps.initSentAt e.native.owners owner = true
      · rw [PqxdhDeploymentIdealEnv.idealStep_challenge setup codec checks t p owner raw allowed e chosen] at member
        obtain ⟨active, rfl, initSent⟩ := chosen
        obtain ⟨ann, origins⟩ := PqxdhDeploymentIdealOrigins.aRun_owner setup codec route t.kem.val _
          (finishChallenge_owner setup codec p t.kem.val raw e) w o holds.ann result member
        obtain ⟨_, _, unused⟩ := PqxdhDeploymentIdealEnv.idealInv_finish_ready t e w inv initSent
        obtain ⟨_, pending, _, alloc, _, core, _, _⟩ := PqxdhDeploymentIdealEnvFacts.finishChallenge_move setup codec
          created p t.kem.val raw e w good initSent unused _ (erase_member setup codec route _ w o result member)
        exact prov_challenge t transcript e _ w _ o _ t.kem.val raw _ holds inv ann active pending alloc core origins
      · rw [PqxdhDeploymentIdealEnv.idealStep_finish_real setup codec checks t p owner raw allowed e chosen] at member
        have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
        obtain ⟨sessions, pending⟩ := PqxdhDeploymentIdealSessions.realStep_quiet setup codec checks _
          (fun _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong) e _ value
        have backend := (PqxdhDeploymentIdealEnvFacts.realStep_move setup codec checks t.kem.val _ e _ value).backend
        obtain ⟨ann, same⟩ := PqxdhDeploymentIdealOrigins.aRun_free setup codec route _ (realFree _ e) w o holds.ann
          result member
        rw [same] at ann ⊢
        exact prov_realQuiet t transcript e _ w _ o _ holds ann backend sessions pending
          (fun _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
          (fun _ _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
  | hmac key message =>
      change result ∈ support ((simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup codec route)
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.hmac key message, allowed⟩).run e)).run
          (w, o)) at member
      have value := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
      obtain ⟨sessions, pending⟩ := PqxdhDeploymentIdealSessions.realStep_quiet setup codec checks _
        (fun _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong) e _ value
      have backend := (PqxdhDeploymentIdealEnvFacts.realStep_move setup codec checks t.kem.val _ e _ value).backend
      obtain ⟨ann, same⟩ := PqxdhDeploymentIdealOrigins.aRun_free setup codec route _ (realFree _ e) w o holds.ann
        result member
      rw [same] at ann ⊢
      exact prov_realQuiet t transcript e _ w _ o _ holds ann backend sessions pending
        (fun _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
        (fun _ _ _ wrong => by simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at wrong)
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

end Programs

/-! ### Consequences at a state: the ghost annotation, L1 and L3 -/

section Consequences
variable {count : ℕ}

/-- The first successful build that returned a key ID is a successful build entry of its session with that key ID. -/
theorem linkOf_built (transcript : List Entry) (keyId : Std.U64) (session : ℕ)
    (response : PqxdhServerRegistrationPublication.Response)
    (linked : PqxdhDeploymentTranscript.linkOf transcript keyId = some (session, response)) :
    BuiltIn transcript session response ∧ response.keyId = keyId := by
  unfold PqxdhDeploymentTranscript.linkOf at linked
  obtain ⟨entry, member, found⟩ := List.exists_of_findSome?_eq_some linked
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · cases found
  · cases command with
    | build index payload =>
        rcases reply with _ | built
        · cases found
        · dsimp only at found
          split at found
          · rename_i same
            simp only [Option.some.injEq, Prod.mk.injEq] at found
            obtain ⟨rfl, rfl⟩ := found
            exact ⟨⟨payload, member⟩, same⟩
          · cases found
    | _ => cases found
  · cases found

/-- Under the provenance invariant and the ideal admissibility predicate, the provenance annotation is the slot map of the install ghosts (design-v2 section 7.2, item 4, `origins_ghost` at a state): a Server peer holds the slot allocated to the Server ghost's coordinates exactly at the ghost's key ID, owner `k` holds the slot allocated to the Beacon ghost's coordinates, and no other handle holds a slot. -/
theorem origins_eq_ghost (t : Target count) (transcript : List Entry) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2) (holds : Prov t transcript e w o)
    (inv : PqxdhDeploymentIdealEnv.IdealInv t e w) :
    o = PqxdhDeploymentIdealTrace.ghostOrigins t e.backend.2.1 e.backend.2.2 := by
  obtain ⟨⟨_, ⟨coveredServer, coveredBeacon⟩, ⟨markedServer, markedBeacon⟩⟩, peerKey, ownerKey, _⟩ := holds
  have peersEq : ∀ keyId, o.peers keyId = (PqxdhDeploymentIdealTrace.ghostOrigins t e.backend.2.1 e.backend.2.2).peers
      keyId := by
    intro keyId
    simp only [PqxdhDeploymentIdealTrace.ghostOrigins]
    rcases peer : e.backend.2.2.peer with _ | ⟨kid, c⟩
    · rcases found : o.peers keyId with _ | j
      · rfl
      · obtain ⟨c, wrong⟩ := peerKey keyId j found
        rw [peer] at wrong; cases wrong
    · dsimp only
      split
      · rename_i same
        subst same
        rcases found : o.peers keyId with _ | j
        · rcases slot : e.backend.2.1.1 c with _ | j
          · rfl
          · have used := (inv.serverMarks j).mpr ⟨keyId, c, peer, slot⟩
            obtain ⟨kid'', found''⟩ := coveredServer j used
            obtain ⟨c'', peer''⟩ := peerKey kid'' j found''
            rw [peer] at peer''
            simp only [Option.some.injEq, Prod.mk.injEq] at peer''
            obtain ⟨rfl, -⟩ := peer''
            rw [found] at found''; cases found''
        · have used := markedServer keyId j found
          obtain ⟨kid', c', peer', slot⟩ := (inv.serverMarks j).mp used
          rw [peer] at peer'
          simp only [Option.some.injEq, Prod.mk.injEq] at peer'
          obtain ⟨-, rfl⟩ := peer'
          exact slot.symm
      · rename_i other
        rcases found : o.peers keyId with _ | j
        · rfl
        · obtain ⟨c', wrong⟩ := peerKey keyId j found
          rw [peer] at wrong
          simp only [Option.some.injEq, Prod.mk.injEq] at wrong
          exact absurd wrong.1.symm other
  have ownersEq : ∀ index, o.owners index = (PqxdhDeploymentIdealTrace.ghostOrigins t e.backend.2.1
      e.backend.2.2).owners index := by
    intro index
    simp only [PqxdhDeploymentIdealTrace.ghostOrigins]
    split
    · rename_i same
      subst same
      rcases found : o.owners t.kem.val with _ | j
      · rcases beacon : e.backend.2.2.beacon with _ | c
        · rfl
        · rcases slot : e.backend.2.1.1 c with _ | j
          · simp [slot]
          · have used := (inv.beaconMarks j).mpr ⟨c, beacon, slot⟩
            obtain ⟨owner'', found''⟩ := coveredBeacon j used
            have same := ownerKey owner'' j found''
            subst same
            rw [found] at found''; cases found''
      · have used := markedBeacon t.kem.val j found
        obtain ⟨c, beacon, slot⟩ := (inv.beaconMarks j).mp used
        rw [beacon]
        exact slot.symm
    · rename_i other
      rcases found : o.owners index with _ | j
      · rfl
      · exact absurd (ownerKey index j found) other
  cases o
  simp only [PqxdhDeploymentIdealTrace.ghostOrigins, Origins.mk.injEq]
  exact ⟨funext peersEq, funext ownersEq⟩

/-- L1 of design-v2 section 7.2 at a state: the Server install ghost is at coordinates holding slot 0, and its key ID is the target's peer in the transcript. -/
theorem trace_peer (t : Target count) (transcript : List Entry) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2) (holds : Prov t transcript e w o)
    (inv : PqxdhDeploymentIdealEnv.IdealInv t e w) (keyId : Std.U64) (c : PqxdhDeploymentIdealSlots.Coord)
    (peer : e.backend.2.2.peer = some (keyId, c)) :
    e.backend.2.1.1 c = some 0 ∧ peerOf t transcript = some keyId := by
  obtain ⟨s, marked⟩ := inv.peerMarked keyId c peer
  exact ⟨(holds.marked s c marked).2.1, holds.peerOf keyId c peer⟩

variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- L3 of design-v2 section 7.2 at a state: under `Phase1ReadBack` and the key facts, a Server peer that designates the target is the Server install ghost's key ID. -/
theorem trace_designated (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (serverKid : Std.U64)
    (t : Target count) (p : Params KemSK count) (transcript : List Entry) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (o : Origins 2) (holds : Prov t transcript e w o)
    (facts : PqxdhDeploymentIdealTrace.KeyFacts setup codec checks t p transcript e.backend.2.2) (keyId : Std.U64)
    (designated : designate setup.source.crypto codec serverKid transcript (.peer keyId) = some (t.accept, t.kem.val)) :
    ∃ c, e.backend.2.2.peer = some (keyId, c) := by
  have marked := PqxdhDeploymentIdealTrace.keyFacts_marked setup codec checks phase1 serverKid t p transcript
    e.backend.2.2 facts (.peer keyId) designated
  obtain ⟨⟨s, c⟩, marks⟩ := Option.isSome_iff_exists.mp marked
  obtain ⟨response, _, _, _, linked, _⟩ := PqxdhDeploymentTranscript.designate_peer setup.source.crypto codec serverKid
    keyId transcript t.accept t.kem.val designated
  obtain ⟨built, keyEq⟩ := linkOf_built transcript keyId t.accept response linked
  have selected := (holds.marked s c marks).1
  subst selected
  refine ⟨c, ?_⟩
  rw [holds.built _ c response marks built, keyEq]

end Consequences

/-! ### The provenance invariant on every outcome of the annotated record world -/

section Outcomes
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentEnvironmentDraw (dropE withE paramStep paramInv)
open PqxdhDeploymentEnvironmentJoin (Good initialized)

/-- The provenance invariant holds at the startup: the empty transcript, the initial environment state of a constructed Server with the split form's initial backend, the initialized fresh World and the empty annotation. -/
theorem prov_initial (t : Target count) (created : PqxdhLiveServerConstruction.Created Unit) :
    Prov t [] (PqxdhDeploymentEnvironment.envInitial (KemSK := KemSK) created (PqxdhDeploymentIdealSteps.splitInit created))
      (initialized created (PqxdhRecordLiftWorld.initial (n := 2))) PqxdhRecordLiftOrigins.empty := by
  have emptyPeers : ∀ keyId j, (PqxdhRecordLiftOrigins.empty : Origins 2).peers keyId ≠ some j := fun _ _ found => by
    simp [PqxdhRecordLiftOrigins.empty] at found
  have emptyOwners : ∀ owner j, (PqxdhRecordLiftOrigins.empty : Origins 2).owners owner ≠ some j := fun _ _ found => by
    simp [PqxdhRecordLiftOrigins.empty] at found
  refine
    { ann := ⟨⟨fun keyId j found => absurd found (emptyPeers keyId j),
          fun owner j found => absurd found (emptyOwners owner j)⟩,
        ⟨fun _ used => by simp [initialized, PqxdhRecordLiftWorld.initial] at used,
          fun _ used => by simp [initialized, PqxdhRecordLiftWorld.initial] at used⟩,
        ⟨fun keyId j found => absurd found (emptyPeers keyId j), fun owner j found => absurd found (emptyOwners owner j)⟩⟩
      peerKey := fun keyId j found => absurd found (emptyPeers keyId j)
      ownerKey := fun owner j found => absurd found (emptyOwners owner j)
      accepts := rfl
      early := fun _ => ⟨rfl, fun s found => ?_, fun _ _ built => ?_⟩
      marked := fun _ _ marked => by simp [PqxdhDeploymentEnvironment.envInitial, PqxdhDeploymentIdealSteps.splitInit,
        IdealCore.initial] at marked
      built := fun _ _ _ marked => by simp [PqxdhDeploymentEnvironment.envInitial, PqxdhDeploymentIdealSteps.splitInit,
        IdealCore.initial] at marked
      peerOf := fun _ _ peer => by simp [PqxdhDeploymentEnvironment.envInitial, PqxdhDeploymentIdealSteps.splitInit,
        IdealCore.initial] at peer }
  · simp [PqxdhDeploymentEnvironment.envInitial, PqxdhDeploymentEnvironment.strip,
      PqxdhRegistrationSchedule.initial] at found
  · obtain ⟨_, member⟩ := built
    simp at member

/-- The provenance invariant on every outcome of the provenance-annotated record world with the ideal environment at fixed parameters (`envG`), together with `Good` and `IdealInv` (design-v2 section 7.2, items 1 and 4: `PqxdhDeploymentIdealOrigins.world_keeps_origins` with `ideal_rStep`). -/
theorem world_provG (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
        (PqxdhDeploymentIdealEnv.envG setup codec checks t p ensureInit identityIndex runtime) serverKid bounds mode
          adversary),
      ∀ value, result.1 = some value → ∃ created, Good created value.2.2 result.2.1 ∧
        PqxdhDeploymentIdealEnv.IdealInv t value.2.2 result.2.1 ∧
        Prov t value.2.1.2.transcript value.2.2 result.2.1 result.2.2 := by
  refine PqxdhDeploymentIdealOrigins.world_keeps_origins setup codec route _
    (fun created => PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)
    (PqxdhDeploymentIdealEnv.IdealInv t) (PqxdhDeploymentIdealEnv.idealInv_stable t)
    (fun created => PqxdhDeploymentIdealEnv.ideal_splits setup codec route checks t p created) (Prov t) (prov_view t)
    (prov_quiet t) (fun created query transcript e w o good inv holds =>
      ideal_rStep setup codec route checks t p created query transcript e w o good inv holds) ?_ serverKid bounds mode
    adversary
  intro created start started
  have initial := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime _ created start started
  subst initial
  exact ⟨_, rfl, PqxdhDeploymentIdealEnv.idealInv_start t created, prov_initial t created⟩

/-- The provenance invariant on every outcome of the provenance-annotated record world with the ideal environment of a target (`envGD`, the challenger's parameters drawn at startup), at the drawn parameters' environment state, together with `Good` and `IdealInv`. -/
theorem world_prov (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) serverKid bounds mode
          adversary),
      ∀ value, result.1 = some value → ∃ created, Good created value.2.2 result.2.1 ∧
        PqxdhDeploymentIdealEnv.IdealInv t (dropE value.2.2) result.2.1 ∧
        Prov t value.2.1.2.transcript (dropE value.2.2) result.2.1 result.2.2 := by
  refine PqxdhDeploymentIdealOrigins.world_keeps_origins setup codec route _
    (fun created => PqxdhDeploymentEnvironmentDraw.paramReg
      (fun p => PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created))
    (paramInv (fun _ => PqxdhDeploymentIdealEnv.IdealInv t))
    (PqxdhDeploymentEnvironmentDraw.stable_param _ (fun _ => PqxdhDeploymentIdealEnv.idealInv_stable t))
    (fun created => PqxdhDeploymentEnvironmentDraw.splits_param created _ _ _
      (fun p => PqxdhDeploymentIdealEnv.ideal_splits setup codec route checks t p created))
    (fun transcript e w o => Prov t transcript (dropE e) w o)
    (fun transcript e w w' o view holds => prov_view t transcript (dropE e) w w' o view holds)
    (fun transcript e w o entry quiet holds => prov_quiet t transcript (dropE e) w o entry quiet holds)
    (fun created query transcript e w o good inv holds result member => ?_) ?_ serverKid bounds mode adversary
  · change result ∈ support ((simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup codec route)
      (Prod.map id (withE e.backend.1) <$> (PqxdhDeploymentIdealEnv.idealStep setup codec checks t e.backend.1 query).run
        (dropE e))).run (w, o)) at member
    rw [simulateQ_map, StateT.run_map, support_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    exact ideal_rStep setup codec route checks t e.backend.1 created query transcript (dropE e) w o
      ((PqxdhDeploymentEnvironmentDraw.good_withE created e.backend.1 (dropE e) w).mp good) inv holds inner
      innerMember
  · intro created start started
    change some (created, start) ∈ support (PqxdhDeploymentIdealParams.drawParams setup count >>= fun p =>
      PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime
        (fun created => (p, PqxdhDeploymentIdealSteps.splitInit created))) at started
    rw [mem_support_bind_iff] at started
    obtain ⟨p, _, startedAt⟩ := started
    have initial := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime _ created start
      startedAt
    subst initial
    exact ⟨_, rfl, PqxdhDeploymentIdealEnv.idealInv_start t created, prov_initial t created⟩

/-- Every outcome of the record world is the erasure of an outcome of the provenance-annotated record world. -/
theorem annotated_cover {E : Type} (env : PqxdhRecordLiftInterface.Environment 2 E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode adversary),
      ∃ annotated ∈ support (PqxdhDeploymentIdealOrigins.annotatedRun setup codec route env serverKid bounds mode
        adversary), annotated.1 = result.1 ∧ annotated.2.1 = result.2 := by
  intro result member
  rw [← PqxdhDeploymentIdealOrigins.annotatedRun_erase, support_map] at member
  obtain ⟨annotated, annotatedMember, rfl⟩ := member
  exact ⟨annotated, annotatedMember, rfl, rfl⟩

/-- `origins_ghost` (design-v2 section 7.2, item 4): on every outcome of the provenance-annotated record world with the ideal environment of a target, the provenance annotation is the slot map of the final install ghosts (`PqxdhDeploymentIdealTrace.ghostOrigins`). -/
theorem origins_ghost (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) serverKid bounds mode
          adversary),
      ∀ value, result.1 = some value →
        result.2.2 = PqxdhDeploymentIdealTrace.ghostOrigins t value.2.2.backend.2.2.1 value.2.2.backend.2.2.2 := by
  intro result member value found
  obtain ⟨_, _, inv, holds⟩ := world_prov setup codec route checks t ensureInit identityIndex runtime serverKid bounds
    mode adversary result member value found
  exact origins_eq_ghost t _ _ _ _ holds inv

/-- `ideal_trace_world` (design-v2 section 7.2, item 3, L1 and L3): on every outcome of the record world with the ideal environment of a target, the Server install ghost is at coordinates holding slot 0 and its key ID is the target's peer in the transcript (L1), and, under `Phase1ReadBack`, every Server peer that designates the target is the Server install ghost's key ID (L3). -/
theorem ideal_trace_world (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary),
      ∀ value, result.1 = some value →
        (∀ keyId c, value.2.2.backend.2.2.2.peer = some (keyId, c) →
          value.2.2.backend.2.2.1.1 c = some 0 ∧ peerOf t value.2.1.2.transcript = some keyId) ∧
        ∀ keyId, designate setup.source.crypto codec setup.serverKeyId value.2.1.2.transcript (.peer keyId) =
            some (t.accept, t.kem.val) → ∃ c, value.2.2.backend.2.2.2.peer = some (keyId, c) := by
  intro result member value found
  obtain ⟨annotated, annotatedMember, sameValue, sameWorld⟩ := annotated_cover setup codec route _ setup.serverKeyId
    bounds mode adversary result member
  obtain ⟨_, _, inv, holds⟩ := world_prov setup codec route checks t ensureInit identityIndex runtime setup.serverKeyId
    bounds mode adversary annotated annotatedMember value (by rw [sameValue]; exact found)
  have facts := PqxdhDeploymentIdealTrace.world_keyFacts setup codec route checks t ensureInit identityIndex runtime
    bounds mode adversary result member value found
  exact ⟨fun keyId c peer => trace_peer t _ _ _ _ holds inv keyId c peer, fun keyId designated =>
    trace_designated setup codec checks phase1 setup.serverKeyId t _ _ _ _ _ holds facts keyId designated⟩

/-- `ideal_trace` (design-v2 section 7.2, item 2, L1 and L3) on the final split game's own support, for every parameter `p`: on every outcome of `gameWith .. splitInit (idealSplit t p)`, the Server install ghost is at coordinates holding slot 0 and its key ID is the target's peer in the transcript (L1), and, under `Phase1ReadBack`, every Server peer that designates the target is the Server install ghost's key ID (L3). Route: CE-11a's `join` at `envG t p` carries supports (`PqxdhDeploymentIdealFrame.lawEq_support`) from the record world with `envG t p`, where the provenance invariant holds (`world_provG` through `annotated_cover`); the key facts come from `PqxdhDeploymentIdealTrace.split_keyFacts`. -/
theorem ideal_trace (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (t : Target count)
    (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ outcome ∈ support ((PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
          adversary).run' runtime),
      ∀ value, outcome = some value →
        (∀ keyId c, value.2.2.2.backend.2.2.peer = some (keyId, c) →
          value.2.2.2.backend.2.1.1 c = some 0 ∧ peerOf t value.2.2.1.transcript = some keyId) ∧
        ∀ keyId, designate setup.source.crypto codec setup.serverKeyId value.2.2.1.transcript (.peer keyId) =
            some (t.accept, t.kem.val) → ∃ c, value.2.2.2.backend.2.2.peer = some (keyId, c) := by
  intro outcome member value found
  have full : ∃ full ∈ support ((PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
        adversary).run runtime), full.1 = some value := by
    rw [StateT.run'_eq, support_map] at member
    obtain ⟨full, fullMember, rfl⟩ := member
    exact ⟨full, fullMember, found⟩
  obtain ⟨full, fullMember, fullFound⟩ := full
  have facts := PqxdhDeploymentIdealTrace.split_keyFacts setup codec route checks t p ensureInit identityIndex bounds mode
    adversary runtime full fullMember value fullFound
  have law := PqxdhDeploymentEnvironmentJoin.join setup codec route PqxdhDeploymentIdealSteps.splitInit
    (fun created => PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)
    (PqxdhDeploymentIdealEnv.envG setup codec checks t p ensureInit identityIndex runtime) ensureInit identityIndex runtime
    rfl (PqxdhDeploymentIdealEnv.IdealInv t) (PqxdhDeploymentIdealEnv.idealInv_stable t)
    (fun created => PqxdhDeploymentIdealEnv.idealInv_start t created)
    (fun created => PqxdhDeploymentIdealEnv.ideal_splits setup codec route checks t p created) bounds mode adversary
  rw [PqxdhDeploymentIdealFrame.lawEq_support law, support_map] at member
  obtain ⟨result, resultMember, joinedEq⟩ := member
  rw [found] at joinedEq
  rcases resultFound : result.1 with _ | v
  · simp only [PqxdhDeploymentEnvironmentJoin.joined, resultFound, Option.map_none, reduceCtorEq] at joinedEq
  · simp only [PqxdhDeploymentEnvironmentJoin.joined, resultFound, Option.map_some, Option.some.injEq] at joinedEq
    subst joinedEq
    obtain ⟨annotated, annotatedMember, sameValue, sameWorld⟩ := annotated_cover setup codec route _ setup.serverKeyId
      bounds mode adversary result resultMember
    obtain ⟨_, _, inv, holds⟩ := world_provG setup codec route checks t p ensureInit identityIndex runtime
      setup.serverKeyId bounds mode adversary annotated annotatedMember v (by rw [sameValue]; exact resultFound)
    exact ⟨fun keyId c peer => trace_peer t _ _ _ _ holds inv keyId c peer, fun keyId designated =>
      trace_designated setup codec checks phase1 setup.serverKeyId t p _ _ _ _ holds facts keyId designated⟩

/-- Three of the four conjuncts of C5 restated (`PqxdhDeploymentIdealTrace.IdealSlots`, design-v2 section 7.2, item 5), on every outcome of the provenance-annotated record world with the ideal environment of a target: the Server restriction (a Server peer holding a slot holds slot 0 and is the target's peer), the Beacon restriction (an owner holding a slot is owner `k`) and, under `Phase1ReadBack`, the Server converse (a Server peer designating the target holds slot 0). The fourth conjunct, the Beacon converse with the anomaly as its alternative, is not proved here. -/
theorem ideal_slots_server (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary),
      ∀ value, result.1 = some value →
        (∀ keyId slot, PqxdhDeploymentIdealTrace.originSlots result.2.2 (.peer keyId) = some slot →
          slot = 0 ∧ peerOf t value.2.1.2.transcript = some keyId) ∧
        (∀ owner slot, PqxdhDeploymentIdealTrace.originSlots result.2.2 (.owner owner) = some slot →
          owner = t.kem.val) ∧
        ∀ keyId, designate setup.source.crypto codec setup.serverKeyId value.2.1.2.transcript (.peer keyId) =
            some (t.accept, t.kem.val) → PqxdhDeploymentIdealTrace.originSlots result.2.2 (.peer keyId) = some 0 := by
  intro result member value found
  obtain ⟨_, _, inv, holds⟩ := world_prov setup codec route checks t ensureInit identityIndex runtime setup.serverKeyId
    bounds mode adversary result member value found
  have ghost := origins_eq_ghost t _ _ _ _ holds inv
  have erased : (result.1, result.2.1) ∈ support (PqxdhRecordLiftWorld.run setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode
        adversary) := by
    rw [← PqxdhDeploymentIdealOrigins.annotatedRun_erase, support_map]
    exact ⟨result, member, rfl⟩
  have facts := PqxdhDeploymentIdealTrace.world_keyFacts setup codec route checks t ensureInit identityIndex runtime
    bounds mode adversary _ erased value found
  refine ⟨fun keyId slot slotted => ?_, fun owner slot slotted => holds.ownerKey owner slot slotted,
    fun keyId designated => ?_⟩
  · change result.2.2.peers keyId = some slot at slotted
    obtain ⟨c, peer⟩ := holds.peerKey keyId slot slotted
    obtain ⟨zero, named⟩ := trace_peer t _ _ _ _ holds inv keyId c peer
    rw [ghost] at slotted
    simp only [PqxdhDeploymentIdealTrace.ghostOrigins, peer, ite_true, zero, Option.some.injEq] at slotted
    exact ⟨slotted.symm, named⟩
  · obtain ⟨c, peer⟩ := trace_designated setup codec checks phase1 setup.serverKeyId t _ _ _ _ _ holds facts keyId
      designated
    obtain ⟨zero, _⟩ := trace_peer t _ _ _ _ holds inv keyId c peer
    change result.2.2.peers keyId = some 0
    rw [ghost]
    simp only [PqxdhDeploymentIdealTrace.ghostOrigins, peer, ite_true, zero]

end Outcomes

end BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.builtIn_append' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.builtIn_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.buildOf_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.buildOf_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.sessionAt_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.sessionAt_lt

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.sessionAt_keep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.sessionAt_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.peerOf_keep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.peerOf_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.quiet_kinds' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.quiet_kinds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_realQuiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_realQuiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_realBuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_realBuild

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.accept_notBuild' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.accept_notBuild

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.builtIn_accept' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.builtIn_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_acceptOther' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_acceptOther

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_markedBuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_markedBuild

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.hiddenEffect_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.hiddenEffect_two

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.owner_of_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.owner_of_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.owner_of_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.owner_of_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.hiddenOwnerEffect_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.hiddenOwnerEffect_owner

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.commitEnv_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.commitEnv_owner

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.finishChallenge_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.finishChallenge_owner

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.buildCached_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.buildCached_program

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.buildCached_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.buildCached_origins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.erase_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.erase_member

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.buildCached_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.buildCached_reply

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.ideal_rStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.ideal_rStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.linkOf_built' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.linkOf_built

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.origins_eq_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.origins_eq_ghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.trace_peer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.trace_peer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.trace_designated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.trace_designated

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.prov_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.world_provG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.world_provG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.world_prov' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.world_prov

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.annotated_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.annotated_cover

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.origins_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.origins_ghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.ideal_trace_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.ideal_trace_world

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.ideal_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.ideal_trace

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.ideal_slots_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance.ideal_slots_server
