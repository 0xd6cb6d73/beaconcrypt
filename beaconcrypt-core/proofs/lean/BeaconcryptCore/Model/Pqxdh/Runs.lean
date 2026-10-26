import BeaconcryptCore.Model.Pqxdh.Theorems

/-!
# BeaconCrypt modified PQXDH — the server over a whole sequence of registrations

The properties of `BeaconcryptCore.Model.Pqxdh.Theorems` describe one server step.
This file lifts them to a server that serves an arbitrary sequence of registration
bundles, which is where the specification's global claims live: identifiers are
never reused (spec §11), published peers are never lost or overwritten (spec §14),
and a beacon bundle is served at most once for the lifetime of the server
(spec §6, §20).

* `Pqxdh.ServerWf` — the invariant that makes key-identifier allocation safe: every
  published identifier is at most the allocation counter, and no identifier is
  published twice.
* `Pqxdh.ServerWf.serverRespond` — one registration preserves it, so it holds
  throughout a run (`Pqxdh.ServerWf.serverRun`).
* `Pqxdh.serverEmit_no_collision_of_wf` — under the invariant the collision check of
  spec §11 can only fire against state the server did not create itself: the freshly
  proposed identifier `n_S + 1` is always free.
* `Pqxdh.serverRespond_peers_preserved` / `Pqxdh.serverRun_peers_preserved` — a
  published peer stays published, unchanged, under the same identifier.
* `Pqxdh.serverRun_replay_of_consumed` and `Pqxdh.serverRun_served_at_most_once` — a
  bundle whose `RID` is already consumed is rejected as a replay every time it
  appears in the run, and consequently a bundle is served successfully at most once.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Pqxdh

/-! ## The allocation invariant (spec §11, §14) -/

/-- The server allocation invariant: every published key identifier is at most the
allocation counter, and no identifier is published twice. -/
structure ServerWf (S : ServerState) : Prop where
  /-- Every published identifier has already been allocated. -/
  bounded : ∀ p ∈ S.peers, p.1 ≤ S.n
  /-- No identifier is published twice. -/
  nodup : (S.peers.map Prod.fst).Nodup

/-- A server that has published nothing satisfies the invariant. -/
theorem serverWf_empty (ikSk : Bytes) (sid n : ℕ) (consumed : List Bytes) :
    ServerWf ⟨ikSk, sid, n, [], consumed⟩ := ⟨by simp, by simp⟩

/-- Under the invariant the next proposed identifier is free: the collision check of
spec §11 never fires on state the server itself produced. -/
theorem ServerWf.lookup_next {S : ServerState} (hwf : ServerWf S) :
    S.peers.lookup (S.n + 1) = none := by
  refine List.lookup_eq_none_iff.2 fun p hp => ?_
  have := hwf.bounded p hp
  simp only [bne_iff_ne, ne_eq]
  omega

/-- Consequently response construction never fails with `KeyIdCollision` on a server
satisfying the invariant, and it succeeds outright unless the counter is exhausted
(spec §11). -/
theorem serverEmit_no_collision_of_wf (c : Crypto) {S1 : ServerState}
    (ikB ds kemCt ePub app : Bytes) (hwf : ServerWf S1) (hn : S1.n ≠ maxKeyId) :
    ∃ r : KexResponse, (serverEmit c S1 ikB ds kemCt ePub app).1 = .ok r := by
  rw [serverEmit, if_neg hn, if_neg (by simp [hwf.lookup_next])]
  exact ⟨_, rfl⟩

/-- Response construction preserves the invariant. -/
theorem ServerWf.serverEmit (c : Crypto) {S1 : ServerState}
    (ikB ds kemCt ePub app : Bytes) (hwf : ServerWf S1) :
    ServerWf (Pqxdh.serverEmit c S1 ikB ds kemCt ePub app).2 := by
  rw [Pqxdh.serverEmit]
  split_ifs with h1 h2
  · exact hwf
  · exact hwf
  · refine ⟨?_, ?_⟩
    · rintro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Nat.le_refl _
      · exact Nat.le_trans (hwf.bounded p hp) (Nat.le_succ _)
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, hwf.nodup⟩
      simp only [List.mem_map, not_exists]
      rintro p ⟨hp, hpe⟩
      have := hwf.bounded p hp
      omega

/-- One registration preserves the invariant, whatever its outcome. -/
theorem ServerWf.serverRespond (c : Crypto) {S : ServerState} (m : InitKex)
    (eSk coins : Bytes) (app : Option Bytes) (hwf : ServerWf S) :
    ServerWf (Pqxdh.serverRespond c S m eSk coins app).2 := by
  rw [Pqxdh.serverRespond]
  split
  · exact hwf
  · split
    · exact hwf
    · split
      · exact hwf
      · split
        · exact hwf
        · split
          · exact ⟨hwf.bounded, hwf.nodup⟩
          · exact ServerWf.serverEmit c _ _ _ _ _ ⟨hwf.bounded, hwf.nodup⟩

/-! ## Published peers are never lost or overwritten (spec §14) -/

/-- The allocation counter never decreases. -/
theorem serverRespond_n_mono (c : Crypto) (S : ServerState) (m : InitKex)
    (eSk coins : Bytes) (app : Option Bytes) :
    S.n ≤ (serverRespond c S m eSk coins app).2.n := by
  rw [serverRespond]
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · split
        · exact Nat.le_refl _
        · split
          · exact Nat.le_refl _
          · rw [serverEmit]
            split_ifs <;> simp

/-- A peer published under some identifier is still published, unchanged, under that
identifier after another registration: the transactional commit of spec §14 only ever
extends the peer map. -/
theorem serverRespond_peers_preserved (c : Crypto) {S : ServerState} (m : InitKex)
    (eSk coins : Bytes) (app : Option Bytes) (hwf : ServerWf S) {k : ℕ} {p : Peer}
    (h : S.peers.lookup k = some p) :
    (serverRespond c S m eSk coins app).2.peers.lookup k = some p := by
  have hne : k ≠ S.n + 1 := by
    rintro rfl
    simp [hwf.lookup_next] at h
  rw [serverRespond]
  split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · split
        · exact h
        · split
          · exact h
          · rw [serverEmit]
            split_ifs
            · exact h
            · exact h
            · rw [List.lookup_cons, show (k == S.n + 1) = false from by simp [hne]]
              exact h

/-! ## Runs of the server -/

/-- One registration request: the bundle together with the randomness the server uses
to answer it and the optional initial application message. -/
structure Request where
  /-- The beacon's registration bundle. -/
  msg : InitKex
  /-- The server's X25519 ephemeral secret for this registration. -/
  eSk : Bytes
  /-- The server's ML-KEM encapsulation randomness for this registration. -/
  coins : Bytes
  /-- The optional initial application message. -/
  app : Option Bytes

/-- The server serving a sequence of registration requests, returning each bundle
paired with the outcome it received, and the final server state. -/
def serverRun (c : Crypto) (S : ServerState) :
    List Request → List (InitKex × Except ServerError KexResponse) × ServerState
  | [] => ([], S)
  | r :: rs =>
      let step := serverRespond c S r.msg r.eSk r.coins r.app
      let rest := serverRun c step.2 rs
      ((r.msg, step.1) :: rest.1, rest.2)

/-- The invariant holds throughout a run. -/
theorem ServerWf.serverRun (c : Crypto) {S : ServerState} (rs : List Request)
    (hwf : ServerWf S) : ServerWf (Pqxdh.serverRun c S rs).2 := by
  induction rs generalizing S with
  | nil => exact hwf
  | cons r rs ih => exact ih (ServerWf.serverRespond c r.msg r.eSk r.coins r.app hwf)

/-- The consumed-registration set only grows over a run. -/
theorem serverRun_consumed_mono (c : Crypto) (S : ServerState) (rs : List Request) :
    S.consumed ⊆ (serverRun c S rs).2.consumed := by
  induction rs generalizing S with
  | nil => exact List.Subset.refl _
  | cons r rs ih =>
      exact (serverRespond_consumed_mono c S r.msg r.eSk r.coins r.app).trans (ih _)

/-- The allocation counter never decreases over a run. -/
theorem serverRun_n_mono (c : Crypto) (S : ServerState) (rs : List Request) :
    S.n ≤ (serverRun c S rs).2.n := by
  induction rs generalizing S with
  | nil => exact Nat.le_refl _
  | cons r rs ih =>
      exact Nat.le_trans (serverRespond_n_mono c S r.msg r.eSk r.coins r.app) (ih _)

/-- A published peer survives an entire run, unchanged and under the same
identifier. -/
theorem serverRun_peers_preserved (c : Crypto) {S : ServerState} (rs : List Request)
    (hwf : ServerWf S) {k : ℕ} {p : Peer} (h : S.peers.lookup k = some p) :
    (serverRun c S rs).2.peers.lookup k = some p := by
  induction rs generalizing S with
  | nil => exact h
  | cons r rs ih =>
      exact ih (ServerWf.serverRespond c r.msg r.eSk r.coins r.app hwf)
        (serverRespond_peers_preserved c r.msg r.eSk r.coins r.app hwf h)

/-! ## One registration per beacon bundle (spec §6, §20) -/

/-- A successfully served bundle has had its registration identifier consumed. -/
theorem serverRespond_ok_consumes (c : Crypto) (S : ServerState) (m : InitKex)
    (eSk coins : Bytes) (app : Option Bytes) (v : ValidInit) (r : KexResponse)
    (hv : validateInit c m = some v) (h : (serverRespond c S m eSk coins app).1 = .ok r) :
    v.rid ∈ (serverRespond c S m eSk coins app).2.consumed := by
  by_cases hr : v.rid ∈ S.consumed
  · rw [serverRespond_replay c S m eSk coins app v hv hr]
    exact hr
  · exact serverRespond_consumes c S m eSk coins app v hv hr
      (by simp [h]) (by simp [h])

/-- Once a registration identifier has been consumed, every later occurrence of the
same bundle in the run is rejected as a registration replay. -/
theorem serverRun_replay_of_consumed (c : Crypto) {S : ServerState} (rs : List Request)
    {m : InitKex} {v : ValidInit} (hv : validateInit c m = some v)
    (hr : v.rid ∈ S.consumed) :
    ∀ p ∈ (serverRun c S rs).1, p.1 = m → p.2 = .error .registrationReplay := by
  induction rs generalizing S with
  | nil => simp [serverRun]
  | cons r rs ih =>
      intro p hp hpm
      simp only [serverRun, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp only at hpm
        subst hpm
        rw [serverRespond_replay c S r.msg r.eSk r.coins r.app v hv hr]
      · exact ih (S := (serverRespond c S r.msg r.eSk r.coins r.app).2)
          (serverRespond_consumed_mono c S r.msg r.eSk r.coins r.app hr) p hp hpm

/-- **A beacon bundle is served at most once.**  Over a whole run of the server, at
most one occurrence of a given bundle receives a response; every other occurrence is
rejected.  This is the one-shot registration guarantee of spec §6 and §20 in its
global form. -/
theorem serverRun_served_at_most_once (c : Crypto) (S : ServerState) (rs : List Request)
    {m : InitKex} {v : ValidInit} (hv : validateInit c m = some v) :
    ((serverRun c S rs).1.filter
      (fun p => decide (p.1 = m) && p.2.isOk)).length ≤ 1 := by
  induction rs generalizing S with
  | nil => simp [serverRun]
  | cons r rs ih =>
      by_cases hr : v.rid ∈ S.consumed
      · -- every occurrence of `m` in the whole run is a replay, so nothing is served
        have hall := serverRun_replay_of_consumed c (S := S) (r :: rs) hv hr
        have : ((serverRun c S (r :: rs)).1.filter
            (fun p => decide (p.1 = m) && p.2.isOk)) = [] := by
          refine List.filter_eq_nil_iff.2 fun p hp => ?_
          by_cases hpm : p.1 = m
          · rw [hall p hp hpm]
            simp [Except.isOk, Except.toBool]
          · simp [hpm]
        rw [this]
        simp
      · rcases hstep : (serverRespond c S r.msg r.eSk r.coins r.app).1 with e | resp
        · -- this request was rejected; the tail is handled by induction
          have : ((r.msg, (serverRespond c S r.msg r.eSk r.coins r.app).1) ::
              (serverRun c (serverRespond c S r.msg r.eSk r.coins r.app).2 rs).1).filter
              (fun p => decide (p.1 = m) && p.2.isOk)
              = (serverRun c (serverRespond c S r.msg r.eSk r.coins r.app).2 rs).1.filter
                (fun p => decide (p.1 = m) && p.2.isOk) := by
            rw [List.filter_cons]
            simp [hstep, Except.isOk, Except.toBool]
          simpa [serverRun, this] using ih (S := _)
        · by_cases hrm : r.msg = m
          · -- this request was served, so `RID` is now consumed and no later
            -- occurrence of `m` can be served
            subst hrm
            have hcons : v.rid ∈ (serverRespond c S r.msg r.eSk r.coins r.app).2.consumed :=
              serverRespond_ok_consumes c S r.msg r.eSk r.coins r.app v resp hv hstep
            have hall := serverRun_replay_of_consumed c
              (S := (serverRespond c S r.msg r.eSk r.coins r.app).2) rs hv hcons
            have htail : ((serverRun c (serverRespond c S r.msg r.eSk r.coins r.app).2 rs).1.filter
                (fun p => decide (p.1 = r.msg) && p.2.isOk)) = [] := by
              refine List.filter_eq_nil_iff.2 fun p hp => ?_
              by_cases hpm : p.1 = r.msg
              · rw [hall p hp hpm]
                simp [Except.isOk, Except.toBool]
              · simp [hpm]
            simp only [serverRun, List.filter_cons, htail]
            split <;> simp
          · have : ((r.msg, (serverRespond c S r.msg r.eSk r.coins r.app).1) ::
                (serverRun c (serverRespond c S r.msg r.eSk r.coins r.app).2 rs).1).filter
                (fun p => decide (p.1 = m) && p.2.isOk)
                = (serverRun c (serverRespond c S r.msg r.eSk r.coins r.app).2 rs).1.filter
                  (fun p => decide (p.1 = m) && p.2.isOk) := by
              rw [List.filter_cons]
              simp [hrm]
            simpa [serverRun, this] using ih (S := _)

/-! ## Runs of the beacon (spec §18, §20)

Registration is one-shot on the beacon side too: whatever sequence of responses a
beacon is fed, at most one of them can be accepted. -/

/-- A beacon processing a sequence of responses, returning each outcome together with
the final beacon state. -/
def beaconRun (c : Crypto) (s : BeaconState) :
    List KexResponse → List (Except BeaconError ℕ) × BeaconState
  | [] => ([], s)
  | r :: rs =>
      let step := beaconFinish c s r
      let rest := beaconRun c step.2 rs
      (step.1 :: rest.1, rest.2)

/-- Processing a response from `InitSent` never lands back in `InitSent`: the state
machine leaves the registration-pending state for good (spec §18). -/
theorem beaconFinish_result_not_initSent (c : Crypto) (b : ServerBinding)
    (ikSk preSk otSk kemSk : Bytes) (resp : KexResponse) (b' : ServerBinding)
    (ikSk' preSk' otSk' kemSk' : Bytes) :
    (beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp).2
      ≠ .initSent b' ikSk' preSk' otSk' kemSk' := by
  intro hc
  have hr := beaconFinish_drops_registration_keys c b ikSk preSk otSk kemSk resp
  rw [hc] at hr
  simp [BeaconState.regSecrets] at hr

/-- A beacon that is not in `InitSent` rejects every response it is given: neither
`Fresh`, nor `Established`, nor `Aborted` can accept a registration. -/
theorem beaconRun_all_error_of_not_initSent (c : Crypto) (s : BeaconState)
    (rs : List KexResponse)
    (h : ∀ b ikSk preSk otSk kemSk, s ≠ .initSent b ikSk preSk otSk kemSk) :
    ∀ o ∈ (beaconRun c s rs).1, o = .error .notInitSent := by
  induction rs generalizing s with
  | nil => simp [beaconRun]
  | cons r rs ih =>
      intro o ho
      rw [beaconRun, beaconFinish_not_initSent c s r h] at ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · rfl
      · exact ih s h o ho

/-- Consequently no response in the run is accepted. -/
theorem beaconRun_no_accept_of_not_initSent (c : Crypto) (s : BeaconState)
    (rs : List KexResponse)
    (h : ∀ b ikSk preSk otSk kemSk, s ≠ .initSent b ikSk preSk otSk kemSk) :
    (beaconRun c s rs).1.filter (fun o => o.isOk) = [] := by
  refine List.filter_eq_nil_iff.2 fun o ho => ?_
  rw [beaconRun_all_error_of_not_initSent c s rs h o ho]
  simp [Except.isOk, Except.toBool]

/-- **A beacon accepts at most one registration.**  However many responses it is fed,
at most one of them is accepted; this is the one-shot registration guarantee of
spec §18 and §20 on the beacon side. -/
theorem beaconRun_accepts_at_most_once (c : Crypto) (s : BeaconState)
    (rs : List KexResponse) :
    ((beaconRun c s rs).1.filter (fun o => o.isOk)).length ≤ 1 := by
  cases rs with
  | nil => simp [beaconRun]
  | cons r rs =>
      cases s with
      | fresh b ikSk preSk kemSk =>
          rw [beaconRun_no_accept_of_not_initSent c _ _ (by simp)]
          simp
      | freshWithCoins b ikSk preSk otSk kemSk =>
          rw [beaconRun_no_accept_of_not_initSent c _ _ (by simp)]
          simp
      | established b ikSk kid ad send recv =>
          rw [beaconRun_no_accept_of_not_initSent c _ _ (by simp)]
          simp
      | aborted =>
          rw [beaconRun_no_accept_of_not_initSent c _ _ (by simp)]
          simp
      | initSent b ikSk preSk otSk kemSk =>
          have htail := beaconRun_no_accept_of_not_initSent c
            (beaconFinish c (.initSent b ikSk preSk otSk kemSk) r).2 rs
            (fun b' ikSk' preSk' otSk' kemSk' =>
              beaconFinish_result_not_initSent c b ikSk preSk otSk kemSk r b' ikSk'
                preSk' otSk' kemSk')
          rw [beaconRun]
          simp only [List.filter_cons, htail]
          split <;> simp

end Pqxdh
