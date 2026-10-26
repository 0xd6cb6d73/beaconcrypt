import BeaconcryptCore.Computational.PqxdhServerAuthEntryBound

/-! Accepted-owner routing for observers stronger than the existing seal-origin event. This gate is a partition of actual accepted executions, not a security assumption. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (ScalarBytes PublicChallenge)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Actual acceptance, absence of the separately charged disclosure/collision events, and one exact first-touch owner. No seal-origin failure is required. -/
def Gate (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (j : Fin (Q + 1)) (ghost : Ghost) : Prop :=
  (∃ snap, ghost.acceptance = some snap) ∧ ¬ BadB setup seed scalar ghost ∧
    ¬ CollB setup seed scalar ghost ∧ entryOwner setup seed scalar Q ghost = some j

/-- Every reached selected input equals the accepted Beacon input under the actual source invariant and owner gate, including accepted executions that satisfy the old seal-origin theorem. -/
theorem selected_input (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (publicValue : PublicChallenge) (Q : Nat) (j : Fin (Q + 1)) (state : GameState KemSK)
    (invariant : GameInv Reader Response setup publicValue state)
    (accepted : Gate setup seed scalar Q j state.ghost) (bytes : Pqxdh.Bytes)
    (selected : SelectedAt setup seed scalar Q j state.ghost bytes) :
    beaconInput setup seed scalar state.ghost.touches = some bytes := by
  by_cases session : j.val < Q
  · obtain ⟨snap, found⟩ := accepted.1
    obtain ⟨before, beaconTouch, snapEq, clean⟩ := invariant.atomic snap found
    have partner := owner_session_ghost setup seed scalar Q state.ghost snap
      (invariant.frozen snap found).1 before beaconTouch snapEq clean j accepted.2.2.2 session
    obtain ⟨message, reply, touched, rooted⟩ :
        ∃ message reply, Touch.session j.val message reply ∈ state.ghost.touches ∧
          rootInput setup seed scalar message = some bytes := by
      simpa only [SelectedAt, session, ↓reduceIte] using selected
    obtain ⟨otherMessage, otherReply, otherBytes, otherTouched, otherRooted, beaconRooted⟩ := partner
    have same := (invariant.sessionOnce j.val message reply otherMessage otherReply touched
      ((invariant.frozen snap found).1.subset otherTouched)).1
    have sameBytes : otherBytes = bytes := Option.some.inj
      (otherRooted.symm.trans ((congrArg (rootInput setup seed scalar) same).symm.trans rooted))
    exact sameBytes ▸ beaconInput_prefix setup seed scalar _ _ otherBytes beaconRooted
      (invariant.frozen snap found).1
  · simpa only [SelectedAt, session, ↓reduceIte] using selected

/-- The actual accepted owner gate excludes both hidden-table refusals without assuming a failure of the older seal-origin property. -/
theorem no_refusal (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (publicValue : PublicChallenge) (Q : Nat) (j : Fin (Q + 1)) (state : GameState KemSK)
    (invariant : GameInv Reader Response setup publicValue state)
    (accepted : Gate setup seed scalar Q j state.ghost) :
    ¬ SelectedBad setup seed scalar Q j state.ghost := by
  rintro ⟨bytes, selected, refused⟩
  have beacon := selected_input setup seed scalar publicValue Q j state invariant accepted bytes selected
  have owned : ownerAt setup seed scalar Q bytes state.ghost.touches = some j := by
    have hit := accepted.2.2.2
    simp only [entryOwner, beacon] at hit
    unfold ownerAt
    split <;> simp_all
  exact refused.elim (fun wrong => wrong owned) (fun queried => accepted.2.1 ⟨bytes, beacon, queried⟩)

/-- Root replies are irrelevant to accepted-owner routing, including the frozen acceptance annotation. -/
theorem gate_erase (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (j : Fin (Q + 1)) (ghost : Ghost) :
    Gate setup seed scalar Q j (eraseGhost ghost) ↔ Gate setup seed scalar Q j ghost := by
  simp only [Gate, badB_erase, collB_erase, entryOwner_erase]
  cases found : ghost.acceptance <;> simp [eraseGhost, found]

/-- The complete source/hidden protocol relation preserves the accepted-owner gate without exposing marked roots to an observer. -/
theorem gate_related (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (j : Fin (Q + 1)) (root : RootOutput) (marks : Marks) (left right : GameState KemSK)
    (related : ProtocolRel root marks left right) :
    Gate setup seed scalar Q j left.ghost ↔ Gate setup seed scalar Q j right.ghost := by
  rw [← gate_erase setup seed scalar Q j left.ghost, related.ghost,
    gate_erase setup seed scalar Q j right.ghost]

/-- Every actual accepted execution lies in a separately charged disclosure/collision event or one of the same Q+1 owner coordinates. This partition does not require any authentication failure. -/
theorem accepted_cases (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (ghost : Ghost) (sessions : Nat)
    (touched : ∀ index message reply, Touch.session index message reply ∈ ghost.touches → index < sessions)
    (bounded : sessions ≤ Q) (accepted : ∃ snap, ghost.acceptance = some snap) :
    BadB setup seed scalar ghost ∨ CollB setup seed scalar ghost ∨
      ∃ j : Fin (Q + 1), Gate setup seed scalar Q j ghost := by
  by_cases bad : BadB setup seed scalar ghost
  · exact Or.inl bad
  · by_cases coll : CollB setup seed scalar ghost
    · exact Or.inr (Or.inl coll)
    · obtain ⟨j, owned⟩ := owner_some setup seed scalar Q ghost sessions touched bounded bad
      exact Or.inr (Or.inr ⟨j, accepted, bad, coll, owned⟩)

end BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry.selected_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry.selected_input

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry.no_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry.no_refusal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry.gate_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry.gate_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry.gate_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry.gate_related

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry.accepted_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry.accepted_cases
