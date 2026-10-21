import BeaconcryptCore.Computational.RawCtxSelectiveChainGame
import BeaconcryptCore.Computational.RawCtxSelectedQueryTrace

/-!
A finite catalogue names a Server peer and a Beacon handle for each selected established session. Target choices add one physical direction and a bounded logical record index relative to the supplied entry chains. Source selection reads the existing directional sender's installed send chain; it invents no owner or replacement kernel. The selected family keeps the original native schedule, bounds the randomized prefix by that target's record number and runs stage zero when the selected sender is absent.

The final adversary-selected target is handled by an exact winning-event partition of the same original execution, then an explicit sum over all targets or the full sessionCount*2*recordCount factor. No pre-execution choice by the adversary is assumed. The catalogue itself does not prove shared-root establishment, zero counters, record reachability, secrecy or a uniform source sampler. Those consuming source facts must tie catalogue entries to actual initialization; nonzero entry counters require explicit source sequence offsets. Snapshot, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveTargets
open RawCtxProtocolReveals RawCtxSelectiveChainGame PqxdhSecretInputKdf PqxdhJointKdfGame RawCtxKdfRequestTable

/-- A finite catalogue names both actual role handles of an established cryptographic session. -/
structure Pair (serverCount beaconCount : Nat) where
  server : Fin serverCount
  peer : Std.U64
  beacon : Fin beaconCount

/-- False selects Server-to-Beacon; true selects Beacon-to-Server. The final coordinate is the zero-based logical record index relative to the supplied entry chains. -/
abbrev Target (sessionCount recordCount : Nat) := Fin sessionCount × Bool × Fin recordCount

def sender {serverCount beaconCount : Nat} (pair : Pair serverCount beaconCount) (direction : Bool) :
    Owner serverCount beaconCount :=
  if direction then .beacon pair.beacon else .server pair.server pair.peer

def receiver {serverCount beaconCount : Nat} (pair : Pair serverCount beaconCount) (direction : Bool) :
    Owner serverCount beaconCount :=
  if direction then .server pair.server pair.peer else .beacon pair.beacon

def recordNumber {sessionCount recordCount : Nat} (target : Target sessionCount recordCount) : Nat :=
  target.2.2.val + 1

/-- The selected starting input is read from the actual directional sender's installed native chain. -/
def startingInput {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (pair : Pair serverCount beaconCount) (direction : Bool)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) : Option RootOutput := do
  let kernel ← selectedKernel (sender pair direction) roles
  pure (RawCtxSelectedQueryTrace.rootVector kernel.refined.send_chain)

/-- Both orientations point at the actual complementary handles, with no independent-owner premise. -/
theorem orientations {serverCount beaconCount : Nat} (pair : Pair serverCount beaconCount) :
    sender pair false = .server pair.server pair.peer ∧ receiver pair false = .beacon pair.beacon ∧
    sender pair true = .beacon pair.beacon ∧ receiver pair true = .server pair.server pair.peer := by
  simp [sender, receiver]

/-- Source target selection has exactly the finite session, two-direction and logical-record factors. -/
theorem target_card (sessionCount recordCount : Nat) :
    Fintype.card (Target sessionCount recordCount) = sessionCount * 2 * recordCount := by
  simp [Target, Nat.mul_assoc]

/-- The selected record is positive and lies within the explicit catalogue's record bound. -/
theorem record_bound {sessionCount recordCount : Nat} (target : Target sessionCount recordCount) :
    1 ≤ recordNumber target ∧ recordNumber target ≤ recordCount := by
  have inside := target.2.2.isLt
  simp only [recordNumber]
  omega

/-- Missing native owners remain absent, rather than being replaced by a fresh selected kernel. -/
theorem starting_missing {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (pair : Pair serverCount beaconCount) (direction : Bool)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (missing : selectedKernel (sender pair direction) roles = none) : startingInput pair direction roles = none := by
  simp [startingInput, missing]

/-- A supported selected input is exactly the existing native send-chain field. -/
theorem starting_present {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (pair : Pair serverCount beaconCount) (direction : Bool)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (kernel : ConcreteRatchetKernel) (present : selectedKernel (sender pair direction) roles = some kernel) :
    startingInput pair direction roles = some (RawCtxSelectedQueryTrace.rootVector kernel.refined.send_chain) := by
  simp [startingInput, present]

/-- The selector runs at the end of the original adaptive execution; none selects no target. -/
def selectedEvent {Choice Result : Type} (select : Result → Option Choice)
    (win : Choice → Result → Prop) (target : Choice) (result : Result) : Prop :=
  select result = some target ∧ win target result

def anyEvent {Choice Result : Type} (select : Result → Option Choice)
    (win : Choice → Result → Prop) (result : Result) : Prop := ∃ target, selectedEvent select win target result

/-- A post-execution adaptive target choice partitions the original winning event exactly, without preselecting the adversary's eventual choice. -/
theorem event_partition {Choice Result : Type} [Fintype Choice] [DecidableEq Choice]
    (game : ProbComp Result) (select : Result → Option Choice) (win : Choice → Result → Prop) :
    Pr{let x ← game}[(anyEvent select win) x] = ∑ target, Pr{let x ← game}[(selectedEvent select win target) x] := by
  classical
  rw [OracleComp.prEvent_eq_tsum_ite,
    Finset.sum_congr rfl fun target _ => OracleComp.prEvent_eq_tsum_ite game (selectedEvent select win target)]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun result => ?_
  cases selected : select result with
  | none => simp [anyEvent, selectedEvent, selected, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
  | some target =>
    by_cases accepted : win target result
    · have filtered : Finset.univ.filter (fun other => target = other ∧ win other result) = {target} := by
        ext other
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · exact fun proof => proof.1.symm
        · intro equal
          subst other
          exact ⟨rfl, accepted⟩
      simp [anyEvent, selectedEvent, selected, accepted, filtered, -evalDist_apply_singleton, -evalDist_apply_setOf,
        -evalDist_apply_univ]
    · simp [anyEvent, selectedEvent, selected, accepted, -evalDist_apply_singleton, -evalDist_apply_setOf,
        -evalDist_apply_univ]

/-- Fixed-target reductions are summed over the adversary's original final-choice partition. -/
theorem selection_sum {Choice Result : Type} [Fintype Choice] [DecidableEq Choice]
    (game : ProbComp Result) (select : Result → Option Choice) (win : Choice → Result → Prop)
    (loss : Choice → ENNReal)
    (bounded : ∀ target, Pr{let x ← game}[(selectedEvent select win target) x] ≤ loss target) :
    Pr{let x ← game}[(anyEvent select win) x] ≤ ∑ target, loss target := by
  rw [event_partition]
  exact Finset.sum_le_sum (fun target _ => bounded target)

/-- A common per-target bound pays the full established-session, two-direction and reachable-record selection factor. -/
theorem selection_factor {Result : Type} (sessionCount recordCount : Nat)
    (game : ProbComp Result) (select : Result → Option (Target sessionCount recordCount))
    (win : Target sessionCount recordCount → Result → Prop) (loss : ENNReal)
    (bounded : ∀ target, Pr{let x ← game}[(selectedEvent select win target) x] ≤ loss) :
    Pr{let x ← game}[(anyEvent select win) x] ≤ (sessionCount * 2 * recordCount : Nat) * loss := by
  simpa only [Finset.sum_const, Finset.card_univ, target_card, nsmul_eq_mul] using
    selection_sum game select win (fun _ => loss) bounded

def unavailableInput : RootOutput := ⟨List.replicate 32 0, by simp⟩

/-- The selected experiment continues all native operations even when the target owner is absent; that case performs no substitutions. -/
noncomputable def selectedFamily {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    {sessionCount recordCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (serverCount beaconCount : Nat) (catalogue : Fin sessionCount → Pair serverCount beaconCount)
    (target : Target sessionCount recordCount) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (table : Table) :=
  let input := startingInput (catalogue target.1) target.2.1 state.1
  family source writer (if input.isSome then min stage (recordNumber target) else 0)
    serverCount beaconCount senderId route decode client state primitive
      (table, ⟨input.getD unavailableInput, 0⟩)

/-- At stage zero the selected experiment retains the complete real family cache/state regardless of target availability. -/
theorem selected_zero {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    {sessionCount recordCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (catalogue : Fin sessionCount → Pair serverCount beaconCount)
    (target : Target sessionCount recordCount) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (table : Table) :
    project <$> selectedFamily source writer 0 serverCount beaconCount catalogue target senderId route decode client state primitive table =
      (simulateQ (tableImpl source (RawCtxProtocolBackend.backend source writer))
        (RawCtxSelectiveKdfFamily.program serverCount beaconCount senderId route decode client state)).run (primitive, table) := by
  simp only [selectedFamily, Nat.zero_min, ite_self]
  exact family_zero source writer serverCount beaconCount senderId route decode client state primitive table _

/-- Selecting an absent native sender never changes the ongoing original family schedule. -/
theorem selected_missing {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    {sessionCount recordCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (serverCount beaconCount : Nat) (catalogue : Fin sessionCount → Pair serverCount beaconCount)
    (target : Target sessionCount recordCount) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (table : Table)
    (missing : selectedKernel (sender (catalogue target.1) target.2.1) state.1 = none) :
    selectedFamily source writer stage serverCount beaconCount catalogue target senderId route decode client state primitive table =
      selectedFamily source writer 0 serverCount beaconCount catalogue target senderId route decode client state primitive table := by
  simp only [selectedFamily, starting_missing _ _ _ missing, Option.isSome_none, Bool.false_eq_true, ite_false]

end BeaconcryptCore.Computational.RawCtxSelectiveTargets

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveTargets.orientations' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveTargets.orientations

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveTargets.target_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveTargets.target_card

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveTargets.record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveTargets.record_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveTargets.starting_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveTargets.starting_missing

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveTargets.starting_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveTargets.starting_present

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveTargets.event_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveTargets.event_partition

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveTargets.selection_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveTargets.selection_sum

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveTargets.selection_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveTargets.selection_factor

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveTargets.selected_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveTargets.selected_zero

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveTargets.selected_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveTargets.selected_missing
