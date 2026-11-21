import BeaconcryptCore.Computational.RawCtxSelectedMessageKey
import BeaconcryptCore.Computational.RawCtxLiveLineage
import BeaconcryptCore.Computational.RawCtxSelectedQueryTrace

/-!
Selected-message freshness retains the actual optional reveal requests, owner names and timestamps. A skipped slot may carry the unavailable selected message key; current chains and all other material retain their original values. Interpreting this private log reconstructs the original byte-based disclosure history, including equal values under different owners. The exact freshness event separates a returned hidden slot from a finite list of known candidate values. It does not assume those values miss the selected key or bound adaptive key recovery by a uniform guessing term.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness
open PqxdhSecretInputKdf RawCtxSelectedMessageKey RawCtxFreshChainCut
open RawCtxProtocolReveals (Request)
variable {S B : Nat}

def RevealSpec (S B : Nat) : OracleSpec (Request S B)
  | .sendChain _ | .receiveChain _ => core.option.Option RatchetChain
  | .skippedKey _ _ => core.option.Option Slot

abbrev Observation (S B : Nat) :=
  (request : (RevealSpec S B).Domain) × (RevealSpec S B).Range request

structure History (S B : Nat) where
  position : Nat
  observations : List (Nat × Observation S B)

def interpretObservation (key : RootOutput) : Observation S B → RawCtxProtocolReveals.Observation S B
  | ⟨.sendChain owner, reply⟩ => ⟨.sendChain owner, reply⟩
  | ⟨.receiveChain owner, reply⟩ => ⟨.receiveChain owner, reply⟩
  | ⟨.skippedKey owner sequence, .None⟩ => ⟨.skippedKey owner sequence, .None⟩
  | ⟨.skippedKey owner sequence, .Some material⟩ =>
      ⟨.skippedKey owner sequence, .Some (interpret key material)⟩

def interpretHistory (key : RootOutput) (history : History S B) : RawCtxProtocolReveals.History S B :=
  ⟨history.position, history.observations.map (fun entry => (entry.1, interpretObservation key entry.2))⟩

def candidates : Observation S B → List RatchetChain
  | ⟨.sendChain _, .Some chain⟩ | ⟨.receiveChain _, .Some chain⟩ => [chain]
  | ⟨.skippedKey _ _, .Some (.known material)⟩ => [⟨material.key.bytes⟩]
  | _ => []

def hiddenObservation : Observation S B → Bool
  | ⟨.skippedKey _ _, .Some (.hidden _)⟩ => true
  | _ => false

def known (prior : List RatchetChain) (history : History S B) : List RatchetChain :=
  prior ++ history.observations.flatMap (fun entry => candidates entry.2)

def hidden (history : History S B) : Bool :=
  history.observations.any (fun entry => hiddenObservation entry.2)

def note (observation : Observation S B) (history : History S B) : History S B :=
  ⟨history.position + 1, history.observations ++ [(history.position, observation)]⟩

/-- Each source optional reveal contributes at most one known candidate; hidden returns are tracked separately, and rejection contributes none. -/
theorem candidates_length (observation : Observation S B) : (candidates observation).length ≤ 1 := by
  rcases observation with ⟨request, reply⟩
  cases request <;> cases reply <;> simp only [candidates, List.length_nil, List.length_singleton, Nat.zero_le, Nat.le_refl]
  rename_i material
  cases material <;> simp

/-- Every native disclosed byte value is either the returned hidden key or one exact known candidate; no constructor injectivity is assumed. -/
theorem disclosed_mem (key : RootOutput) (observation : Observation S B) (value : RatchetChain) :
    value ∈ RawCtxLiveLineage.disclosed (interpretObservation key observation) ↔
      (hiddenObservation observation = true ∧ value = concreteChain key) ∨ value ∈ candidates observation := by
  rcases observation with ⟨request, reply⟩
  cases request <;> cases reply <;> simp only [interpretObservation, RawCtxLiveLineage.disclosed,
    hiddenObservation, candidates, Bool.false_eq_true, false_and, false_or, List.mem_singleton, List.not_mem_nil]
  rename_i material
  cases material <;> simp [interpret, concreteMaterial, concreteChain]

/-- Interpreting the complete timestamped source history exposes exactly its known candidates and any explicitly returned selected-key slot. -/
theorem known_mem (key : RootOutput) (prior : List RatchetChain) (history : History S B) (value : RatchetChain) :
    value ∈ RawCtxLiveLineage.known prior (interpretHistory key history) ↔
      (hidden history = true ∧ value = concreteChain key) ∨ value ∈ known prior history := by
  simp only [RawCtxLiveLineage.known, interpretHistory, List.mem_append, List.mem_flatMap, List.mem_map,
    known, hidden, List.any_eq_true]
  simp only [exists_exists_and_eq_and, disclosed_mem]
  aesop

/-- Exact source byte freshness requires no returned hidden key, freshness of the retained known lineage, and absence of a selected-key hit among all actual known replies. -/
theorem fresh_factor (key : RootOutput) (remaining prior : List RatchetChain) (history : History S B) :
    RawCtxLiveLineage.Fresh (concreteChain key :: remaining) prior (interpretHistory key history) ↔
      hidden history = false ∧ RawCtxLiveLineage.FreshValues remaining (known prior history) ∧
        concreteChain key ∉ known prior history := by
  simp only [RawCtxLiveLineage.Fresh, RawCtxLiveLineage.FreshValues, List.mem_cons, known_mem]
  cases flag : hidden history <;> simp_all
  aesop

/-- The concrete interpreter preserves the exact source timestamp and appended optional reply. -/
theorem interpret_note (key : RootOutput) (observation : Observation S B) (history : History S B) :
    interpretHistory key (note observation history) =
      RawCtxProtocolReveals.note (interpretObservation key observation) (interpretHistory key history) := by
  simp [interpretHistory, note, RawCtxProtocolReveals.note]

/-- Hidden revelation is monotone under actual logged replies, including every later failure or successful operation. -/
theorem hidden_note (observation : Observation S B) (history : History S B) :
    hidden (note observation history) = (hidden history || hiddenObservation observation) := by
  simp [hidden, note]

/-- All duplicate and cross-owner known values remain in their original source order. -/
theorem known_note (prior : List RatchetChain) (observation : Observation S B) (history : History S B) :
    known prior (note observation history) = known prior history ++ candidates observation := by
  simp [known, note, List.append_assoc]

/-- The probe list charges all earlier authorized disclosures and at most one candidate per actual optional reveal, without removing repeated values. -/
theorem known_length (prior : List RatchetChain) (history : History S B) :
    (known prior history).length ≤ prior.length + history.observations.length := by
  suffices ∀ entries : List (Nat × Observation S B),
      (entries.flatMap (fun entry => candidates entry.2)).length ≤ entries.length by
    simpa only [known, List.length_append] using Nat.add_le_add_left (this history.observations) prior.length
  intro entries
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have bound := candidates_length entry.2
      omega

/-- Any returned hidden skipped material makes the original selected-record freshness event false; no later continuation can undo a retained observation. -/
theorem hidden_stops (key : RootOutput) (remaining prior : List RatchetChain) (history : History S B)
    (position : Nat) (observation : Observation S B)
    (retained : (position, observation) ∈ history.observations) (returned : hiddenObservation observation = true) :
    ¬ RawCtxLiveLineage.Fresh (concreteChain key :: remaining) prior (interpretHistory key history) := by
  intro fresh
  have clear := (fresh_factor key remaining prior history).mp fresh |>.1
  have exposed : hidden history = true := List.any_eq_true.mpr ⟨(position, observation), retained, returned⟩
  rw [clear] at exposed
  cases exposed

/-- Exact32-byte inputs for the ordinary CTX shared-ROM probes, in original disclosure order. -/
def keys (prior : List RatchetChain) (history : History S B) : List CtxRomAuth.CtxKey :=
  (known prior history).map RawCtxSelectedQueryTrace.rootVector

/-- A native selected-key equality is exactly one equality with the probe list; representation preserves every byte and permits aliases. -/
theorem keys_hit (key : RootOutput) (prior : List RatchetChain) (history : History S B) :
    concreteChain key ∈ known prior history ↔ key ∈ keys prior history := by
  rw [keys, List.mem_map]
  constructor
  · intro present
    exact ⟨concreteChain key, present, RawCtxSelectedQueryTrace.rootVector_concrete key⟩
  · rintro ⟨chain, present, same⟩
    have equal : chain = concreteChain key := by
      apply BeaconcryptCore.Refinement.RepresentationBridge.absChain_injective
      change (RawCtxSelectedQueryTrace.rootVector chain).toList =
        (RawCtxSelectedQueryTrace.rootVector (concreteChain key)).toList
      rw [same, RawCtxSelectedQueryTrace.rootVector_concrete]
    exact equal ▸ present

/-- Every stopped known candidate incurs one CTX prefix probe, including duplicate byte values. -/
theorem keys_length (prior : List RatchetChain) (history : History S B) :
    (keys prior history).length ≤ prior.length + history.observations.length := by
  simpa only [keys, List.length_map] using known_length prior history

/-- The executable part of the selected-key freshness check uses only the retained known lineage and the hidden-reveal flag. -/
def Clear (remaining prior : List RatchetChain) (history : History S B) : Prop :=
  hidden history = false ∧ RawCtxLiveLineage.FreshValues remaining (known prior history)

/-- The native freshness event equals the key-free check minus the exact ordinary CTX candidate-key hit event. -/
theorem fresh_keys (key : RootOutput) (remaining prior : List RatchetChain) (history : History S B) :
    RawCtxLiveLineage.Fresh (concreteChain key :: remaining) prior (interpretHistory key history) ↔
      Clear remaining prior history ∧ key ∉ keys prior history := by
  rw [fresh_factor, keys_hit]
  exact and_assoc.symm

end BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.candidates_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.candidates_length
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.disclosed_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.disclosed_mem
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.known_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.known_mem
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.fresh_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.fresh_factor
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.interpret_note' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.interpret_note
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.hidden_note' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.hidden_note
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.known_note' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.known_note
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.known_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.known_length
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.hidden_stops' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.hidden_stops
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.keys_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.keys_hit
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.keys_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.keys_length
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.fresh_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness.fresh_keys
