import BeaconcryptCore.Computational.RawCtxSourceChainHandles
import BeaconcryptCore.Computational.RawCtxProtocolReveals

/-!
Freshness uses the finite source lineage of one selected record input. Its forbidden32-byte values are the selected material key, that input and every source root/first/next ancestor. Actual optional current-chain and skipped-key replies enter a monotone private history by value across owner names. Prior authorized disclosures remain in the history; disposed secrets are never added as new live capabilities. This is finite operational exposure bookkeeping, not unbounded public-function closure, a no-collision premise or a secrecy theorem. Public guessing and accidental aliases retain their separate computational terms.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxLiveLineage
open RawCtxSourceChainHandles RawCtxProtocolReveals

/-- Private finite provenance from the target value back to its source root. -/
def lineage {Atom : Type} : Chain Atom → List (Chain Atom)
  | .root atom => [.root atom]
  | .first parent => .first parent :: lineage parent
  | .next parent => .next parent :: lineage parent

/-- The selected record key itself is included through first(input), followed by all input ancestors. -/
noncomputable def forbidden {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (input : Chain Atom) : List RatchetChain :=
  (lineage (.first input)).map (chainOf source roots)

/-- Every source handle occurs in its own finite lineage. -/
theorem self_mem {Atom : Type} (target : Chain Atom) : target ∈ lineage target := by
  cases target <;> simp [lineage]

/-- Earlier ancestors are retained transitively; first32 and second32 edges are both followed. -/
theorem ancestor_subset {Atom : Type} (target ancestor : Chain Atom)
    (present : ancestor ∈ lineage target) : lineage ancestor ⊆ lineage target := by
  induction target <;> simp_all [lineage, List.subset_def]
  all_goals rcases present with rfl | present <;> simp_all [lineage]

/-- Any original input ancestor is forbidden by its actual bytes, independently of owner or handle aliases. -/
theorem ancestor_forbidden {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (input ancestor : Chain Atom) (present : ancestor ∈ lineage input) :
    chainOf source roots ancestor ∈ forbidden source roots input := by
  exact List.mem_map.mpr ⟨ancestor, List.mem_cons_of_mem _ present, rfl⟩

/-- A skipped-material disclosure exposes exactly first(input), so the target record key itself is forbidden. -/
theorem material_key_forbidden {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (input : Chain Atom) :
    (⟨(materialOf source roots input).key.bytes⟩ : RatchetChain) ∈ forbidden source roots input := by
  exact List.mem_cons_self

/-- A disclosure check scans one record key and the finite input lineage; no unbounded closure is evaluated. -/
theorem forbidden_length {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (input : Chain Atom) :
    (forbidden source roots input).length = (lineage input).length + 1 := by
  simp [forbidden, lineage]

def disclosed {serverCount beaconCount : Nat} : Observation serverCount beaconCount → List RatchetChain
  | ⟨.sendChain _, .None⟩ | ⟨.receiveChain _, .None⟩ | ⟨.skippedKey _ _, .None⟩ => []
  | ⟨.sendChain _, .Some chain⟩ | ⟨.receiveChain _, .Some chain⟩ => [chain]
  | ⟨.skippedKey _ _, .Some material⟩ => [⟨material.key.bytes⟩]

def known {serverCount beaconCount : Nat} (prior : List RatchetChain)
    (history : History serverCount beaconCount) : List RatchetChain :=
  prior ++ history.observations.flatMap (fun entry => disclosed entry.2)

def FreshValues (blocked values : List RatchetChain) : Prop :=
  ∀ value ∈ blocked, value ∉ values

noncomputable def exposedValues (blocked values : List RatchetChain) : Bool := by
  classical
  exact values.any (fun value => decide (value ∈ blocked))

def Fresh {serverCount beaconCount : Nat} (blocked prior : List RatchetChain)
    (history : History serverCount beaconCount) : Prop :=
  FreshValues blocked (known prior history)

noncomputable def exposed {serverCount beaconCount : Nat} (blocked : List RatchetChain)
    (observation : Observation serverCount beaconCount) : Bool :=
  exposedValues blocked (disclosed observation)

/-- Each actual optional reveal contributes at most one32-byte value; rejected reveals contribute none. -/
theorem disclosed_length {serverCount beaconCount : Nat}
    (observation : Observation serverCount beaconCount) : (disclosed observation).length ≤ 1 := by
  rcases observation with ⟨request, reply⟩
  cases request <;> cases reply <;> simp [disclosed]

/-- Recording the actual reply preserves prior knowledge and invalidates freshness exactly on a forbidden value. -/
theorem fresh_note {serverCount beaconCount : Nat} (blocked prior : List RatchetChain)
    (history : History serverCount beaconCount) (observation : Observation serverCount beaconCount) :
    Fresh blocked prior (note observation history) ↔
      Fresh blocked prior history ∧ exposed blocked observation = false := by
  simp [Fresh, FreshValues, known, note, exposed, exposedValues, List.mem_append, not_or, forall_and]
  aesop

/-- Advancing the API timestamp leaves all earlier disclosed values intact. -/
theorem fresh_tick {serverCount beaconCount : Nat} (blocked prior : List RatchetChain)
    (history : History serverCount beaconCount) :
    Fresh blocked prior (tick history) ↔ Fresh blocked prior history := by
  rfl

/-- Appending any actual32-byte disclosure retains all earlier knowledge, including roots and public views. -/
theorem freshValues_append (blocked prior later : List RatchetChain) :
    FreshValues blocked (prior ++ later) ↔
      FreshValues blocked prior ∧ FreshValues blocked later := by
  simp [FreshValues, List.mem_append, not_or, forall_and]

/-- The finite exposure flag is exactly the negation of value freshness for the returned block list. -/
theorem exposedValues_false (blocked values : List RatchetChain) :
    exposedValues blocked values = false ↔ FreshValues blocked values := by
  simp [exposedValues, FreshValues]
  aesop

/-- Previously returned root or ancestor bytes invalidate the selected record even after that native secret has disappeared. -/
theorem known_ancestor_not_fresh {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (input ancestor : Chain Atom) (present : ancestor ∈ lineage input) (values : List RatchetChain)
    (disclosed : chainOf source roots ancestor ∈ values) :
    ¬ FreshValues (forbidden source roots input) values := by
  exact fun fresh => fresh _ (ancestor_forbidden source roots input ancestor present) disclosed

/-- A disclosed record key is also a disclosed first32-derived chain for every target descended from that handle. -/
theorem known_first_alias_not_fresh {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (input parent : Chain Atom) (present : .first parent ∈ lineage input) (values : List RatchetChain)
    (disclosed : (⟨(materialOf source roots parent).key.bytes⟩ : RatchetChain) ∈ values) :
    ¬ FreshValues (forbidden source roots input) values := by
  exact known_ancestor_not_fresh source roots input (.first parent) present values disclosed

/-- A successful disclosure of the target record key invalidates that target regardless of its owner label. -/
theorem known_material_not_fresh {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (input : Chain Atom) (values : List RatchetChain)
    (disclosed : (⟨(materialOf source roots input).key.bytes⟩ : RatchetChain) ∈ values) :
    ¬ FreshValues (forbidden source roots input) values := by
  exact fun fresh => fresh _ (material_key_forbidden source roots input) disclosed

end BeaconcryptCore.Computational.RawCtxLiveLineage

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.self_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.self_mem

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.ancestor_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.ancestor_subset

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.ancestor_forbidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.ancestor_forbidden

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.material_key_forbidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.material_key_forbidden

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.forbidden_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.forbidden_length

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.disclosed_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.disclosed_length

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.fresh_note' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.fresh_note

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.fresh_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.fresh_tick

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.freshValues_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.freshValues_append

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.exposedValues_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.exposedValues_false

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.known_ancestor_not_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.known_ancestor_not_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.known_first_alias_not_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.known_first_alias_not_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveLineage.known_material_not_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveLineage.known_material_not_fresh
