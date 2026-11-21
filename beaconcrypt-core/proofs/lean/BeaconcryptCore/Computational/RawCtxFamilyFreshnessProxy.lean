import BeaconcryptCore.Computational.RawCtxLiveLineage
import BeaconcryptCore.Computational.RawCtxGenericFamilyLive
import BeaconcryptCore.Computational.RawCtxSelectedLiveRead

/-!
Actual finite-family disclosure freshness is separated from the selected input's unavailable bytes. The proxy checks retained known ancestors and material values together with the sticky direct-read flag. Known reveal aliases remain explicit candidates, including prior authorized disclosures. Public outputs are not freshness exclusions. Native family lookups, optional rejection and original history observations are kept exact. These operational statements take the current hybrid's blocked values; they do not reevaluate a fixed-source lineage after an ancestor replacement.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy
open RawCtxProtocolReveals RawCtxSelectedChain RawCtxSelectedLiveRead RawCtxLiveLineage
open RawCtxGenericFamilyRead PqxdhSecretInputKdf
variable {S B : Nat}

abbrev Input (S B : Nat) := RawCtxGenericFamilyRead.ReadInput Kernel S B

def readKind : Request S B → Read
  | .sendChain _ => .sendChain
  | .receiveChain _ => .receiveChain
  | .skippedKey _ sequence => .skippedKey sequence

noncomputable def labelValue : (input : Input S B) → (RevealSpec S B).Range input.1
  | (.sendChain _, kernel) => labelRead .sendChain kernel
  | (.receiveChain _, kernel) => labelRead .receiveChain kernel
  | (.skippedKey _ sequence, kernel) => labelRead (.skippedKey sequence) kernel

def direct (input : Input S B) : Bool := exposed (readKind input.1) input.2

noncomputable def actualObservation (target : RatchetChain) (input : Input S B) : Observation S B :=
  ⟨input.1, nativeValue (nativeKernel target) input⟩
noncomputable def labelObservation (input : Input S B) : Observation S B := ⟨input.1, labelValue input⟩

/-- Every unflagged optional family reply is exactly the target-free reply, independent of owner labels. -/
theorem value_before (target : RatchetChain) (input : Input S B) (safe : direct input = false) :
    nativeValue (nativeKernel target) input = labelValue input := by
  rcases input with ⟨request, entry⟩
  cases request with
  | sendChain owner =>
      have equality := before_exposure .sendChain target entry safe
      cases entry <;> simpa only [nativeValue, labelValue, nativeRead, Option.map_none, Option.map_some, OracleSpec.Range, RawCtxGenericFamilyRead.ReadSpec, RawCtxSelectedLiveRead.ReadSpec, RevealSpec] using equality
  | receiveChain owner =>
      have equality := before_exposure .receiveChain target entry safe
      cases entry <;> simpa only [nativeValue, labelValue, nativeRead, Option.map_none, Option.map_some, OracleSpec.Range, RawCtxGenericFamilyRead.ReadSpec, RawCtxSelectedLiveRead.ReadSpec, RevealSpec] using equality
  | skippedKey owner sequence =>
      have equality := before_exposure (.skippedKey sequence) target entry safe
      cases entry <;> simpa only [nativeValue, labelValue, nativeRead, Option.map_none, Option.map_some, OracleSpec.Range, RawCtxGenericFamilyRead.ReadSpec, RawCtxSelectedLiveRead.ReadSpec, RevealSpec] using equality

/-- A flagged current-chain read puts the selected input bytes in the actual native disclosure history. -/
theorem direct_disclosed (target : RatchetChain) (input : Input S B) (hit : direct input = true) :
    target ∈ disclosed (actualObservation target input) := by
  rcases input with ⟨request, entry⟩
  cases request <;> cases entry <;> simp_all only [direct, readKind, RawCtxSelectedLiveRead.exposed, Bool.false_eq_true]
  all_goals split at hit <;> simp_all [actualObservation, nativeValue, disclosed, nativeKernel,
    RawCtxChainInterpretation.mapChains, interpret]

/-- Appending the exact original timestamped observation appends precisely its actual disclosed values. -/
theorem known_note (prior : List RatchetChain) (history : History S B) (observation : Observation S B) :
    known prior (note observation history) = known prior history ++ disclosed observation := by
  simp [known, note, List.append_assoc]

/-- The tracked observation is exactly the actual source reveal at the selected owner in the complete finite family. -/
theorem family_observation {M P I D K : Type} (target : RatchetChain) (request : Request S B)
    (roles : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) :
    actualObservation target (request, RawCtxGenericRoleFamily.selectedKernel (requestOwner request) roles) =
      ⟨request, reveal request (RawCtxGenericRoleFamily.nativeRoles (nativeKernel target) roles)⟩ := by
  exact congrArg (Sigma.mk request) (source_value (nativeKernel target) request roles)

def Witness (target : RatchetChain) (history : History S B) (flag : Bool) : Prop :=
  flag = true → target ∈ known [] history

/-- Every new direct-read bit is witnessed by its actual native optional reply; earlier witness values remain in the original history. -/
theorem witness_note (target : RatchetChain) (input : Input S B) (history : History S B) (flag : Bool)
    (before : Witness target history flag) :
    Witness target (note (actualObservation target input) history) (flag || direct input) := by
  intro hit
  rw [known_note, List.mem_append]
  have either : flag = true ∨ direct input = true := by simpa using hit
  exact either.elim (fun old => Or.inl (before old))
    (fun current => Or.inr (direct_disclosed target input current))

/-- An earlier hidden-read witness survives every non-read API timestamp advance. -/
theorem witness_tick (target : RatchetChain) (history : History S B) (flag : Bool) :
    Witness target (tick history) flag ↔ Witness target history flag := by
  rfl

/-- Actual permitted-disclosure freshness forces the derived direct-read flag to be clear, without conditioning the experiment. -/
theorem fresh_clear (target : RatchetChain) (blocked prior : List RatchetChain)
    (history : History S B) (flag : Bool) (witness : Witness target history flag)
    (fresh : Fresh (target :: blocked) prior history) : flag = false := by
  cases flag with
  | false => rfl
  | true =>
      exfalso
      apply fresh target (List.mem_cons_self)
      exact List.mem_append_right prior (witness rfl)

def knownInputs (prior : List RatchetChain) (history : History S B) : List RootOutput :=
  (known prior history).map RawCtxSelectedQueryTrace.rootVector

def Proxy (blocked prior : List RatchetChain) (history : History S B) (flag : Bool) : Prop :=
  flag = false ∧ Fresh blocked prior history

/-- An unavailable input can coincide with an available disclosed value only through its explicitly recorded32-byte candidate. -/
theorem no_alias (target : RootOutput) (prior : List RatchetChain) (history : History S B)
    (safe : target ∉ knownInputs prior history) :
    RawCtxFreshChainCut.concreteChain target ∉ known prior history := by
  intro present
  apply safe
  exact List.mem_map.mpr ⟨_, present, RawCtxSelectedQueryTrace.rootVector_concrete target⟩

/-- Outside the explicit known-disclosure candidate event, actual byte freshness equals the target-free proxy once the source-derived read witness is retained. -/
theorem fresh_proxy (target : RootOutput) (blocked prior : List RatchetChain) (history : History S B) (flag : Bool)
    (witness : Witness (RawCtxFreshChainCut.concreteChain target) history flag)
    (safe : flag = false → target ∉ knownInputs prior history) :
    Fresh (RawCtxFreshChainCut.concreteChain target :: blocked) prior history ↔ Proxy blocked prior history flag := by
  constructor
  · intro fresh
    exact ⟨fresh_clear _ blocked prior history flag witness fresh,
      fun value present => fresh value (List.mem_cons_of_mem _ present)⟩
  · intro proxy
    have absent := no_alias target prior history (safe proxy.1)
    intro value present
    rcases List.mem_cons.mp present with equal | present
    · exact equal ▸ absent
    · exact proxy.2 value present

/-- The original optional read contributes exactly the same32-byte value to the input-candidate ledger. -/
theorem observation_inputs (owner : Owner S B) (read : Read) (reply : RawCtxSelectedLiveRead.ReadSpec.Range read) :
    (disclosed (observation owner read reply)).map RawCtxSelectedQueryTrace.rootVector = replyInputs read reply := by
  cases read <;> cases reply <;> rfl

/-- The family reader's available-value projection is the exact existing per-read candidate list, including skipped-key material. -/
theorem label_inputs (input : Input S B) :
    (disclosed (labelObservation input)).map RawCtxSelectedQueryTrace.rootVector =
      candidates (readKind input.1) input.2 := by
  rcases input with ⟨request, entry⟩
  cases request with
  | sendChain owner => exact observation_inputs owner .sendChain (labelRead .sendChain entry)
  | receiveChain owner => exact observation_inputs owner .receiveChain (labelRead .receiveChain entry)
  | skippedKey owner sequence => exact observation_inputs owner (.skippedKey sequence) (labelRead (.skippedKey sequence) entry)

/-- Each actual reveal appends at most one candidate and preserves every prior disclosed value. -/
theorem knownInputs_note_length (prior : List RatchetChain) (history : History S B) (observed : Observation S B) :
    (knownInputs prior (note observed history)).length ≤ (knownInputs prior history).length + 1 := by
  simp only [knownInputs, known_note, List.length_map, List.length_append]
  exact Nat.add_le_add_left (disclosed_length observed) _

end BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.value_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.value_before
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.direct_disclosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.direct_disclosed
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.known_note' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.known_note
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.family_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.family_observation
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.witness_note' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.witness_note
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.witness_tick' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.witness_tick
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.fresh_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.fresh_clear
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.no_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.no_alias
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.fresh_proxy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.fresh_proxy
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.observation_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.observation_inputs
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.label_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.label_inputs
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.knownInputs_note_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy.knownInputs_note_length
