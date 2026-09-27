import BeaconcryptCore.Computational.PqxdhLiveKemReservation

/-!
Selecting an actual future KEM creation ordinal moves its exact generator ahead of the whole bounded source continuation. Unselected keys keep their original index order. The comparison includes both complete private services and histories, without identifying owners by public-key bytes. The subsequent executable CCA router must remove the chosen secret and implement the original freshness rule.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveKemSelection
open PqxdhLiveKemReservation PqxdhLiveKemBirth PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

def sampleFamily (sampler : ProbComp (Pair KemSK)) : (count : Nat) → ProbComp (Fin count → Pair KemSK)
  | 0 => pure Fin.elim0
  | count + 1 => do
      let first ← sampler
      let rest ← sampleFamily sampler count
      pure (Fin.cons first rest)

/-- Finite indexing changes only the representation of the exact ordered private reservation. -/
theorem family_list (sampler : ProbComp (Pair KemSK)) (count : Nat) :
    samplePairs sampler count = List.ofFn <$> sampleFamily sampler count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [samplePairs, sampleFamily, ih, map_bind, map_pure, bind_map_left, List.ofFn_succ]
      rfl

/-- Drawing the chosen creation's actual private pair first preserves every complete evaluated continuation of the whole indexed reservation. -/
theorem target_first {Result : Type} (sampler : ProbComp (Pair KemSK))
    (count : Nat) (target : Fin (count + 1))
    (next : (Fin (count + 1) → Pair KemSK) → ProbComp Result) :
    𝒮[sampleFamily sampler (count + 1) >>= next] =
      𝒮[do
        let chosen ← sampler
        let others ← sampleFamily sampler count
        next (target.insertNth chosen others)] := by
  induction count
  case succ count ih =>
    induction target using Fin.cases
    case succ target =>
      calc
        _ = 𝒮[do
          let first ← sampler
          let chosen ← sampler
          let others ← sampleFamily sampler count
          next (Fin.cons first (target.insertNth chosen others))] := by
            change 𝒮[(do
              let first ← sampler
              let others ← sampleFamily sampler (count + 1)
              pure (Fin.cons first others)) >>= next] = _
            simp only [bind_assoc, pure_bind]
            apply evalSPMF_bind_congr'
            intro first
            exact ih target (fun rest => next (Fin.cons first rest))
        _ = _ := by
          rw [PqxdhSecretInputKdf.evalSPMF_sample_comm sampler sampler]
          simp [sampleFamily, Fin.insertNth_succ_cons, bind_assoc]
    case zero => simp [sampleFamily, Fin.insertNth_zero']
  case zero =>
    have targetZero : target = 0 := Fin.ext (by omega)
    simp [targetZero, sampleFamily, Fin.insertNth_zero']

set_option backward.isDefEq.respectTransparency false in
/-- The actual bounded joint/native KEM service draws the chosen future creation first only through this complete execution equality. Every other pair keeps its index, and the created prefix and all earlier histories remain part of the result. -/
theorem source_target_first (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) {Result : Type}
    (client : OracleComp (Spec KemSK) Result) (count : Nat) (target : Fin (count + 1))
    (bounded : client.IsQueryBoundP (IsCreate (KemSK := KemSK)) (count + 1)) (state : State KemSK) :
    𝒮[(simulateQ (impl baseImpl primitives kem) client).run state] =
      𝒮[do
        let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
        let others ← sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
        (simulateQ (reserved baseImpl primitives kem
          (state.2.keys ++ List.ofFn (target.insertNth chosen others))) client).run state] := by
  rw [complete baseImpl primitives kem client (count + 1) bounded state]
  simp only [family_list, bind_map_left]
  exact target_first (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count target
    (fun family => (simulateQ (reserved baseImpl primitives kem (state.2.keys ++ List.ofFn family)) client).run state)

/-- The executable local reservation pays the full actual generator allowance for each unselected private pair. -/
theorem family_uniform (sampler : ProbComp (Pair KemSK)) (qKeygen count : Nat)
    (bounded : sampler.IsTotalQueryBound qKeygen) :
    (sampleFamily sampler count).IsTotalQueryBound (qKeygen * count) := by
  simpa only [family_list, IsTotalQueryBound, isQueryBound_map_iff] using
    reservation_uniform sampler qKeygen count bounded

/-- The chosen future pair is at its absolute source creation index, after the entire already-created prefix. -/
theorem selected_index (earlier : List (Pair KemSK)) {count : Nat} (target : Fin (count + 1))
    (chosen : Pair KemSK) (others : Fin count → Pair KemSK) :
    (earlier ++ List.ofFn (target.insertNth chosen others))[earlier.length + target.val]? = some chosen := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left, List.getElem?_ofFn, target.isLt, _root_.dite_true, Fin.eta, Fin.insertNth_apply_same]

/-- Every locally generated unselected pair resolves to its original absolute source creation position after insertion of the chosen slot. -/
theorem other_index (earlier : List (Pair KemSK)) {count : Nat} (target : Fin (count + 1))
    (chosen : Pair KemSK) (others : Fin count → Pair KemSK) (index : Fin count) :
    (earlier ++ List.ofFn (target.insertNth chosen others))[earlier.length + (target.succAbove index).val]? =
      some (others index) := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left, List.getElem?_ofFn, (target.succAbove index).isLt,
    _root_.dite_true, Fin.eta, Fin.insertNth_apply_succAbove]

/-- The selected generator remains charged once in addition to all local unselected generators; moving it does not erase its challenger cost. -/
theorem selected_uniform (sampler : ProbComp (Pair KemSK)) (qKeygen count : Nat)
    (bounded : sampler.IsTotalQueryBound qKeygen) (target : Fin (count + 1)) :
    (do
      let chosen ← sampler
      let others ← sampleFamily sampler count
      pure (target.insertNth (α := fun _ => Pair KemSK) chosen others)).IsTotalQueryBound (qKeygen + qKeygen * count) := by
  apply isTotalQueryBound_bind bounded
  intro chosen
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using family_uniform sampler qKeygen count bounded

end BeaconcryptCore.Computational.PqxdhLiveKemSelection

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemSelection.family_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemSelection.family_list

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemSelection.target_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemSelection.target_first

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemSelection.source_target_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemSelection.source_target_first

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemSelection.family_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemSelection.family_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemSelection.selected_index' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemSelection.selected_index

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemSelection.other_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemSelection.other_index

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemSelection.selected_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemSelection.selected_uniform
