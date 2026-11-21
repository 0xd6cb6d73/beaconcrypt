-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicStartup

/-! Moving an independent selected scalar into the private challenge leaves the actual constructor's counted dummy draw at its original position. The exact sampler laws retain the complete World, including every randomness count; no early challenge draw is charged to that World. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSampling
variable {n : Nat} {Value : Type}
open PqxdhRecordLiftWorld (countCoin sampled)

private theorem byte (count : Nat) :
    (simulateQ countCoin ($ᵗ UInt8)).run count =
      (fun value => (value, count + 1)) <$> ($ᵗ UInt8) := by
  change (simulateQ countCoin ((@FinEnum.equiv UInt8 FinEnum.instUInt8).symm <$>
    (unifSpec.query 255 : ProbComp (Fin 256)))).run count = _
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run]
  rfl

private theorem vector (size count : Nat) :
    (simulateQ countCoin ($ᵗ Vector UInt8 size)).run count =
      (fun value => (value, count + size)) <$> ($ᵗ Vector UInt8 size) := by
  induction size generalizing count with
  | zero => rfl
  | succ size ih =>
      change (simulateQ countCoin (Vector.push <$> ($ᵗ Vector UInt8 size) <*> ($ᵗ UInt8))).run count = _
      simp only [seq_eq_bind_map, bind_map_left]
      simp only [simulateQ_bind, simulateQ_map, StateT.run_map, StateT.run_bind, ih, bind_map_left,
        byte, Functor.map_map]
      change _ = (fun value => (value, count + (size + 1))) <$>
        (Vector.push <$> ($ᵗ Vector UInt8 size) <*> ($ᵗ UInt8))
      simp only [seq_eq_bind_map, bind_map_left, map_bind, Functor.map_map, Nat.add_assoc]

/-- Every literal byte-vector sampler keeps its exact count and its actual uniform bytes. -/
theorem bytes (size count : Nat) :
    (simulateQ countCoin ($ᵗ List.Vector UInt8 size)).run count =
      (fun value => (value, count + size)) <$> ($ᵗ List.Vector UInt8 size) := by
  change (simulateQ countCoin (List.Vector.ofFn <$>
    ((fun (v : Vector UInt8 size) (i : Fin size) => v.get i) <$>
      ($ᵗ Vector UInt8 size)))).run count = _
  simp only [simulateQ_map, StateT.run_map, vector, Functor.map_map]
  change (fun a => (List.Vector.ofFn fun i => a.get i, count + size)) <$> ($ᵗ Vector UInt8 size) =
    (fun value => (value, count + size)) <$> (List.Vector.ofFn <$>
      ((fun (v : Vector UInt8 size) (i : Fin size) => v.get i) <$> ($ᵗ Vector UInt8 size)))
  simp only [Functor.map_map]

def advance (count : Nat) (before : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  { before with primitive := ({ before.primitive.1 with uniform := before.primitive.1.uniform + count }, before.primitive.2) }

/-- Native byte sampling retains the complete World and advances its count by precisely the byte width. -/
theorem sampled_bytes (size : Nat) (before : PqxdhRecordLiftWorld.State n) :
    (sampled ($ᵗ List.Vector UInt8 size)).run before =
      (fun value => (value, advance size before)) <$> ($ᵗ List.Vector UInt8 size) := by
  change (do let result ← (simulateQ countCoin ($ᵗ List.Vector UInt8 size)).run before.primitive.1.uniform
             pure (result.1, { before with primitive := ({ before.primitive.1 with uniform := result.2 }, before.primitive.2) })) = _
  rw [bytes size before.primitive.1.uniform]
  simp only [advance, bind_pure_comp, Functor.map_map]

/-- Actual native scalar sampling changes only the original World's uniform count by exactly 32. -/
theorem scalar (before : PqxdhRecordLiftWorld.State n) :
    (sampled PqxdhJointGapDh.sampleScalar).run before =
      (fun value => (value, advance 32 before)) <$> PqxdhJointGapDh.sampleScalar :=
  sampled_bytes 32 before

/-- An early independent private scalar can replace the scalar used by the continuation while the original constructor still performs its complete counted dummy draw. -/
theorem scalar_eager (before : PqxdhRecordLiftWorld.State n)
    (next : PqxdhJointGapDh.ScalarBytes → PqxdhRecordLiftWorld.State n → ProbComp Value) :
    (do let drawn ← (sampled PqxdhJointGapDh.sampleScalar).run before
        next drawn.1 drawn.2) =ᵈ
      (do let selected ← PqxdhJointGapDh.sampleScalar
          let dummy ← (sampled PqxdhJointGapDh.sampleScalar).run before
          next selected dummy.2) := by
  simp only [scalar, bind_map_left]
  apply _root_.EvalDistEq.bind_right
  intro selected
  exact (OracleComp.EvalDistEq.bind_const PqxdhJointGapDh.sampleScalar
    (next selected (advance 32 before))).symm

end BeaconcryptCore.Computational.RegistrationNativeSampling

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSampling.bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSampling.bytes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSampling.scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSampling.scalar
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSampling.scalar_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSampling.scalar_eager

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSampling.sampled_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSampling.sampled_bytes
