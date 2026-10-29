-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSampling
import BeaconcryptCore.Computational.RegistrationWorldCoinCompiler

/-! The source Beacon constructor draws through EnvEffects, which increments both uniform and coin-effect counts. These exact laws preserve both counters when an independent private challenge scalar replaces the original counted draw's returned bytes. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeEnvSampling
open RegistrationWorldCoinCompiler (coin)
variable {n : Nat} {Value : Type}

def advance (count : Nat) (before : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  { before with primitive := ({ before.primitive.1 with
      uniform := before.primitive.1.uniform + count
      effects := Function.update before.primitive.1.effects .coin (before.primitive.1.effects .coin + count) }, before.primitive.2) }

private theorem advance_add (left right : Nat) (before : PqxdhRecordLiftWorld.State n) :
    advance right (advance left before) = advance (left + right) before := by
  simp only [advance, Function.update_self, Function.update_idem, Nat.add_assoc]

private theorem byte (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ coin ($ᵗ UInt8)).run before =
      (fun value => (value, advance 1 before)) <$> ($ᵗ UInt8) := by
  change (simulateQ coin ((@FinEnum.equiv UInt8 FinEnum.instUInt8).symm <$>
    (unifSpec.query 255 : ProbComp (Fin 256)))).run before = _
  simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query, RegistrationWorldCoinCompiler.coin_run,
    Functor.map_map]
  rfl

private theorem vector (size : Nat) (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ coin ($ᵗ Vector UInt8 size)).run before =
      (fun value => (value, advance size before)) <$> ($ᵗ Vector UInt8 size) := by
  induction size generalizing before with
  | zero =>
      simp only [advance, Nat.add_zero]
      change (pure (#v[], before) : ProbComp (Vector UInt8 0 × PqxdhRecordLiftWorld.State n)) = pure (#v[], _)
      congr 2
      simp only [Function.update_eq_self]
  | succ size ih =>
      change (simulateQ coin (Vector.push <$> ($ᵗ Vector UInt8 size) <*> ($ᵗ UInt8))).run before = _
      simp only [seq_eq_bind_map, bind_map_left]
      simp only [simulateQ_bind, simulateQ_map, StateT.run_map, StateT.run_bind, ih, bind_map_left,
        byte, Functor.map_map, advance_add]
      change _ = (fun value => (value, advance (size + 1) before)) <$>
        (Vector.push <$> ($ᵗ Vector UInt8 size) <*> ($ᵗ UInt8))
      simp only [seq_eq_bind_map, bind_map_left, map_bind, Functor.map_map]

/-- The literal Env sampler retains actual bytes and increments both original counters by exactly the width. -/
theorem bytes (size : Nat) (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ coin ($ᵗ List.Vector UInt8 size)).run before =
      (fun value => (value, advance size before)) <$> ($ᵗ List.Vector UInt8 size) := by
  change (simulateQ coin (List.Vector.ofFn <$>
    ((fun (v : Vector UInt8 size) (i : Fin size) => v.get i) <$>
      ($ᵗ Vector UInt8 size)))).run before = _
  simp only [simulateQ_map, StateT.run_map, vector, Functor.map_map]
  change (fun a => (List.Vector.ofFn fun i => a.get i, advance size before)) <$> ($ᵗ Vector UInt8 size) =
    (fun value => (value, advance size before)) <$> (List.Vector.ofFn <$>
      ((fun (v : Vector UInt8 size) (i : Fin size) => v.get i) <$> ($ᵗ Vector UInt8 size)))
  simp only [Functor.map_map]

/-- Exact constructor scalar sampling retains every World coordinate and both 32-query charges. -/
theorem scalar (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ coin PqxdhJointGapDh.sampleScalar).run before =
      (fun value => (value, advance 32 before)) <$> PqxdhJointGapDh.sampleScalar := bytes 32 before

/-- The counted dummy scalar remains at the actual Env draw position, with no change to either original count. -/
theorem scalar_eager (before : PqxdhRecordLiftWorld.State n)
    (next : PqxdhJointGapDh.ScalarBytes → PqxdhRecordLiftWorld.State n → ProbComp Value) :
    (do let drawn ← (simulateQ coin PqxdhJointGapDh.sampleScalar).run before
        next drawn.1 drawn.2) =ᵈ
      (do let selected ← PqxdhJointGapDh.sampleScalar
          let dummy ← (simulateQ coin PqxdhJointGapDh.sampleScalar).run before
          next selected dummy.2) := by
  simp only [scalar, bind_map_left]
  apply _root_.EvalDistEq.bind_right
  intro selected
  exact (OracleComp.EvalDistEq.bind_const PqxdhJointGapDh.sampleScalar
    (next selected (advance 32 before))).symm

end BeaconcryptCore.Computational.RegistrationNativeEnvSampling

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEnvSampling.bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEnvSampling.bytes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEnvSampling.scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEnvSampling.scalar
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEnvSampling.scalar_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEnvSampling.scalar_eager
