-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.LazyOracleDiscard
import BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial
import BeaconcryptCore.Computational.PqxdhRecordLiftSeed

/-!
# The 108-byte layout of a hidden slot

A hidden slot's key-schedule output is 108 bytes: the 76-byte ratchet response (key32, next32, nonce12) and the 32-byte opposite initial chain. The deployment environment owns the material (key32, nonce12); the record world owns the seed (next32, right32), which is exactly `PqxdhRecordLiftSeed.Seed`. `joinOutput` and `splitOutput` are inverse bijections, so a uniform 108-byte output has the same law as independent uniform material and a uniform seed, through every continuation. This is a statement about uniform bytes only; it says nothing about how any concrete key schedule is computed.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout
open LazyOracleDiscard

/-- Environment-owned position-1 material of a hidden slot: (key32, nonce12). -/
abbrev Material := RawCtxKdfRequestTable.KeyPart × RawCtxKdfRequestTable.NoncePart

/-- Reassemble the 108-byte key-schedule output from the material and the world seed (next32, right32). -/
def joinOutput (m : Material) (seed : PqxdhRecordLiftSeed.Seed) : PqxdhServerAuthKeySchedule.Output :=
  (RawCtxKdfRequestTable.assemble (m.1, seed.1, m.2), seed.2)

/-- Split the 108-byte output into material and seed. -/
def splitOutput (o : PqxdhServerAuthKeySchedule.Output) : Material × PqxdhRecordLiftSeed.Seed :=
  let parts := PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv o.1
  ((parts.1, parts.2.2), (parts.2.1, o.2))

/-- Splitting a joined output returns the material and the seed unchanged. -/
theorem split_join (m : Material) (seed : PqxdhRecordLiftSeed.Seed) :
    splitOutput (joinOutput m seed) = (m, seed) := by
  have parts := PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.apply_symm_apply (m.1, seed.1, m.2)
  simp only [splitOutput, joinOutput, RawCtxKdfRequestTable.assemble, parts]

/-- Joining the two halves of a split output returns the output unchanged. -/
theorem join_split (o : PqxdhServerAuthKeySchedule.Output) :
    joinOutput (splitOutput o).1 (splitOutput o).2 = o := by
  simp only [joinOutput, splitOutput]
  rw [RawCtxKdfRequestTable.assemble_parts]

/-- The 108-byte layout as an equivalence. -/
def joinEquiv : Material × PqxdhRecordLiftSeed.Seed ≃ PqxdhServerAuthKeySchedule.Output where
  toFun x := joinOutput x.1 x.2
  invFun := splitOutput
  left_inv x := split_join x.1 x.2
  right_inv := join_split

/-- The next chain of a joined output is the world seed's first half. -/
theorem joinOutput_next (m : Material) (seed : PqxdhRecordLiftSeed.Seed) :
    PqxdhOrderedChainHybrids.nextChain (joinOutput m seed).1 = seed.1 :=
  PqxdhRecordLiftSeed.assembled_next m.1 seed.1 m.2

/-- The source factor of a joined output is the assembled ratchet response and the seed's opposite chain. -/
theorem factor_join (m : Material) (seed : PqxdhRecordLiftSeed.Seed) :
    PqxdhServerAuthCtxMaterial.factor (joinOutput m seed) =
      (RawCtxKdfRequestTable.fullResponse (RawCtxKdfRequestTable.assemble (m.1, seed.1, m.2)), seed.2) :=
  rfl

/-- The 108-byte split: a uniform output is independent uniform material and a uniform seed, through every continuation. The proof transports the uniform measure along the bijection `joinEquiv` on the discrete measurable structure of the two finite types. -/
theorem uniform_split {Result : Type} (k : PqxdhServerAuthKeySchedule.Output → ProbComp Result) :
    LawEq ($ᵗ PqxdhServerAuthKeySchedule.Output >>= k)
      (do let m ← $ᵗ Material; let seed ← $ᵗ PqxdhRecordLiftSeed.Seed; k (joinOutput m seed)) := by
  intro β _ cont
  let : MeasurableSpace (Material × PqxdhRecordLiftSeed.Seed) := ⊤
  let : DiscreteMeasurableSpace (Material × PqxdhRecordLiftSeed.Seed) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let : MeasurableSpace PqxdhServerAuthKeySchedule.Output := ⊤
  let : DiscreteMeasurableSpace PqxdhServerAuthKeySchedule.Output :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have split : (($ᵗ (Material × PqxdhRecordLiftSeed.Seed)) >>= fun x => k (joinEquiv x) >>= cont) =
      ((do let m ← $ᵗ Material; let seed ← $ᵗ PqxdhRecordLiftSeed.Seed; k (joinOutput m seed)) >>= cont) := by
    rw [← PqxdhFullSecretInputKdf.pairSample (A := Material) (B := PqxdhRecordLiftSeed.Seed)]
    simp only [bind_assoc, pure_bind]
    rfl
  rw [← split, bind_assoc]
  exact (evalDist_bind_bijective_uniform_cross _ _ SampleableType.evalDist_uniformSample
    SampleableType.evalDist_uniformSample joinEquiv joinEquiv.bijective (fun o => k o >>= cont)).symm

/-- m5: drawing the material costs at most 44 uniform queries. -/
theorem material_bound : ($ᵗ Material : ProbComp Material).IsTotalQueryBound 44 := by
  simp only [← PqxdhFullSecretInputKdf.pairSample]
  exact isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun key =>
      isTotalQueryBound_bind
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 12) (fun nonce =>
          show (pure (key, nonce) : ProbComp Material).IsTotalQueryBound 0 from by trivial))

end BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.split_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.split_join

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.join_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.join_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.joinOutput_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.joinOutput_next

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.factor_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.factor_join

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.uniform_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.uniform_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.material_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout.material_bound
