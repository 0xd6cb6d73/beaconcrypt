import BeaconcryptCore.Computational.PqxdhDynamicKemRouter
import BeaconcryptCore.Computational.PqxdhLivePhase1State

/-!
The private pool is an interpreter representation, not a permanent public reveal capability. A live owner read first checks the actual native retained prekey/KEM field; terminal and disposed owners reject without consulting the pool. A retained handle selects its actual creation index. This models logical native-field erasure only, with no snapshot, persistence, physical-erasure or restored-state behavior.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead
open PqxdhDynamicKemRouter PqxdhKemIndCca PqxdhLiveKemRouting
open PqxdhLiveKemBirth (PoolSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK I D : Type}

/-- Compromise of the current native KEM field cannot recover a handle already disposed by the source phase transition. -/
def read (owner : RawCtxBeaconLifecycle.State I D Handle) : OracleComp (PoolSpec KemSK) (Option KemSK) :=
  match PqxdhLivePhase1State.privateKeys owner with
  | none => pure none
  | some pair => (PoolSpec KemSK).query (.reveal pair.2.2)

/-- An absent native field rejects before any private service request. -/
theorem absent (owner : RawCtxBeaconLifecycle.State I D Handle)
    (missing : PqxdhLivePhase1State.privateKeys owner = none) :
    read (KemSK := KemSK) owner = pure none := by simp only [read, missing]

/-- Explicit source KEM disposal prevents subsequent pool access, even though the trusted interpreter retains its historical key table. -/
theorem disposed (owner : RawCtxBeaconLifecycle.State I D Handle) :
    read (KemSK := KemSK) (PqxdhLivePhase1State.deleteKem owner) = pure none :=
  absent _ (PqxdhLivePhase1State.deleteKem_privateKeys owner)

set_option backward.isDefEq.respectTransparency false in
/-- A retained live KEM field requests exactly its original creation index, independently of public-key byte collisions. -/
theorem present (owner : RawCtxBeaconLifecycle.State I D Handle) (prekey : D) (handle : Handle)
    (retained : PqxdhLivePhase1State.privateKeys owner = some (prekey, handle)) :
    read (KemSK := KemSK) owner = (PoolSpec KemSK).query (.reveal handle.2) := by simp only [read, retained]

/-- Disposal makes no hidden primitive or selected-key query and preserves all interpreter state under the dynamic router. -/
theorem disposed_routed (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK) (state : PqxdhDynamicKemRouter.State KemSK)
    (owner : RawCtxBeaconLifecycle.State I D Handle) :
    (((simulateQ (pre kem selected reservation) (read (PqxdhLivePhase1State.deleteKem owner))).run).run state) =
      pure (some none, state) := by
  rw [disposed]
  rfl

/-- The source owner read has at most one logical private-pool request; an erased field has zero. -/
theorem read_bound (owner : RawCtxBeaconLifecycle.State I D Handle) :
    (read (KemSK := KemSK) owner).IsTotalQueryBound 1 := by
  unfold read
  split
  · trivial
  · exact ⟨Nat.zero_lt_succ 0, fun _ => trivial⟩

end BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead.absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead.absent
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead.disposed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead.disposed
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead.present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead.present
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead.disposed_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead.disposed_routed
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead.read_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead.read_bound
