-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler
import BeaconcryptCore.Computational.RegistrationNativeKemBirthPool
import BeaconcryptCore.Computational.RegistrationNativePlatformKemClientJournal

/-! Literal private KEM handles keep the same complete pair through every actual counted operation and corrected native callback. Creation appends and all other operations preserve existing rows; public-key aliases are irrelevant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedPoolLookup
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhLiveKemBirth (Pool)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem draw_step (setup : Setup base KemSK)
    (query : (RegistrationNativeKemCountedCapability.LeafSpec KemSK).Domain)
    (before after : Pool KemSK) (reply : (RegistrationNativeKemCountedCapability.LeafSpec KemSK).Range query)
    (supported : (reply, after) ∈ support ((RegistrationNativeKemCountedCapability.draw setup.baseImpl setup.kem query).run before)) :
    RegistrationNativeKemBirthPool.KeyStep setup.baseImpl setup.kem before after := by
  let other : QueryImpl unifSpec (StateT Unit ProbComp) := fun query => StateT.lift (unifSpec.query query)
  have law : Prod.map id (fun pool => ((), pool)) <$>
      (RegistrationNativeKemCountedCapability.draw setup.baseImpl setup.kem query).run before =
      (RegistrationNativeKemInterface.source setup.baseImpl setup.kem unifSpec other (.inr query)).run ((), before) := by
    cases query with
    | inl query => simp only [RegistrationNativeKemCountedCapability.draw, RegistrationNativeKemInterface.source, StateT.run]; rfl
    | inr key => simp only [RegistrationNativeKemCountedCapability.draw, RegistrationNativeKemInterface.source, StateT.run_lift, bind_pure_comp, Functor.map_map]; rfl
  have native : (reply, ((), after)) ∈ support
      ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem unifSpec other (.inr query)).run ((), before)) := by
    rw [← law, support_map]
    exact ⟨_, supported, rfl⟩
  exact RegistrationNativeKemBirthPool.source_step setup.baseImpl setup.kem other (.inr query) ((), before) ((), after) reply native

/-- Every actual counted request preserves an old handle or appends one genuinely generated pair. -/
theorem query_step (setup : Setup base KemSK) (query : (RegistrationNativeKemCountedProgram.Spec KemSK).Domain)
    (before after : Pool KemSK) (reply : (RegistrationNativeKemCountedProgram.Spec KemSK).Range query)
    (supported : (reply, after) ∈ support ((RegistrationNativeKemCountedProgram.handler setup.baseImpl setup.kem query).run before)) :
    RegistrationNativeKemBirthPool.KeyStep setup.baseImpl setup.kem before after := by
  cases query with
  | inl query =>
    simp only [RegistrationNativeKemCountedProgram.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨value, _called, same⟩ := supported
    have preserved : after = before := (congrArg Prod.snd same).symm
    exact Or.inl (congrArg Pool.keys preserved)
  | inr query =>
    have forgotten : (reply.1, after) ∈ support ((RegistrationNativeKemCountedCapability.draw setup.baseImpl setup.kem query).run before) := by
      rw [← RegistrationNativeKemCountedCapability.actual_forget setup.baseImpl setup.kem query before, support_map]
      exact ⟨_, supported, rfl⟩
    exact draw_step setup query before after reply.1 forgotten

/-- Every actual adaptive counted program preserves the exact pair at each old handle. -/
theorem program (setup : Setup base KemSK) (work : OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK) Value)
    (before after : Pool KemSK) (value : Value)
    (supported : (value, after) ∈ support (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work before))
    (handle : Nat) (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (found : before.keys[handle]? = some pair) :
    after.keys[handle]? = some pair := by
  induction work using OracleComp.inductionOn generalizing before after value with
  | pure returned =>
    simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    exact supported.2 ▸ found
  | query_bind query next ih =>
    simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨reply, middle⟩, called, continued⟩ := supported
    exact ih reply middle after value continued
      (RegistrationNativeKemBirthPool.lookup_step setup.baseImpl setup.kem before middle (query_step setup query before middle reply called) handle pair found)

end BeaconcryptCore.Computational.RegistrationNativeKemCountedPoolLookup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedPoolLookup.query_step' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedPoolLookup.query_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedPoolLookup.program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedPoolLookup.program
