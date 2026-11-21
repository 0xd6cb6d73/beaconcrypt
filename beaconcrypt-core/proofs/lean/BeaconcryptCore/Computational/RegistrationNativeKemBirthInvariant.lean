-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBirthPool
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! Concrete native deployment effects preserve every existing owner's exact indexed private pair and the original generator support. Owners, record-World indices and KEM handles remain separate. Phase changes are handled by explicit retained handle/public-key metadata rather than by private-key equality or a public-key injectivity assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemBirthPool (Generated KeyStep)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeExperiment (State trusted)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

def metadata {mlSource : RegistrationNativeMldsa.Source} (owner : Owner mlSource) :=
  (owner.kemHandle, owner.kemPublic)

def Owns {mlSource : RegistrationNativeMldsa.Source} (owners : List (Owner mlSource))
    (pool : PqxdhLiveKemBirth.Pool KemSK) : Prop :=
  ∀ owner ∈ owners, ∃ pair, pool.keys[owner.kemHandle]? = some pair ∧ pair.1 = owner.kemPublic

def Holds (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owners : List (Owner mlSource)) (pool : PqxdhLiveKemBirth.Pool KemSK) : Prop :=
  Generated setup.baseImpl setup.kem pool ∧ Owns owners pool

/-- Every concrete global effect has the actual source pool step, including sampled primitive work and all rejected private decapsulations. -/
theorem trusted_step (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (mlSource : RegistrationNativeMldsa.Source)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before after : State n KemSK mlSource)
    (reply : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query)
    (supported : (reply, after) ∈ support
      ((trusted setup checks representation created mlSource query).run before)) :
    KeyStep setup.baseImpl setup.kem before.pool after.pool := by
  cases query with
  | inl effect =>
      simp only [trusted, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
        StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨result, _, returned⟩ := supported
      cases returned
      exact Or.inl rfl
  | inr lower =>
      simp only [trusted, PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp,
        Functor.map_map, support_map] at supported
      obtain ⟨result, sampled, returned⟩ := supported
      cases returned
      have native : result.1 ∈ support
          ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
            (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) lower).run
              (before.server.world.auxiliary, before.pool)) := by
        apply OracleComp.support_simulateQ_run'_subset PqxdhRecordLiftWorld.countCoin _
          before.server.world.world.1.primitive.1.uniform
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst sampled
      exact RegistrationNativeKemBirthPool.source_step setup.baseImpl setup.kem
        (RegistrationNativeKemBackend.serverOther setup checks representation created.seed)
        lower _ _ result.1.1 native

private theorem step_holds (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owners : List (Owner mlSource)) (before after : PqxdhLiveKemBirth.Pool KemSK)
    (prior : Holds setup owners before) (step : KeyStep setup.baseImpl setup.kem before after) :
    Holds setup owners after := by
  refine ⟨RegistrationNativeKemBirthPool.generated_step setup.baseImpl setup.kem before after prior.1 step, ?_⟩
  intro owner member
  obtain ⟨pair, found, publicKey⟩ := prior.2 owner member
  exact ⟨pair, RegistrationNativeKemBirthPool.lookup_step setup.baseImpl setup.kem before after step _ pair found, publicKey⟩

/-- An arbitrary adaptive global subprogram preserves the exact private pair of every earlier owner and all generator receipts. -/
theorem trusted_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (mlSource : RegistrationNativeMldsa.Source)
    (owners : List (Owner mlSource))
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before after : State n KemSK mlSource) (reply : Value)
    (prior : Holds setup owners before.pool)
    (supported : (reply, after) ∈ support
      ((simulateQ (trusted setup checks representation created mlSource) work).run before)) :
    Holds setup owners after.pool := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (trusted setup checks representation created mlSource) (fun current => Holds setup owners current.pool)
    (fun query current valid result reached => step_holds setup owners current.pool result.2.pool valid
      (trusted_step setup checks representation created mlSource query current result.2 result.1 reached))
    work before prior (reply, after) supported

/-- Native lifecycle updates retain ownership whenever their actual local list preserves each handle/public-key pair. -/
theorem metadata_transport {mlSource : RegistrationNativeMldsa.Source}
    (before after : List (Owner mlSource)) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prior : Owns before pool) (same : after.map metadata = before.map metadata) : Owns after pool := by
  intro owner member
  have memberMeta : metadata owner ∈ before.map metadata := by rw [← same]; exact List.mem_map_of_mem member
  obtain ⟨old, oldMember, oldMeta⟩ := List.mem_map.mp memberMeta
  obtain ⟨pair, found, publicKey⟩ := prior old oldMember
  have handle : old.kemHandle = owner.kemHandle := congrArg Prod.fst oldMeta
  have key : old.kemPublic = owner.kemPublic := congrArg Prod.snd oldMeta
  refine ⟨pair, ?_, publicKey.trans key⟩
  rw [← handle]
  exact found

end BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant.trusted_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant.trusted_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant.trusted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant.trusted_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant.metadata_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant.metadata_transport
