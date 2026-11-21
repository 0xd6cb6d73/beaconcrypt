-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Computational.PqxdhChallengeSecretRouting

/-! Resource receipts concern the original counted native source, independently of the operational uniform projection. Ordinary Server conversions and DH are deterministic; ephemeral creation pays all32 scalar-byte draws. External KEM keygen/encapsulation/decapsulation use their actual algorithm query-cap contracts. No evaluated-distribution equality is used as a resource certificate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSourceBills
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemInterface (OtherRequest OtherSpec)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

structure Caps (setup : Setup base KemSK) where
  keygen : Nat
  encapsulate : Nat
  decapsulate : Nat
  keygen_bound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound keygen
  encapsulate_bound : ∀ key,
    (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)).IsTotalQueryBound encapsulate
  decapsulate_bound : ∀ secret ciphertext,
    (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.decaps secret ciphertext)).IsTotalQueryBound decapsulate

/-- The functional-decapsulation interface already used by the native KEM hop derives its zero-draw bill. -/
def functionalCaps (setup : Setup base KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (keygen encapsulate : Nat)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound keygen)
    (encapsulationBound : ∀ key, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.encaps key)).IsTotalQueryBound encapsulate) : Caps setup :=
  ⟨keygen, encapsulate, 0, keygenBound, encapsulationBound, fun secret ciphertext => by
    rw [functional.exact, simulateQ_pure]
    trivial⟩

def otherCost : OtherRequest → Nat
  | .generate _ => 32
  | _ => 0

/-- The actual ordinary Server primitive backend pays only its32-byte ephemeral draw; all optional conversion/DH refusals are deterministic. -/
theorem other_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : OtherRequest) (before : RegistrationServerRoleBackend.State) :
    ((RegistrationNativeKemBackend.serverOther setup checks representation seed query).run before).IsTotalQueryBound (otherCost query) := by
  cases query with
  | convertPublic key => simp [RegistrationNativeKemBackend.serverOther, OtherRequest.primitive,
      RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, IsTotalQueryBound, otherCost]
  | convertSecret role => cases role <;> simp [RegistrationNativeKemBackend.serverOther, OtherRequest.primitive,
      RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, IsTotalQueryBound, otherCost]
  | generate role =>
      cases role
      simp only [RegistrationNativeKemBackend.serverOther, OtherRequest.primitive,
        RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend,
        PqxdhServerAuthExperiment.generateEphemeral, StateT.run, bind_pure_comp,
        IsTotalQueryBound, isQueryBound_map_iff, otherCost]
      exact PqxdhJointIdentity.sampleSeed_uniform_bound
  | dh request =>
      cases role : request.secret_role <;>
        simp [RegistrationNativeKemBackend.serverOther, OtherRequest.primitive, RegistrationServerRoleBackend.native,
          RegistrationServerRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, IsTotalQueryBound, role, otherCost]

def cost (setup : Setup base KemSK) (caps : Caps setup) :
    (RegistrationNativeKemInterface.Spec OtherSpec KemSK).Domain → Nat
  | .inl query => otherCost query
  | .inr (.inl .create) => caps.keygen
  | .inr (.inl (.decapsulate _ _)) => caps.decapsulate
  | .inr (.inl (.reveal _)) => 0
  | .inr (.inr _) => caps.encapsulate

/-- Every complete native lower callback has its actual primitive draw cap, including missing generated handles and rejected decapsulation. -/
theorem source_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (seed : PqxdhJointIdentity.IdentitySeed) (caps : Caps setup)
    (query : (RegistrationNativeKemInterface.Spec OtherSpec KemSK).Domain)
    (before : RegistrationServerRoleBackend.State × PqxdhLiveKemBirth.Pool KemSK) :
    ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem OtherSpec
      (RegistrationNativeKemBackend.serverOther setup checks representation seed) query).run before).IsTotalQueryBound
        (cost setup caps query) := by
  rcases query with query | (query | key)
  · simpa only [RegistrationNativeKemInterface.source, StateT.run, IsTotalQueryBound, isQueryBound_map_iff, cost] using
      other_bound setup checks representation seed query before.1
  · cases query with
    | create => simpa only [RegistrationNativeKemInterface.source, StateT.run,
        PqxdhLiveKemBirth.poolImpl, IsTotalQueryBound, isQueryBound_map_iff, cost] using caps.keygen_bound
    | decapsulate handle ciphertext =>
        cases found : before.2.keys[handle]? with
        | none => simp [RegistrationNativeKemInterface.source, PqxdhLiveKemBirth.poolImpl, StateT.run, IsTotalQueryBound, found, cost]
        | some pair => simpa only [RegistrationNativeKemInterface.source, StateT.run,
            PqxdhLiveKemBirth.poolImpl, found, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, cost] using
            caps.decapsulate_bound pair.2 ciphertext
    | reveal handle => simp [RegistrationNativeKemInterface.source, PqxdhLiveKemBirth.poolImpl, StateT.run, IsTotalQueryBound, cost]
  · simpa only [RegistrationNativeKemInterface.source, StateT.run_lift, bind_pure_comp,
      IsTotalQueryBound, isQueryBound_map_iff, cost] using caps.encapsulate_bound key

/-- The original deployment's retained uniform bill is bounded before opening or projecting the selected native KEM call. -/
theorem trusted_uniform (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (caps : Caps setup)
    (query : (RegistrationNativeKemInterface.Spec OtherSpec KemSK).Domain)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource)
    (reply : (RegistrationNativeKemInterface.Spec OtherSpec KemSK).Range query)
    (supported : (reply, after) ∈ support
      ((RegistrationNativeExperiment.trusted setup checks representation created mlSource (.inr query)).run before)) :
    after.server.world.world.1.primitive.1.uniform ≤
      before.server.world.world.1.primitive.1.uniform + cost setup caps query := by
  simp only [RegistrationNativeExperiment.trusted, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨result, sampled, returned⟩ := supported
  cases returned
  exact RegistrationNativeKemWorldUniform.sampled_bound _ _
    (source_bound setup checks representation created.seed caps query (before.server.world.auxiliary, before.pool))
    before.server.world.world.1 result sampled

end BeaconcryptCore.Computational.RegistrationNativeKemSourceBills

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSourceBills.other_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSourceBills.other_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSourceBills.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSourceBills.source_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSourceBills.trusted_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSourceBills.trusted_uniform
