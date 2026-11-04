-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeGeneratedPath

/-! Actual native startup retains its generated joint identity and the literal initialized Server public key. This derives the source identity relation rather than assuming it for an arbitrary Created value. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStartupIdentity
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι}

private theorem sampled_support (work : ProbComp V) (before : PqxdhRecordLiftWorld.State n)
    (result : V × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.sampled work).run before)) : result.1 ∈ support work := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, called, returned⟩ := supported
  cases returned
  apply OracleComp.support_simulateQ_run'_subset PqxdhRecordLiftWorld.countCoin work before.primitive.1.uniform
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst called

/-- Successful initialized startup uses the same generated seed for both the exposed joint identity and the actual Server Ed25519 identity. -/
theorem identity (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    initial.created.publicIdentity = setup.joint.publicKeys initial.created.seed ∧
      initial.created.server.server.identity = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys initial.created.seed).ed25519 := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, constructorSupport, continued⟩ := supported
  have actual := sampled_support
    ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ())
    (PqxdhRecordLiftWorld.initial : PqxdhRecordLiftWorld.State n) constructed constructorSupport
  change (constructed.1.1, constructed.1.2) ∈ support _ at actual
  cases constructor : constructed.1.1 with
  | none => simp [constructor] at continued
  | some created =>
      rw [constructor] at actual
      obtain ⟨seed, literal, _imported⟩ := PqxdhLiveServerConstruction.construct_origin setup.joint ensureInit
        identityIndex serverKeyId none () constructed.1.2 created actual
      have fields : created.publicIdentity = setup.joint.publicKeys created.seed ∧
          created.server.server.identity = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys created.seed).ed25519 := by
        rw [literal]
        exact ⟨rfl, rfl⟩
      simp only [constructor, mem_support_bind_iff] at continued
      obtain ⟨generated, _sampled, continued⟩ := continued
      cases generation : generated.1 with
      | none => simp [generation] at continued
      | some credential =>
          simp only [generation, mem_support_bind_iff] at continued
          obtain ⟨initialized, _native, returned⟩ := continued
          cases native : initialized.1 with
          | fail error | div => simp [native] at returned
          | ok reply => cases reply with
            | none => simp [native] at returned
            | some state =>
                simp only [native, support_pure, Set.mem_singleton_iff, Option.some.injEq] at returned
                cases returned
                exact fields

end BeaconcryptCore.Computational.RegistrationNativeStartupIdentity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupIdentity.identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupIdentity.identity
