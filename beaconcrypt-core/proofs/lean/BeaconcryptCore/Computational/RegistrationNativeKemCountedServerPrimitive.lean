-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedTrusted

/-! Actual Server KEM getters are represented by counted indexed leaves; all non-KEM operations keep the actual native role and source coin costs. These source-normalization equations expose the free primitive tree for resource proofs. Complete Server agreement and acceptance evaluator transport are separate. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedServerPrimitive
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemServerState (State)
open RegistrationNativeKemCountedProgram (Spec)
open RegistrationAgreementShared (PrimitiveSpec)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

noncomputable def program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl PrimitiveSpec (StateT (State n source) (OracleComp (Spec KemSK))) := fun query =>
  simulateQ (fun request => RegistrationNativeKemCountedTrusted.implementation setup checks representation created (.inr request))
    (RegistrationNativeKemInterface.server checks query)

/-- The actual Server backend never invokes the private recipient decapsulation service. -/
theorem decapsulate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (ciphertext : core.option.Option (Std.Array U8 1088#usize)) :
    program (n := n) (source := source) setup checks representation created (.decapsulate ciphertext) = pure .None := by
  simp only [program, RegistrationNativeKemInterface.server, simulateQ_pure]

/-- Missing public input invokes no KEM leaf. -/
theorem missing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    program (n := n) (source := source) setup checks representation created (.encapsulate .None) = pure .None := by
  simp only [program, RegistrationNativeKemInterface.server, simulateQ_pure]

/-- A checked source encapsulation invokes exactly the indexed counted leaf and retains the original typed reply. -/
theorem encapsulate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (key : Std.Array U8 1184#usize) :
    program (n := n) (source := source) setup checks representation created (.encapsulate (.Some key)) =
      if checks.kemKey (RegistrationRootInput.pqKey key) then
        (fun result => .Some (PqxdhAcceptedRegistration.ciphertextArray result.1, PqxdhRootTableInitialization.rootArray result.2)) <$>
          RegistrationNativeKemCountedTrusted.world (RegistrationNativeKemCountedProgram.call (.inr (RegistrationRootInput.pqKey key)))
      else pure .None := by
  by_cases valid : checks.kemKey (RegistrationRootInput.pqKey key) = true
  · simp only [program, RegistrationNativeKemInterface.server, valid, ite_true, RegistrationNativeKemInterface.encapsulate,
      simulateQ_map, simulateQ_spec_query, RegistrationNativeKemCountedTrusted.implementation]
    rfl
  · simp only [program, RegistrationNativeKemInterface.server, valid, Bool.false_eq_true, ite_false, simulateQ_pure]

noncomputable def core (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (State n source) (OracleComp (Spec KemSK)))
  | .convertPublic key => program setup checks representation created (.convertPublic key)
  | .convertSecret role => program setup checks representation created (.convertSecret role)
  | .generate role => program setup checks representation created (.generate role)
  | .encapsulate key => program setup checks representation created (.encapsulate key)
  | .decapsulate ciphertext => program setup checks representation created (.decapsulate ciphertext)
  | .dh request => program setup checks representation created (.dh request)
  | .root request => pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request))

noncomputable def agreement (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (State n source) (OracleComp (Spec KemSK))) := fun query => do
  modify fun before => { before with server := { before.server with world := { before.server.world with
    requests := before.server.world.requests ++ RegistrationWorldAgreement.recorded query } } }
  core setup checks representation created query

noncomputable def agree (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (authenticated : registration.AuthenticatedInit) :
    StateT (State n source) (OracleComp (Spec KemSK)) (RustM agreement.AgreementEffect) := do
  let before ← get
  simulateQ (agreement setup checks representation created)
    (RegistrationReplaySchedule.begin before.server.control authenticated before.server.consumed)

end BeaconcryptCore.Computational.RegistrationNativeKemCountedServerPrimitive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerPrimitive.decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerPrimitive.decapsulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerPrimitive.missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerPrimitive.missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerPrimitive.encapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerPrimitive.encapsulate
