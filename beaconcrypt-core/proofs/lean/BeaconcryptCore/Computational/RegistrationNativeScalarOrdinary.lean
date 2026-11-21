-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarCreate
import BeaconcryptCore.Computational.RegistrationNativeKemRoster

/-! After the selected owner has been created the eager native source is exactly the ordinary source. The actual owner-roster prefix theorem derives the persistent index ordering for every adaptive continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarOrdinary
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every ordinary source step keeps the old roster length as a lower bound, without any key-injectivity assumption. -/
theorem monotone (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (query : TypedSpec.Domain) (before : RegistrationNativeExperiment.State n KemSK source)
    (result : TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation
      created source credential query).run before)) : before.beacons.length ≤ result.2.beacons.length := by
  obtain ⟨tail, same⟩ := RegistrationNativeKemRoster.typed_prefix setup checks wire route representation created credential query before result supported
  have sizes := congrArg List.length same
  simp only [List.length_map, List.length_append] at sizes
  omega

/-- Outside the selected roster index, every literal typed callback is the original native callback. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (query : TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source) (ordinary : before.beacons.length ≠ selected) :
    (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar query).run before =
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before := by
  cases query with
  | inl coin => rfl
  | inr command =>
      cases command with
      | create edPin mlPin keyId =>
        change (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId)).run before =
            (RegistrationNativeExperiment.beacon setup checks representation created
              (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before
        unfold RegistrationNativeExperiment.beacon
        have localEq := RegistrationNativeScalarEagerLaws.ordinary_create (n := n) setup source selected scalar edPin mlPin keyId
          before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) ordinary
        dsimp only [StateT.run] at localEq ⊢
        rw [localEq]
      | bundle _ | accept _ | build _ _ | finish _ _ | hmac _ _ | hash _
      | serverSend _ _ | serverRaw _ | beaconSend _ _ | beaconRaw _ _ => rfl

/-- Once the selected roster position exists, every complete adaptive eager-source continuation is exactly the ordinary native source. -/
theorem done_program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (work : OracleComp TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (done : selected < before.beacons.length) :
    (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) work).run before =
      (simulateQ (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [handler setup checks wire route representation created credential selected scalar query before (by omega)]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro result supported
      exact ih result.1 result.2 (by have kept := monotone setup checks wire route representation created credential query before result supported; omega)

end BeaconcryptCore.Computational.RegistrationNativeScalarOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarOrdinary.monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarOrdinary.monotone
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarOrdinary.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarOrdinary.handler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarOrdinary.done_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarOrdinary.done_program
