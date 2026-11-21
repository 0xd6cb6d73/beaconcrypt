-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
import BeaconcryptCore.Computational.RegistrationServerNativeSource
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! Actual Server agreement changes its private role, request trace and uniform counter while retaining the live source Server identity, control, replay set and installed peer store. This derives the returned-object material frame through every successful or rejected continuation. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAgreementMaterial
open BeaconcryptCore.Computational
variable {n : Nat} {Auxiliary Value : Type}

theorem query_frame (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (before after : RegistrationWorldAgreement.State n Auxiliary)
    (reply : RegistrationAgreementExecutor.Spec.Range query)
    (supported : (reply, after) ∈ support ((RegistrationWorldAgreement.agreement source primitive query).run before)) :
    after.world.1.server = before.world.1.server := by
  simp only [RegistrationWorldAgreement.agreement, PqxdhRecordLiftWorld.sampled,
    StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨result, _called, returned⟩ := supported
  have same := congrArg Prod.snd returned
  cases same
  rfl

theorem program_frame (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Value)
    (before after : RegistrationWorldAgreement.State n Auxiliary) (reply : Value)
    (supported : (reply, after) ∈ support ((simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run before)) :
    after.world.1.server = before.world.1.server := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    cases supported.2
    rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, middle⟩, queried, continued⟩ := supported
    exact (ih answer middle after continued).trans (query_frame source primitive query before middle answer queried)

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {source : RegistrationNativeMldsa.Source} {KemSK ι : Type} {base : OracleSpec ι}

theorem agree (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (before after : RegistrationServerFrontendCompiler.State n)
    (related : AdapterPublicWrapperState.Server view views created credential self before)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (reply : RustM agreement.AgreementEffect)
    (supported : (reply, after) ∈ support ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)) :
    AdapterPublicWrapperState.Server view views created credential self after := by
  simp only [RegistrationServerNativeSource.agree, StateT.run, support_map] at supported
  obtain ⟨⟨value, world⟩, called, returned⟩ := supported
  have same := congrArg Prod.snd returned
  cases same
  rcases related.peers with ⟨records, reached, sender, identity, peers⟩
  have unchanged := program_frame setup.source (RegistrationServerRoleBackend.native setup checks representation created.seed)
    (RegistrationReplaySchedule.begin before.control authenticated before.consumed) before.world world value called
  exact ⟨related.identity, related.control, related.pinIdentity, related.pinIdentifier, related.pinMldsa, related.replay,
    records, unchanged.trans reached, sender, identity, peers⟩
end BeaconcryptCore.Refinement.AdapterPublicServerAgreementMaterial

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementMaterial.query_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementMaterial.query_frame

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementMaterial.program_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementMaterial.program_frame

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementMaterial.agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementMaterial.agree
