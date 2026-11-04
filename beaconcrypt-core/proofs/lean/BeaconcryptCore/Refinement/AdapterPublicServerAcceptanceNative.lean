-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceSemantics
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The complete original extracted public Server acceptance and the literal corrected native acceptance are projections of the same source pin/authentication/lookup/allocation/agreement run. Concrete hostile-input decoding is retained, Fresh admission is derived, and the full caller RNG/private receipt remains in the source witness. Primitive assumptions name only individual functional/sampling operations and standard storage/allocation footprints. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceNative
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerReservationNative (project AllocationReply)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK I Reader Response PlatformState : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource (StateT PlatformState ProbComp)
attribute [local irreducible] RegistrationAuthenticationExecutor.begin
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]

noncomputable def accept (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : (StateT PlatformState ProbComp) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (input : Slice U8) : NativeM (RustM (Option Nat)) :=
  match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none => pure (.ok none)
  | some packet => RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet)

theorem coupled {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀ key, (@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (membershipOperation : ∀ identifier, AdapterPublicServerReplayPrefix.contains
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp))
      self.consumed_registrations identifier = pure (views.replay self.consumed_registrations identifier))
    (allocated : (StateT PlatformState ProbComp) AllocationReply)
    (allocationOperation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views self.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := (StateT PlatformState ProbComp)) views {self with consumed_registrations := history}) :
    project view before <$>
      ((AdapterPublicServerEntryReceipt.program coins setup codec route verify edLaws recording writer generator self input rng).run before) =
      RustM.ok <$> (accept coins setup codec checks (AdapterPublicServerSourceLens.admitted <$> allocated)
        route verify model.representation created input).run before := by
  rw [AdapterPublicServerEntryReceipt.source_joint coins setup codec route verify edLaws recording writer generator self input rng
    view views created credential before related edGetter mlGetter]
  unfold accept
  cases decoded : RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none => simp only [map_pure, StateT.run_pure, project]
  | some packet =>
    simp only []
    rw [← AdapterPublicServerAcceptanceSemantics.accept_run coins setup codec checks
      (AdapterPublicServerSourceLens.admitted <$> allocated) route verify edLaws model.representation created packet before]
    rw [related.control]
    simp only [StateT.run_bind, map_bind]
    apply StateT.ext
    intro previous
    simp only [StateT.run_bind, StateT.run_map]
    apply OracleComp.bind_congr_of_forall_mem_support
    rintro ⟨⟨lookup, currentNative⟩, between⟩ supported
    rw [AdapterPublicServerWorldLens.world_run] at supported
    simp only [StateT.run_map, support_map] at supported
    obtain ⟨⟨⟨looked, world⟩, nextExternal⟩, called, returned⟩ := supported
    have stateEq := congrArg (fun result => result.1.2) returned
    have replyEq := congrArg (fun result => result.1.1) returned
    have externalEq := congrArg Prod.snd returned
    cases replyEq
    cases externalEq
    change AdapterPublicAgreementNativeWorldMap.putWorld before world = currentNative at stateEq
    subst currentNative
    have prefixFrame := AdapterPublicServerPrefixFrame.program_server coins setup codec route verify edLaws
      before.server.control before.server.pin.binding before.server.pin.public_key packet
      before.server.world.world.1 world lookup previous between called
    have currentMaterial := AdapterPublicServerPrefixMaterial.related_world view views created credential self before related world prefixFrame
    cases lookup with
    | fail error | div => simp only [StateT.run_pure, map_pure, project, AdapterPublicServerAcceptanceSemantics.afterLookup]
    | ok optional => cases optional with
      | none => simp only [StateT.run_pure, map_pure, project, AdapterPublicServerAcceptanceSemantics.afterLookup]
      | some pending =>
        have control := AdapterPublicServerPrefixFrame.program_lookup coins setup codec route verify edLaws
          before.server.control before.server.pin.binding before.server.pin.public_key packet
          before.server.world.world.1 world pending previous between called
        have stage := AdapterPublicServerLookupNative.coupled coins generator setup checks view views model entropy
          created credential self pending rng packet (AdapterPublicAgreementNativeWorldMap.putWorld before world)
          currentMaterial control (membershipOperation _) allocated allocationOperation footprint insertion
        have baseSame : project (R := R) view (AdapterPublicAgreementNativeWorldMap.putWorld before world) = project view before := by
          funext result
          exact AdapterPublicServerPrefixMaterial.project_world view before world result
        rw [baseSame] at stage
        simpa only [StateT.run_map, AdapterPublicServerAcceptanceSemantics.afterLookup] using
          congrArg (fun action => action.run between) stage

end BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceNative.coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceNative.coupled
