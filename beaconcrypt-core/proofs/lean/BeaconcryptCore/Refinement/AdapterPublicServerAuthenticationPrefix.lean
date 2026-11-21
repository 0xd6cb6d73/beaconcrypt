-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual Server pin recomputation and mandatory Init authentication form one shared World prefix. Its complete reply is the source-owned lookup capability; rejected inputs remain explicit before replay lookup or reservation. The individual Ed contracts preserve the exact parse/open order and invalid-key result. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix
open BeaconcryptCore.Computational
open AdapterPublicServerWorldLens (world world_run pure_world bind_world simulate_world)
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "WorldM" => StateT (PqxdhRecordLiftWorld.State n) m
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m
attribute [local irreducible] RegistrationAuthenticationExecutor.begin

omit ed in
theorem core_run (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ (RegistrationNativePlatformAuthentication.core coins setup codec route verify)
      (RegistrationAuthenticationExecutor.begin pin packet)).run before =
      simulateQ coins ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before) := by
  have interpreted := RegistrationNativePlatformInterpret.state_simulate coins
    (RegistrationWorldAuthentication.implementation (n := n) setup codec route verify)
    (RegistrationAuthenticationExecutor.begin pin packet)
  have ran := congrArg (fun action => action.run before) interpreted
  change simulateQ coins ((simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify)
    (RegistrationAuthenticationExecutor.begin pin packet)).run before) =
      (simulateQ (RegistrationNativePlatformAuthentication.core coins setup codec route verify)
        (RegistrationAuthenticationExecutor.begin pin packet)).run before at ran
  rw [← ran]
  unfold RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program RegistrationWorldAuthentication.implementation
  rw [← QueryImpl.simulateQ_compose]

theorem after_pin_run (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (pinReply : RegistrationNativeServerPinRecompute.PinReply) (before : PqxdhRecordLiftWorld.State n) :
    (AdapterPublicServerAuthentication.afterPin
      (RegistrationNativePlatformAuthentication.native coins setup codec route verify edLaws) control packet pinReply).run before =
      match pinReply with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok .None => pure (.ok .None, before)
      | .ok (.Some pin) => (fun result => (AdapterPublicServerAuthentication.observed control result.1, result.2)) <$>
          simulateQ coins ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before) := by
  cases pinReply with
  | fail error | div => rfl
  | ok pin => cases pin with
    | none => rfl
    | some pin =>
      have callbacks : RegistrationNativePlatformAuthentication.native (n := n) coins setup codec route verify edLaws ∘ₛ AdapterInitAuthenticationStateful.abstractNative =
          RegistrationNativePlatformAuthentication.core coins setup codec route verify := by
        funext query
        exact RegistrationNativePlatformAuthentication.abstract_query coins setup codec route verify edLaws query
      simp only [AdapterPublicServerAuthentication.afterPin, StateT.run_map]
      rw [callbacks, core_run]

noncomputable def program (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (packet : registration.InitPacket) : WorldM (RustM (core.option.Option peer.RegistrationLookup)) := do
  let pinReply ← RegistrationNativePlatformInterpret.state coins (RegistrationNativeServerPinRecompute.native binding publicKey)
  AdapterPublicServerAuthentication.afterPin
    (RegistrationNativePlatformAuthentication.native coins setup codec route verify edLaws) control packet pinReply

omit ed in
private theorem map_world {A B : Type} (function : A → B) (work : WorldM A) :
    world (KemSK := KemSK) (mlSource := mlSource) (function <$> work) = function <$> world work := by
  apply StateT.ext
  intro before
  rw [world_run, StateT.run_map, StateT.run_map, world_run]
  simp only [Functor.map_map]

theorem after_pin_world (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (pinReply : RegistrationNativeServerPinRecompute.PinReply) :
    world (n := n) (KemSK := KemSK) (mlSource := mlSource)
      (AdapterPublicServerAuthentication.afterPin
        (RegistrationNativePlatformAuthentication.native coins setup codec route verify edLaws) control packet pinReply) =
      AdapterPublicServerAuthentication.afterPin
        (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws) control packet pinReply := by
  cases pinReply with
  | fail error | div => exact pure_world _
  | ok pin => cases pin with
    | none => exact pure_world _
    | some pin =>
      unfold AdapterPublicServerAuthentication.afterPin
      simp only []
      rw [map_world]
      simp only [QueryImpl.simulateQ_compose]
      unfold AdapterPublicServerAuthenticationNative.native
      rw [← simulate_world]


variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [localOps : AdapterPublicWrapperRequestMonad.LocalOperations
  (AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations
  (AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]

theorem source {E : Type} (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey)) :
    letI : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT NativeM) :=
      AdapterPublicWrapperChildren.children
        (AdapterPublicWrapperChildNative.normalAuthentication
          (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
    letI : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT NativeM) := AdapterPublicConcreteCodecs.codecs
    ((AdapterPublicServerAcceptBody.authenticate (m := NativeM) self input).run).run before =
      match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
      | none => pure (.ok .None, before)
      | some packet => (world (program coins setup codec route verify edLaws self.control before.server.pin.binding before.server.pin.public_key packet)).run before := by
  let : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT NativeM) :=
    AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.normalAuthentication
        (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
  let : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT NativeM) := AdapterPublicConcreteCodecs.codecs
  rw [AdapterPublicServerAuthentication.authenticate]
  cases decoded : RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none => rfl
  | some packet =>
    simp only []
    unfold program
    rw [bind_world, StateT.run_bind, StateT.run_bind]
    rw [AdapterPublicServerPinGlobal.source coins view views created credential self before related edGetter mlGetter]
    have pinSame : (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformSourceBuild.pin coins)).run before =
        (world (RegistrationNativePlatformInterpret.state coins
          (RegistrationNativeServerPinRecompute.native before.server.pin.binding before.server.pin.public_key))).run before := by
      rw [world_run]
      unfold RegistrationNativePlatformExperiment.server RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformInterpret.state
      simp only [StateT.run, Functor.map_map]
      rfl
    rw [pinSame]
    apply bind_congr
    rintro ⟨pinReply, current⟩
    exact congrArg (fun action => action.run current)
      (after_pin_world coins setup codec route verify edLaws self.control packet pinReply).symm


end BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix.core_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix.core_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix.after_pin_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix.after_pin_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix.after_pin_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix.after_pin_world

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix.source
