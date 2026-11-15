-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame
import BeaconcryptCore.Refinement.AdapterPublicServerEntryReceipt
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The literal corrected native Server accept callback factors through the same actual pin/authentication lookup prefix as the extracted public SDK. Only native Core continuations are rearranged; all original effects and full Native/platform poststates are retained. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceSemantics
open BeaconcryptCore.Computational
open AdapterPublicServerWorldLens (world world_run bind_world)
open AdapterPublicServerSourceLens (server_bind server_pure)
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m
attribute [local irreducible] RegistrationAuthenticationExecutor.begin

noncomputable def afterLookup (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (reserve : m Bool) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (checked : RustM (core.option.Option peer.RegistrationLookup)) : NativeM (RustM (Option Nat)) :=
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok .None => pure (.ok none)
  | .ok (.Some pending) => RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve)
        representation created packet pending.authenticated)

theorem after_pin (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : m Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (control : pqxdh.ServerState)
    (packet : registration.InitPacket) (pinReply : RegistrationNativeServerPinRecompute.PinReply) :
    (do let checked ← world (AdapterPublicServerAuthentication.afterPin
          (RegistrationNativePlatformAuthentication.native coins setup codec route verify edLaws) control packet pinReply)
        afterLookup (n := n) (mlSource := mlSource) coins setup checks reserve representation created packet checked) =
      RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks (StateT.lift reserve) route verify
          representation created packet pinReply) := by
  rw [AdapterPublicServerAuthenticationPrefix.after_pin_world]
  cases pinReply with
  | fail error | div => simp only [AdapterPublicServerAuthentication.afterPin, pure_bind, afterLookup,
      RegistrationNativePlatformSourceAccept.afterPin, server_pure]
  | ok optional => cases optional with
    | none => simp only [AdapterPublicServerAuthentication.afterPin, pure_bind, afterLookup,
        RegistrationNativePlatformSourceAccept.afterPin, server_pure]
    | some pin =>
      have actual : simulateQ
          (AdapterPublicServerAuthenticationNative.native (n := n) (mlSource := mlSource) coins setup codec route verify edLaws ∘ₛ AdapterInitAuthenticationStateful.abstractNative)
          (RegistrationAuthenticationExecutor.begin pin packet) = RegistrationNativePlatformExperiment.server
            (RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet) := by
        apply StateT.ext
        intro before
        exact AdapterPublicServerAuthenticationNative.begin_run coins setup codec route verify edLaws pin packet before
      simp only [AdapterPublicServerAuthentication.afterPin, RegistrationNativePlatformSourceAccept.afterPin,
        bind_map_left, server_bind]
      rw [actual]
      apply bind_congr
      intro authenticated
      cases authenticated with
      | fail error | div =>
        simp only [AdapterPublicServerAuthentication.observed,
          AdapterInitAuthenticationDriver.observe, afterLookup, server_pure]
        rfl
      | ok pair =>
        rcases pair with ⟨events, state⟩
        cases state <;> simp only [AdapterPublicServerAuthentication.observed, AdapterInitAuthenticationDriver.observe,
          AdapterInitAuthenticationStateful.stateOption, bind_tc_ok, PeerOwnership.registration_lookup_begin,
          afterLookup, server_pure]

theorem accept_run (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : m Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (do let checked ← world (AdapterPublicServerAuthenticationPrefix.program coins setup codec route verify edLaws
          before.server.control before.server.pin.binding before.server.pin.public_key packet)
        afterLookup coins setup checks reserve representation created packet checked).run before =
      (RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet)).run before := by
  unfold AdapterPublicServerAuthenticationPrefix.program
  rw [bind_world, bind_assoc]
  simp only [after_pin]
  unfold RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformSourceAccept.acceptWith
  rw [server_bind, StateT.run_bind, StateT.run_bind]
  have pinSame : (world (RegistrationNativePlatformInterpret.state coins
      (RegistrationNativeServerPinRecompute.native before.server.pin.binding before.server.pin.public_key))).run before =
      (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformSourceBuild.pin coins)).run before := by
    rw [world_run]
    unfold RegistrationNativePlatformExperiment.server RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformInterpret.state
    simp only [StateT.run, Functor.map_map]
    rfl
  rw [pinSame]

end BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceSemantics

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceSemantics.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceSemantics.after_pin

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceSemantics.accept_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceSemantics.accept_run
