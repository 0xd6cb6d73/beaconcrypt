-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget

/-! The actual routed pool-free authentication request retains the native global-World verifier receipt. Its broad public accepted tuple is derived from the real authenticated continuation, without an exact-bundle or session-uniqueness premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemAuthenticationReceipt
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationWorldAuthentication.begin

/-- The actual selected-accept source authentication callback supplies the exact public tuple used by original broad CE designation. -/
theorem accepted (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (packet : registration.InitPacket) (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (before after : RegistrationNativeKemServerState.State n mlSource × PqxdhLiveKemBirth.Pool KemSK)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationNativeKemParsedRouting.source setup checks wire route representation created credential
        (.inl (.inl (.inl (.authenticate packet))))).run before)) :
    PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) =
      some (RegistrationRootInput.identity authenticated.registration, RegistrationRootInput.keys authenticated.registration) := by
  simp only [RegistrationNativeKemParsedRouting.source, RegistrationNativeKemParsedRouting.other,
    RegistrationNativeKemInterface.source, RegistrationNativeKemRouting.publicAmbient,
    RegistrationNativeKemFrontendInterface.other, RegistrationNativeKemServerInterface.other,
    RegistrationNativeKemServerInterface.server, RegistrationServerNativeSource.authenticate,
    RegistrationServerNativeSource.sourceStep, RegistrationWorldServerFrontend.authenticate,
    RegistrationWorldServerFrontend.withWorld, RegistrationServerFrontendCompiler.restore,
    StateT.run, Functor.map_map, support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  rcases result with ⟨replyValue, afterWorld⟩
  have reply := congrArg Prod.fst equal
  change replyValue = .ok (events, .Accepted authenticated) at reply
  subst replyValue
  exact RegistrationNativeKemPublicTarget.world_accepted setup (RegistrationNativeWire.ledgerCodec wire)
    route mlSource.verify before.1.server.pin packet before.1.server.world.world.1 afterWorld events authenticated reached

end BeaconcryptCore.Computational.RegistrationNativeKemAuthenticationReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemAuthenticationReceipt.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemAuthenticationReceipt.accepted
