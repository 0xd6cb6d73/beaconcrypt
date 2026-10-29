-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider
import BeaconcryptCore.Computational.RegistrationNativeKemAuthenticationReceipt

/-! The uniform candidate provider retains the actual shared native ML/Ed authentication. Its accepted capability has the original publicly verified tuple, independently of private KEM phase, birth timing or candidate replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenAuthentication
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State implementation)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationWorldAuthentication.begin

/-- Actual successful authentication under the open candidate source gives the exact original public accepted tuple. -/
theorem accepted (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)
    (packet : registration.InitPacket) (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit) (before after : State n mlSource KemSK)
    (supported : (some (.ok (events, .Accepted authenticated)), after) ∈ support
      (((implementation setup checks wire route representation created credential selected pairs publicKey real
        (.inl (.inl (.inl (.authenticate packet))))).run).run before)) :
    PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) =
      some (RegistrationRootInput.identity authenticated.registration, RegistrationRootInput.keys authenticated.registration) := by
  rw [implementation, RegistrationNativeKemSwitchFacts.ambient_run, support_map] at supported
  obtain ⟨⟨reply, reachedContext⟩, called, returned⟩ := supported
  have resultEq := congrArg Prod.fst returned
  change some reply = some (.ok (events, .Accepted authenticated)) at resultEq
  cases Option.some.inj resultEq
  simp only [RegistrationNativeKemParsedRouting.other, RegistrationNativeKemRouting.publicAmbient,
    RegistrationNativeKemFrontendInterface.other, RegistrationNativeKemServerInterface.other,
    RegistrationNativeKemServerInterface.server, RegistrationServerNativeSource.authenticate,
    RegistrationServerNativeSource.sourceStep, RegistrationWorldServerFrontend.authenticate,
    RegistrationWorldServerFrontend.withWorld, RegistrationServerFrontendCompiler.restore,
    StateT.run, Functor.map_map, support_map] at called
  obtain ⟨⟨replyValue, afterWorld⟩, reached, equal⟩ := called
  have replyEq := congrArg Prod.fst equal
  change replyValue = .ok (events, .Accepted authenticated) at replyEq
  cases replyEq
  exact RegistrationNativeKemPublicTarget.world_accepted setup (RegistrationNativeWire.ledgerCodec wire)
    route mlSource.verify before.1.1.server.pin packet before.1.1.server.world.world.1 afterWorld events authenticated reached

end BeaconcryptCore.Computational.RegistrationNativeKemOpenAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenAuthentication.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenAuthentication.accepted
