-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerWorldLens
import BeaconcryptCore.Refinement.AdapterPublicServerAuthentication
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual split Ed parse/open callbacks and shared-cache authentication hashes implement the native Server authentication in the complete Native/platform state. Only individual Ed functional contracts are used; invalid-key rejection and every original authentication operand remain in the program. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationNative
open BeaconcryptCore.Computational
open AdapterPublicServerWorldLens (world world_run simulate_world)
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK I Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m

noncomputable def native (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto) :
    QueryImpl AdapterInitAuthenticationStateful.NativeSpec NativeM :=
  fun query => world (RegistrationNativePlatformAuthentication.native coins setup codec route verify edLaws query)

theorem abstract_query (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    (native (n := n) (mlSource := mlSource) coins setup codec route verify edLaws ∘ₛ AdapterInitAuthenticationStateful.abstractNative) query =
      world (RegistrationNativePlatformAuthentication.core coins setup codec route verify query) := by
  rw [QueryImpl.apply_compose]
  unfold native
  rw [← simulate_world]
  change world ((RegistrationNativePlatformAuthentication.native (n := n) coins setup codec route verify edLaws ∘ₛ
    AdapterInitAuthenticationStateful.abstractNative) query) = _
  rw [RegistrationNativePlatformAuthentication.abstract_query]

theorem begin_run (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (simulateQ (native coins setup codec route verify edLaws ∘ₛ AdapterInitAuthenticationStateful.abstractNative)
      (RegistrationAuthenticationExecutor.begin pin packet)).run before =
      (RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet)).run before := by
  have callbacks : native (n := n) (mlSource := mlSource) coins setup codec route verify edLaws ∘ₛ AdapterInitAuthenticationStateful.abstractNative =
      fun query => world (RegistrationNativePlatformAuthentication.core coins setup codec route verify query) := by
    funext query
    exact abstract_query coins setup codec route verify edLaws query
  rw [callbacks, ← simulate_world, world_run]
  have interpreted := RegistrationNativePlatformInterpret.state_simulate coins
    (RegistrationWorldAuthentication.implementation (n := n) setup codec route verify)
    (RegistrationAuthenticationExecutor.begin pin packet)
  have ran := congrArg (fun action => action.run before.server.world.world.1) interpreted
  change simulateQ coins ((simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify)
    (RegistrationAuthenticationExecutor.begin pin packet)).run before.server.world.world.1) =
      (simulateQ (RegistrationNativePlatformAuthentication.core coins setup codec route verify)
        (RegistrationAuthenticationExecutor.begin pin packet)).run before.server.world.world.1 at ran
  rw [← ran]
  unfold RegistrationNativePlatformExperiment.server RegistrationNativePlatformSourceAccept.authenticate
    RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program RegistrationWorldAuthentication.implementation
  simp only [StateT.run, Functor.map_map]
  rw [← QueryImpl.simulateQ_compose]
  rfl

end BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationNative.abstract_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationNative.abstract_query

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationNative.begin_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationNative.begin_run
