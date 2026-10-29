-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemServerInterface

/-! Actual native Server primitive continuations factor through the exposed KEM getter and the separate private indexed service. The exact output retains every source coordinate and the entire private pool; only the stated native uniform accounting projection is applied to the client state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemServerPrimitive
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeKemServerState (State mask)
open RegistrationNativeKemServerInterface (withRole)
variable {ι KemSK Reader Response Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

private def embed (before : State n mlSource)
    (state : RegistrationServerRoleBackend.State × PqxdhLiveKemBirth.Pool KemSK) :=
  (withRole (mask before) state.1, state.2)

private theorem lift_query (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : State n mlSource)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (state : RegistrationServerRoleBackend.State × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id (embed before) <$>
        (RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
          (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) query).run state =
      (simulateQ (RegistrationNativeKemServerInterface.source setup codec checks route verify representation created)
        (RegistrationNativeKemServerInterface.lift query)).run (embed before state) := by
  rcases query with query | (query | key)
  · simp only [RegistrationNativeKemServerInterface.lift, simulateQ_spec_query,
      RegistrationNativeKemServerInterface.source, RegistrationNativeKemInterface.source,
      RegistrationNativeKemServerInterface.other, StateT.run, Functor.map_map, Prod.map, id_eq,
      embed, withRole, mask, RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask]
  · simp only [RegistrationNativeKemServerInterface.lift, simulateQ_spec_query,
      RegistrationNativeKemServerInterface.source, RegistrationNativeKemInterface.source,
      StateT.run, Functor.map_map, Prod.map, id_eq, embed]
  · simp only [RegistrationNativeKemServerInterface.lift, simulateQ_spec_query,
      RegistrationNativeKemServerInterface.source, RegistrationNativeKemInterface.source,
      StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map, id_eq, embed]

private theorem lift_program (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : State n mlSource)
    (work : OracleComp (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK) Value)
    (state : RegistrationServerRoleBackend.State × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id (embed before) <$>
        (simulateQ (RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
          (RegistrationNativeKemBackend.serverOther setup checks representation created.seed)) work).run state =
      (simulateQ (RegistrationNativeKemServerInterface.source setup codec checks route verify representation created)
        (simulateQ RegistrationNativeKemServerInterface.lift work)).run (embed before state) := by
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (embed before)
    (lift_query setup codec checks route verify representation created before) work state

private theorem backend_full (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (seed : PqxdhJointIdentity.IdentitySeed)
    (work : OracleComp RegistrationAgreementShared.PrimitiveSpec Value)
    (role : RegistrationServerRoleBackend.State) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (RegistrationNativeKemBackend.server setup checks representation seed) work).run (role, pool) =
      (fun result => (result.1, (result.2, pool))) <$>
        (simulateQ (RegistrationServerRoleBackend.native setup checks representation seed) work).run role := by
  induction work using OracleComp.inductionOn generalizing role with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        RegistrationNativeKemBackend.server_query, bind_map_left, map_bind, ih]

/-- A complete arbitrary native primitive continuation has its actual outputs and role effects, with the entire private pool unchanged and every other projected client coordinate retained. -/
theorem primitive_program (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp RegistrationAgreementShared.PrimitiveSpec Value)
    (before : State n mlSource) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (RegistrationNativeKemServerInterface.source setup codec checks route verify representation created)
      (simulateQ (RegistrationNativeKemServerInterface.primitive checks) work)).run (mask before, pool) =
      (fun result => (result.1, (withRole (mask before) result.2, pool))) <$>
        (simulateQ (RegistrationServerRoleBackend.native setup checks representation created.seed) work).run
          before.server.world.auxiliary := by
  have law := lift_program setup codec checks route verify representation created before
    (simulateQ (RegistrationNativeKemInterface.server checks) work) (before.server.world.auxiliary, pool)
  rw [← QueryImpl.simulateQ_compose] at law
  change Prod.map id (embed before) <$>
      (simulateQ (RegistrationNativeKemBackend.server setup checks representation created.seed) work).run
        (before.server.world.auxiliary, pool) = _ at law
  rw [backend_full, Functor.map_map] at law
  simpa only [RegistrationNativeKemServerInterface.primitive, QueryImpl.simulateQ_compose,
    embed, withRole, mask, RegistrationNativeKemServerState.maskServer,
    RegistrationNativeKemWorldUniform.mask, Prod.map, id_eq] using law.symm

end BeaconcryptCore.Computational.RegistrationNativeKemServerPrimitive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerPrimitive.primitive_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerPrimitive.primitive_program
