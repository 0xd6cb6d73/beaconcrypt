-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftWorld
import BeaconcryptCore.Computational.RegistrationRecordBinding

/-! The actual extracted Init authentication controller is an open client of the global record world. Every transcript and fingerprint hash uses that world's instrumented shared cache. Erasing instrumentation gives the concrete native callback interpretation, so its accepted-source receipts apply to the reached global cache. This adapter does not identify the legacy registration/KEM interpreter with the native first-record completion controller. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 2048

namespace BeaconcryptCore.Computational.RegistrationWorldAuthentication

open PqxdhRecordLiftInterface
open PqxdhServerAuthExperiment (Setup Codec)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow (Event)

variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

attribute [local irreducible] RegistrationAuthenticationExecutor.execute registration.begin_init_authentication

def project (world : PqxdhRecordLiftWorld.State n) : RawCtxSharedPrimitive.SharedState Unit :=
  ((), world.primitive.2)

/-- Verification consumes every actual native operand; only hashes need a World effect. -/
def callbacks (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (OracleComp (WorldSpec n))
  | .hash request => do
      let digest ← (WorldSpec n).query (.inr (.inl (.inr (.hash (hashBytes request)))))
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .mldsa request => pure (RegistrationAuthenticationShared.verifyMldsa verify request)
  | .ed25519 request => pure (RegistrationAuthenticationShared.verifyEd25519 crypto request)

noncomputable def implementation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  PqxdhRecordLiftWorld.handler setup codec route ∘ₛ callbacks setup.source.crypto verify

def program (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    OracleComp (WorldSpec n) (RustM (List Event × registration.InitAuthentication)) :=
  simulateQ (callbacks crypto verify) (RegistrationAuthenticationExecutor.begin pin packet)

noncomputable def begin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    StateT (PqxdhRecordLiftWorld.State n) ProbComp (RustM (List Event × registration.InitAuthentication)) :=
  simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
    (program setup.source.crypto verify pin packet)

theorem hash_project (bytes : Pqxdh.Bytes) (state : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$>
      (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run state =
      (fun result => (result.1, ((), result.2))) <$>
        (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.primitive.2 := by
  have same := congrArg (fun work => (fun result => (result.1, ((), result.2))) <$> work)
    (PqxdhRecordLiftWorld.countCoin_forget
      ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.primitive.2) state.primitive.1.uniform)
  simpa only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability,
    PqxdhRecordLiftWorld.sampled, PqxdhRecordLiftWorld.chargeEffect, StateT.run,
    bind_pure_comp, Functor.map_map, project, Prod.map, id_eq] using same

theorem callbacks_project (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Spec.Domain) (state : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$> (implementation setup codec route verify query).run state =
      (RegistrationAuthenticationShared.implementation setup.source.crypto verify codec.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source) query).run (project state) := by
  cases query with
  | hash request =>
      rw [RegistrationAuthenticationShared.hash_exact]
      have same := congrArg (fun work =>
        (fun result =>
          (core.option.Option.Some (RegistrationAuthenticationShared.digestArray result.1), result.2)) <$> work)
        (hash_project (hashBytes request) state)
      simp only [implementation, QueryImpl.apply_compose, callbacks, bind_pure_comp,
        simulateQ_map, simulateQ_spec_query, PqxdhRecordLiftWorld.handler, StateT.run_map]
      simp only [Functor.map_map, Prod.map, id_eq, project] at same ⊢
      convert same using 1
      rfl
  | mldsa request =>
      rfl
  | ed25519 request =>
      rfl

/-- The entire actual controller uses the same cache as global record operations. -/
theorem begin_project (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (state : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$> (begin setup codec route verify pin packet).run state =
      (RegistrationAuthenticationShared.begin setup.source.crypto verify codec.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source) pin packet).run (project state) := by
  unfold begin program
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (implementation setup codec route verify)
    (RegistrationAuthenticationShared.implementation setup.source.crypto verify codec.frameWrite
      (RawCtxSourceHkdf.kdfImpl setup.source)) project
    (callbacks_project setup codec route verify)
    (RegistrationAuthenticationExecutor.begin pin packet) state

theorem begin_native_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : PqxdhRecordLiftWorld.State n) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((begin setup codec route verify pin packet).run before)) :
    (.ok (events, .Accepted authenticated), project after) ∈ support
      ((RegistrationAuthenticationShared.begin setup.source.crypto verify codec.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source) pin packet).run (project before)) := by
  rw [← begin_project, support_map]
  exact Set.mem_image_of_mem (Prod.map id project) supported

/-- Installed AD retains the selected keys and fingerprints from the reached global cache. -/
theorem begin_associated_data (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : PqxdhRecordLiftWorld.State n) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((begin setup codec route verify pin packet).run before))
    (server : RawCtxServerRouting.Identity) :
    (RegistrationRecordBinding.ofRegistration authenticated.binding).associatedBytes server =
      BeaconcryptCore.Refinement.SessionBinding.boundAssociatedData
        (absBytes pin.binding.identity_public_key) (absBytes authenticated.binding.beacon_identity_public_key)
        (MldsaSharedAuthentication.cacheHash after.primitive.2 (absBytes pin.public_key))
        (MldsaSharedAuthentication.cacheHash after.primitive.2 (absBytes packet.mldsa_public_key)) :=
  RegistrationRecordBinding.accepted_selected_associated_data setup.source.crypto verify codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) pin packet (project before) (project after) events authenticated
    (begin_native_support setup codec route verify pin packet before after events authenticated supported) server

end BeaconcryptCore.Computational.RegistrationWorldAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAuthentication.hash_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAuthentication.hash_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAuthentication.callbacks_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAuthentication.callbacks_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAuthentication.begin_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAuthentication.begin_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAuthentication.begin_native_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAuthentication.begin_native_support

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAuthentication.begin_associated_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAuthentication.begin_associated_data
