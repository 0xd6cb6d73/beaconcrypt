-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldAuthentication

/-! Incoming mandatory native authentication is an open EnvEffects program. Its actual ML operands and attached Ed25519 message remain local verification inputs; every transcript and fingerprint hash uses the actual record World cache. The compiler has no World in its environment state and no supplied verdict, digest or simulation law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationAuthenticationCompiler
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open PqxdhServerAuthExperiment (Setup Codec)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow (Event Executes Gates)
variable {n : Nat} {Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

attribute [local irreducible] RegistrationAuthenticationExecutor.execute registration.begin_init_authentication

def callbacks (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (OracleComp (EnvEffects n))
  | .hash request => do
      let digest ← (EnvEffects n).query (.inr (.hash (hashBytes request)))
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .mldsa request => pure (RegistrationAuthenticationShared.verifyMldsa verify request)
  | .ed25519 request => pure (RegistrationAuthenticationShared.verifyEd25519 crypto request)

def program (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    OracleComp (EnvEffects n) (RustM (List Event × registration.InitAuthentication)) :=
  simulateQ (callbacks crypto verify) (RegistrationAuthenticationExecutor.begin pin packet)

/-- The actual verifier query has exactly the native World interpretation, with the complete cache and counter state. -/
theorem query_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Request) :
    simulateQ (PqxdhRecordLiftWorld.effects (n := n)) (callbacks setup.source.crypto verify query) =
      RegistrationWorldAuthentication.implementation setup codec route verify query := by
  cases query <;> rfl

/-- Arbitrary verifier continuations execute the same native controller callbacks; state is never replaced by a caller-supplied poststate. -/
theorem program_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    simulateQ (PqxdhRecordLiftWorld.effects (n := n)) (simulateQ (callbacks setup.source.crypto verify) work) =
      simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  exact query_native setup codec route verify query

/-- The real entry point factors into EnvEffects before the original record World interpreter. -/
theorem begin_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    simulateQ (PqxdhRecordLiftWorld.effects (n := n)) (program setup.source.crypto verify pin packet) =
      RegistrationWorldAuthentication.begin setup codec route verify pin packet := by
  rw [program, program_native setup codec route verify]
  simp only [RegistrationWorldAuthentication.begin, RegistrationWorldAuthentication.program,
    RegistrationWorldAuthentication.implementation, QueryImpl.simulateQ_compose]

/-- Every reached controller trace uses the extracted requests and continuations. -/
theorem begin_execution (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : PqxdhRecordLiftWorld.State n) (events : List Event) (final : registration.InitAuthentication)
    (supported : (.ok (events, final), after) ∈ support
      ((simulateQ PqxdhRecordLiftWorld.effects (program setup.source.crypto verify pin packet)).run before)) :
    Executes pin packet events final := by
  rw [program, program_native setup codec route verify] at supported
  exact RegistrationAuthenticationExecutor.simulated_begin_sound _ pin packet events final before after supported

/-- Successful native admission still requires all seven actual authentication callbacks, including the mandatory ML gate. -/
theorem begin_gates (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : PqxdhRecordLiftWorld.State n) (events : List Event) (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((simulateQ PqxdhRecordLiftWorld.effects (program setup.source.crypto verify pin packet)).run before)) :
    Gates packet events ∧ events.length = 7 := by
  rw [program, program_native setup codec route verify] at supported
  exact RegistrationAuthenticationExecutor.simulated_begin_accepted_requires_gates _ pin packet events authenticated
    before after supported

/-- Populated AD281 retains the actual selected keys and both fingerprints in the reached global cache. -/
theorem begin_associated_data (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : PqxdhRecordLiftWorld.State n) (events : List Event) (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((simulateQ PqxdhRecordLiftWorld.effects (program setup.source.crypto verify pin packet)).run before))
    (server : RawCtxServerRouting.Identity) :
    (RegistrationRecordBinding.ofRegistration authenticated.binding).associatedBytes server =
      BeaconcryptCore.Refinement.SessionBinding.boundAssociatedData
        (absBytes pin.binding.identity_public_key) (absBytes authenticated.binding.beacon_identity_public_key)
        (MldsaSharedAuthentication.cacheHash after.primitive.2 (absBytes pin.public_key))
        (MldsaSharedAuthentication.cacheHash after.primitive.2 (absBytes packet.mldsa_public_key)) := by
  rw [begin_native setup codec route verify pin packet] at supported
  exact RegistrationWorldAuthentication.begin_associated_data setup codec route verify pin packet before after events
    authenticated supported server

/-- Each actual verification callback makes at most one hash effect and no random or administrative effect. -/
theorem callback_bound (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Request) (kind : EffectKind) :
    (callbacks (n := n) crypto verify query).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .hash then 1 else 0) := by
  cases query with
  | hash request => cases kind <;> simp [callbacks, isQueryBoundP_query_iff, effectKind]
  | mldsa request => trivial
  | ed25519 request => trivial

end BeaconcryptCore.Computational.RegistrationAuthenticationCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.query_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.query_native
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.program_native
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.begin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.begin_native
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.begin_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.begin_execution
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.begin_gates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.begin_gates
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.begin_associated_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.begin_associated_data
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationCompiler.callback_bound
