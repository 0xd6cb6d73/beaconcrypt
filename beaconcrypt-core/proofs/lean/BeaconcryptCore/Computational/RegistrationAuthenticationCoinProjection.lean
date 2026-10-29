-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationCompiler
import BeaconcryptCore.Computational.RegistrationWorldCoinCompiler

/-! Native authentication reads the actual CTX cache and increments hash/uniform counters. It does not read the separate Env coin-effect ledger. This derived projection allows the open Server source comparison to retain authentication before replay and agreement without an assumed whole-verifier equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldCoinCompiler (eraseCoin)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

private theorem charge_hash (bytes : List UInt8) (before : PqxdhRecordLiftWorld.State n) :
    eraseCoin (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) before) =
      PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) (eraseCoin before) := by
  have distinct : PqxdhRecordLiftInterface.EffectKind.hash ≠ .coin := by decide
  simp only [eraseCoin, PqxdhRecordLiftWorld.chargeEffect, PqxdhRecordLiftInterface.effectKind,
    Function.update_of_ne distinct, Function.update_comm distinct]

/-- The actual shared hash service ignores only the unrelated Env coin-effect ledger while keeping the native cache and hash/uniform bill. -/
theorem hash_mask (bytes : List UInt8) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id eraseCoin <$> (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before =
      (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run (eraseCoin before) := by
  have sampled := RegistrationWorldCoinCompiler.sampled_erase
    ((CtxRomAuth.ctxRandomOracle ((), bytes)).run before.primitive.2)
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) before)
  rw [charge_hash] at sampled
  have lifted := congrArg (fun distribution => (fun result => (result.1.1,
    { result.2 with primitive := (result.2.primitive.1, result.1.2) })) <$> distribution) sampled
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run,
    bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, eraseCoin,
    PqxdhRecordLiftWorld.chargeEffect] at lifted ⊢
  exact lifted

/-- Every actual native verifier callback retains its reply and complete World after this counter projection. -/
theorem query_mask (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Request) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id eraseCoin <$>
      (RegistrationWorldAuthentication.implementation setup codec route verify query).run before =
      (RegistrationWorldAuthentication.implementation setup codec route verify query).run (eraseCoin before) := by
  cases query with
  | hash request =>
      have sampled := congrArg (fun distribution => Prod.map
        (fun digest => core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest)) id <$> distribution)
        (hash_mask (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) before)
      simp only [RegistrationWorldAuthentication.implementation, QueryImpl.apply_compose,
        RegistrationWorldAuthentication.callbacks, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
        PqxdhRecordLiftWorld.handler, StateT.run_map]
      simp only [Functor.map_map, Prod.map_def, id_eq] at sampled ⊢
      exact sampled
  | mldsa request => rfl
  | ed25519 request => rfl

/-- The mandatory ML/Ed/hash entry point commutes with the proved counter projection for its entire native controller trace. -/
theorem begin_mask (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : beaconcrypt_core.session.ServerAuthenticationPin) (packet : beaconcrypt_core.registration.InitPacket)
    (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id eraseCoin <$>
      (RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before =
      (RegistrationWorldAuthentication.begin setup codec route verify pin packet).run (eraseCoin before) := by
  unfold RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ eraseCoin
    (query_mask setup codec route verify) _ before

end BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection.hash_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection.hash_mask
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection.query_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection.query_mask
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection.begin_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection.begin_mask
