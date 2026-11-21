-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicRetained
import BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform

/-! Ordinary native record and publication components cannot read the external KEM pool or its private uniform counter. Both input and output are projected: operations may sample again. Complete roots, signing receipts, World cache, native/effect counters, kernels, owners, raw attempts and produced frames remain retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State world effect publication common)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def mask (before : State n KemSK) : State n KemSK :=
  { before with pool := PqxdhLiveKemBirth.empty, world := RegistrationNativeKemWorldUniform.mask before.world }

private theorem world_input (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (natural : ∀ state, Prod.map id RegistrationNativeKemWorldUniform.mask <$> work.run state =
      Prod.map id RegistrationNativeKemWorldUniform.mask <$> work.run (RegistrationNativeKemWorldUniform.mask state))
    (before : State n KemSK) :
    Prod.map id mask <$> (world work).run before =
      Prod.map id mask <$> (world work).run (mask before) := by
  have actual := congrArg (fun distribution =>
    (fun result => (result.1, { before with world := result.2, pool := (PqxdhLiveKemBirth.empty : PqxdhLiveKemBirth.Pool KemSK) })) <$>
      simulateQ RegistrationNativePublicInterpreter.coins distribution) (natural before.world)
  simpa only [world, StateT.run, mask, simulateQ_map, Functor.map_map, Prod.map_def, id_eq] using actual

theorem effect_input (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : State n KemSK) :
    Prod.map id mask <$> (effect query).run before =
      Prod.map id mask <$> (effect query).run (mask before) :=
  world_input _ (RegistrationNativeKemWorldEffects.effects_input query) before

/-- Arbitrary adaptive environment work preserves its entire ordinary outcome under the external-pool/counter projection. -/
theorem effects_program_input (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (before : State n KemSK) :
    Prod.map id mask <$> (simulateQ effect work).run before =
      Prod.map id mask <$> (simulateQ effect work).run (mask before) := by
  let normalized : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n)
      (RegistrationNativePublicInterpreter.M n KemSK) :=
    fun query current => Prod.map id mask <$> (effect query).run current
  have step : ∀ query current, Prod.map id mask <$> (effect query).run current =
      (normalized query).run (mask current) := effect_input
  have first := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ normalized mask step work before
  have second := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ normalized mask step work (mask before)
  exact first.trans second.symm

/-- Actual shared signing attempts retain chronological receipts on success and failure, with no access to the external KEM pool. -/
theorem publication_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (before : State n KemSK) :
    Prod.map id mask <$> (publication setup wire sign query).run before =
      Prod.map id mask <$> (publication setup wire sign query).run (mask before) := by
  have actual := effects_program_input
    ((RegistrationBoundSourceCompiler.compiler setup.source (RegistrationNativeWire.ledgerCodec wire).frameWrite sign query).run before.receipts)
    before
  have mapped := congrArg (fun distribution =>
    (fun result => (result.1.1, { result.2 with receipts := result.1.2 })) <$> distribution) actual
  simpa only [publication, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_map, StateT.run_modify, map_pure, bind_pure_comp,
    Functor.map_map, mask, Prod.map_def, id_eq] using mapped

/-- Every actual paired common callback retains all semantic state under both sides of the mask. -/
theorem common_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain) (before : State n KemSK) :
    Prod.map id mask <$> (common setup wire sign query).run before =
      Prod.map id mask <$> (common setup wire sign query).run (mask before) := by
  cases query with
  | inl query => exact publication_input setup wire sign query before
  | inr query => exact effect_input query before

/-- Early native admission and full record execution have the same branch and complete projected outcome. -/
theorem guarded_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (before : State n KemSK) :
    Prod.map id mask <$> (world
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query)).run before =
      Prod.map id mask <$> (world
        (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query)).run (mask before) :=
  world_input _ (RegistrationNativeKemWorldRecordUniform.guarded_input setup (RegistrationNativeWire.ledgerCodec wire) route query) before

private theorem ordinary_input (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) (before : State n KemSK)
    (natural : Prod.map id mask <$> work.run before = Prod.map id mask <$> work.run (mask before)) :
    Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary hmac work).run before =
      Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary hmac work).run (mask before) := by
  have actual := congrArg (fun distribution => simulateQ RegistrationNativePublicRetained.coins
    (simulateQ (RegistrationNativePublicRootCoins.localImpl hmac) distribution)) natural
  simpa only [RegistrationNativePublicRetained.ordinary, StateT.run, simulateQ_map] using actual

/-- The retained-service ordinary compiler preserves the actual common callback after externalizing KEM state. -/
theorem ordinary_common (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain) (before : State n KemSK) :
    Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary setup.hmac (common setup wire sign query)).run before =
      Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary setup.hmac (common setup wire sign query)).run (mask before) :=
  ordinary_input setup.hmac _ before (common_input setup wire sign query before)

/-- The retained-service ordinary compiler preserves actual guarded records and every failure poststate. -/
theorem ordinary_guarded (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (before : State n KemSK) :
    Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary setup.hmac (world
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query))).run before =
      Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary setup.hmac (world
        (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query))).run (mask before) :=
  ordinary_input setup.hmac _ before (guarded_input setup wire route query before)

end BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.effect_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.effect_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.effects_program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.effects_program_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.publication_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.publication_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.common_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.common_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.guarded_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.guarded_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.ordinary_common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.ordinary_common
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.ordinary_guarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame.ordinary_guarded
