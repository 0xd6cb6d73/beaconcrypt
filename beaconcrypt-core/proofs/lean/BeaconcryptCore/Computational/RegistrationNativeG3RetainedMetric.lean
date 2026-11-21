-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenRetained
import BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld

/-! The actual open retained compiler cannot read the three separately billed World coordinates. Its complete executable outputs remain unchanged under bilateral metric projection, retaining the original shared cache, keys, kernels, private roots and receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State world effect publication common)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def mask (before : State n KemSK) : State n KemSK :=
  { before with pool := PqxdhLiveKemBirth.empty, world := RegistrationNativeG3MetricWorld.mask before.world }

/-- Repeated normalization forgets exactly the same accounting coordinates. -/
theorem mask_idempotent (before : State n KemSK) : mask (mask before) = mask before := by
  simp only [mask, RegistrationNativeG3MetricWorld.mask_idempotent]

private theorem world_input (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (natural : ∀ state, Prod.map id RegistrationNativeG3MetricWorld.mask <$> work.run state =
      Prod.map id RegistrationNativeG3MetricWorld.mask <$> work.run (RegistrationNativeG3MetricWorld.mask state))
    (before : State n KemSK) :
    Prod.map id mask <$> (world work).run before =
      Prod.map id mask <$> (world work).run (mask before) := by
  have actual := congrArg (fun distribution =>
    (fun result => (result.1, { before with world := result.2, pool := (PqxdhLiveKemBirth.empty : PqxdhLiveKemBirth.Pool KemSK) })) <$>
      simulateQ RegistrationNativePublicInterpreter.coins distribution) (natural before.world)
  simpa only [world, StateT.run, mask, simulateQ_map, Functor.map_map, Prod.map_def, id_eq] using actual

theorem effect_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : State n KemSK) :
    Prod.map id mask <$> (effect query).run before =
      Prod.map id mask <$> (effect query).run (mask before) :=
  world_input _ (fun current => by
    exact RegistrationNativeG3MetricWorld.guarded_input (n := n) (KemSK := KemSK)
      setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inl query)) current) before

/-- Arbitrary adaptive environment work preserves its entire ordinary outcome under the external-pool/counter projection. -/
theorem effects_program_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (before : State n KemSK) :
    Prod.map id mask <$> (simulateQ effect work).run before =
      Prod.map id mask <$> (simulateQ effect work).run (mask before) := by
  let normalized : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n)
      (RegistrationNativePublicInterpreter.M n KemSK) :=
    fun query current => Prod.map id mask <$> (effect query).run current
  have step : ∀ query current, Prod.map id mask <$> (effect query).run current =
      (normalized query).run (mask current) := effect_input setup wire route
  have first := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ normalized mask step work before
  have second := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ normalized mask step work (mask before)
  rw [mask_idempotent] at second
  exact first.trans second.symm

/-- Actual shared signing attempts retain chronological receipts on success and failure, with no access to the external KEM pool. -/
theorem publication_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (route : RawCtxServerRouting.SenderDecoder) (query : RegistrationBoundPublication.Spec.Domain) (before : State n KemSK) :
    Prod.map id mask <$> (publication setup wire sign query).run before =
      Prod.map id mask <$> (publication setup wire sign query).run (mask before) := by
  have actual := effects_program_input setup wire route
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
    (route : RawCtxServerRouting.SenderDecoder) (query : (RegistrationNativePairedServerService.Common n).Domain) (before : State n KemSK) :
    Prod.map id mask <$> (common setup wire sign query).run before =
      Prod.map id mask <$> (common setup wire sign query).run (mask before) := by
  cases query with
  | inl query => exact publication_input setup wire sign route query before
  | inr query => exact effect_input setup wire route query before

/-- Early native admission and full record execution have the same branch and complete projected outcome. -/
theorem guarded_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (before : State n KemSK) :
    Prod.map id mask <$> (world
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query)).run before =
      Prod.map id mask <$> (world
        (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query)).run (mask before) :=
  world_input _ (RegistrationNativeG3MetricWorld.guarded_input setup (RegistrationNativeWire.ledgerCodec wire) route query) before

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
    (route : RawCtxServerRouting.SenderDecoder) (query : (RegistrationNativePairedServerService.Common n).Domain) (before : State n KemSK) :
    Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary setup.hmac (common setup wire sign query)).run before =
      Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary setup.hmac (common setup wire sign query)).run (mask before) :=
  ordinary_input setup.hmac _ before (common_input setup wire sign route query before)

/-- The retained-service ordinary compiler preserves actual guarded records and every failure poststate. -/
theorem ordinary_guarded (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (before : State n KemSK) :
    Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary setup.hmac (world
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query))).run before =
      Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary setup.hmac (world
        (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query))).run (mask before) :=
  ordinary_input setup.hmac _ before (guarded_input setup wire route query before)


/-- The metric projection commutes with the original empty-pool/uniform projection. -/
theorem mask_old (before : State n KemSK) :
    mask (RegistrationNativeOpenRetained.mask before) = mask before ∧
      RegistrationNativeOpenRetained.mask (mask before) = mask before := by
  exact ⟨rfl, rfl⟩

private theorem old_ordinary_input (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) (before : State n KemSK)
    (natural : ∀ current, Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary hmac work).run current =
      Prod.map id mask <$> (RegistrationNativePublicRetained.ordinary hmac work).run (mask current)) :
    Prod.map id mask <$> (RegistrationNativeOpenRetained.ordinary hmac work).run before =
      Prod.map id mask <$> (RegistrationNativeOpenRetained.ordinary hmac work).run (mask before) := by
  have same := congrArg (simulateQ (RegistrationNativeOpenRetained.baseLift (KemSK := KemSK))) (natural (RegistrationNativeOpenRetained.mask before))
  have left : ∀ current : State n KemSK, mask (RegistrationNativeOpenRetained.mask current) = mask current := fun current => (mask_old current).1
  have right : ∀ current : State n KemSK, RegistrationNativeOpenRetained.mask (mask current) = mask current := fun current => (mask_old current).2
  simpa only [RegistrationNativeOpenRetained.ordinary, StateT.run, Functor.map_map,
    Function.comp_def, Prod.map_def, id_eq, simulateQ_map, left, right] using same

/-- Every actual open retained callback preserves its exact projected output under metric input normalization. -/
theorem query_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State n KemSK) :
    Prod.map id mask <$> (RegistrationNativeOpenRetained.compiler setup wire route sign query).run before =
      Prod.map id mask <$> (RegistrationNativeOpenRetained.compiler setup wire route sign query).run (mask before) := by
  rcases query with (message | (message | query) | query) | query
  · simp only [RegistrationNativeOpenRetained.compiler, StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, mask_idempotent]
  · simp only [RegistrationNativeOpenRetained.compiler, StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, mask_idempotent]
  · exact old_ordinary_input setup.hmac _ before (ordinary_common setup wire sign route query)
  · simp only [RegistrationNativeOpenRetained.compiler, StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, mask_idempotent]
  · exact old_ordinary_input setup.hmac _ before (ordinary_guarded setup wire route (.inr (.inr query)))

/-- The complete original retained client has the same executable value when only metric input coordinates are normalized. -/
theorem client_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : State n KemSK) :
    RegistrationNativeOpenRetained.client setup wire route sign work before =
      RegistrationNativeOpenRetained.client setup wire route sign work (mask before) := by
  let normalized : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
      (StateT (State n KemSK) (OracleComp (RegistrationNativeOpenRetained.Spec KemSK))) :=
    fun query current => Prod.map id mask <$> (RegistrationNativeOpenRetained.compiler setup wire route sign query).run current
  have step : ∀ query current, Prod.map id mask <$> (RegistrationNativeOpenRetained.compiler setup wire route sign query).run current =
      (normalized query).run (mask current) := query_input setup wire route sign
  have first := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ normalized mask step work
    (RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear before))
  have second := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ normalized mask step work
    (RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear (mask before)))
  have clear_mask : ∀ current : State n KemSK,
      mask (RegistrationNativePublicRetained.clear current) = RegistrationNativePublicRetained.clear (mask current) := by
    intro current
    rfl
  have same : mask (RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear before)) =
      mask (RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear (mask before))) := by
    rw [(mask_old _).1, (mask_old _).1, clear_mask, clear_mask, mask_idempotent]

  rw [same] at first
  have values := congrArg (Functor.map Prod.fst) (first.trans second.symm)
  simpa only [RegistrationNativeOpenRetained.client, StateT.run'_eq, Functor.map_map, Prod.map_def, id_eq] using values

end BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.effect_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.effect_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.effects_program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.effects_program_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.publication_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.publication_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.common_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.common_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.guarded_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.guarded_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.ordinary_common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.ordinary_common
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.ordinary_guarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.ordinary_guarded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.mask_old' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.mask_old
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.query_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.query_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.client_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.client_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.mask_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedMetric.mask_idempotent
