-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealProvenanceRun
import BeaconcryptCore.Computational.CborRawIdealProvenanceTrace
import BeaconcryptCore.Computational.CborRawEnvironmentJoin

/-! Concrete ideal registration provenance for the original raw transcript. Public payload admission and response-envelope stripping preserve every accept ordinal, returned session and assigned peer. The local proof invokes the actual existing ideal registration handler and retains its complete World, environment and origins. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealProvenance
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment EnvQuery EnvSpec)
open PqxdhDeploymentInterface (Entry Spec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentEnvironmentJoin (Good)
open PqxdhDeploymentIdealOrigins (aEffects IsFixed)
open PqxdhDeploymentIdealProvenance (Prov)
open CborRawPublicState (Public)
open CborRawIdealProvenanceTrace (shape entryShape)
variable {ι KemSK Reader Response Bk A : Type} {baseSpec : OracleSpec ι} {n : Nat}

/-- The actual public registration adapter commutes with the original annotated shared effects. -/
theorem step_effects (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) {E : Type} (env : Environment n E)
    (query : EnvQuery) (state : Public × E) (world : PqxdhRecordLiftOrigins.State n) :
    (simulateQ (aEffects setup codec route) ((CborRawEnvironment.step env query).run state)).run world =
      (fun value => ((CborRawEnvironment.reply state.1 query value.1.1,
        (CborRawEnvironment.next state.1 query value.1.1, value.1.2)), value.2)) <$>
        (simulateQ (aEffects setup codec route)
          ((env.step (CborRawEnvironment.request state.1 query)).run state.2)).run world := by
  simp only [CborRawEnvironment.step_run, simulateQ_map, StateT.run_map]

/-- Every delegated registration reply has the same public provenance shape after native envelope stripping. -/
theorem entry_shape (state : Public) (query : EnvQuery)
    (reply : EnvSpec.Range (CborRawEnvironment.request state query)) :
    entryShape ⟨.inl (.inr (CborRawEnvironment.request state query).val), reply⟩ =
      entryShape ⟨.inl (.inr query.val), CborRawEnvironment.reply state query reply⟩ := by
  rcases query with ⟨command, valid⟩
  cases command with
  | build session payload =>
      dsimp only [CborRawEnvironment.request, CborRawEnvironment.reply, entryShape]
      cases reply <;> rfl
  | _ => rfl

private theorem map_state_apply {Input Output : Type} (f : Input → Output)
    (work : StateT (PqxdhRecordLiftOrigins.State n) ProbComp Input)
    (state : PqxdhRecordLiftOrigins.State n) :
    (f <$> work) state = Prod.map f id <$> work state :=
  bind_pure_comp (Prod.map f id) (work state)

private theorem lifted_request {E : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (request : (PqxdhRecordLiftInterface.WorldSpec n).Domain) (e : E)
    (world : PqxdhRecordLiftOrigins.State n) :
    (simulateQ (PqxdhRecordLiftOrigins.handler setup codec route)
      ((StateT.lift (liftM ((PqxdhRecordLiftInterface.WorldSpec n).query request)) :
        StateT E (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) _).run e)).run world =
      (fun value => ((value.1, e), value.2)) <$>
        (PqxdhRecordLiftOrigins.handler setup codec route request).run world := by
  rw [StateT.run_lift, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp]

/-- Fixed commands never inspect the public registration wrapper or call its environment step. -/
theorem ordinary_fixed_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) {E : Type} (env : Environment n E) (serverKid : Std.U64)
    (query : Spec.Domain) (isFixed : IsFixed query) (publicState : Public) (e : E)
    (world : PqxdhRecordLiftOrigins.State n) :
    (PqxdhDeploymentIdealOrigins.aWorldStep setup codec route
      (CborRawEnvironment.environment env serverKid) query).run ((publicState, e), world) =
      (fun value => (value.1, ((publicState, value.2.1), value.2.2))) <$>
        (PqxdhDeploymentIdealOrigins.aWorldStep setup codec route env query).run (e, world) := by
  rw [PqxdhDeploymentIdealOrigins.aWorldStep_run, PqxdhDeploymentIdealOrigins.aWorldStep_run, Functor.map_map]
  rcases query with coin | command
  · simp only [PqxdhRecordLiftInterface.native, StateT.lift, StateT.run, bind_pure_comp, simulateQ_map, map_state_apply, Functor.map_map] <;> rfl
  · cases command <;> simp only [IsFixed] at isFixed
    case hash bytes =>
      simp only [PqxdhRecordLiftInterface.native, StateT.lift, StateT.run,
        bind_pure_comp, simulateQ_map, map_state_apply, Functor.map_map]
      rfl
    case serverSend keyId plaintext =>
      erw [lifted_request setup codec route (.inr (.inr (.inl (.inl (plaintext, keyId))))) (publicState, e) world,
        lifted_request setup codec route (.inr (.inr (.inl (.inl (plaintext, keyId))))) e world, Functor.map_map]
      erw [Functor.map_map]
    case serverRaw raw =>
      erw [lifted_request setup codec route (.inr (.inr (.inl (.inr raw)))) (publicState, e) world,
        lifted_request setup codec route (.inr (.inr (.inl (.inr raw)))) e world, Functor.map_map]
      erw [Functor.map_map]
    case beaconSend owner plaintext =>
      erw [lifted_request setup codec route (.inr (.inr (.inr (owner, .inl plaintext)))) (publicState, e) world,
        lifted_request setup codec route (.inr (.inr (.inr (owner, .inl plaintext)))) e world, Functor.map_map]
      erw [Functor.map_map]
    case beaconRaw owner raw =>
      erw [lifted_request setup codec route (.inr (.inr (.inr (owner, .inr raw)))) (publicState, e) world,
        lifted_request setup codec route (.inr (.inr (.inr (owner, .inr raw)))) e world, Functor.map_map]
      erw [Functor.map_map]

section Ideal
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)

/-- One actual raw ideal registration step preserves provenance of the original raw transcript. -/
theorem step_prov (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : EnvQuery) (transcript : List Entry)
    (state : Public × EnvState KemSK SplitBk) (world : PqxdhRecordLiftWorld.State 2)
    (origins : PqxdhRecordLiftOrigins.Origins 2) (good : Good created state.2 world)
    (inv : PqxdhDeploymentIdealEnv.IdealInv target state.2 world)
    (holds : Prov target transcript state.2 world origins)
    (result : (EnvSpec.Range query × (Public × EnvState KemSK SplitBk)) × PqxdhRecordLiftOrigins.State 2)
    (supported : result ∈ support ((simulateQ
      (aEffects setup (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse))
      ((CborRawEnvironment.step (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse)
        checks target parameters ensureInit identityIndex runtime) query).run state)).run (world, origins))) :
    Prov target (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2.2 result.2.1 result.2.2 := by
  rw [step_effects, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have source := reached
  rw [CborRawIdealProvenanceStep.effects_codec setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.route parse) (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)] at source
  have preserved := PqxdhDeploymentIdealProvenance.ideal_rStep setup (CborRawCompile.sourceCodec wire parse)
    (CborRawCompile.route parse) checks target parameters created (CborRawEnvironment.request state.1 query)
    transcript state.2 world origins good inv holds inner source
  apply CborRawIdealProvenanceTrace.prov_transport target _ _ _ _ _ _ preserved
  simp only [shape, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  rw [entry_shape]

end Ideal
end BeaconcryptCore.Computational.CborRawIdealProvenance

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenance.step_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenance.step_effects

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenance.entry_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenance.entry_shape

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenance.ordinary_fixed_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenance.ordinary_fixed_public

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenance.step_prov' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenance.step_prov
