-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocol
import BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialEager

/-! Completing the material44 table is now composed with the actual guarded selective protocol. The public protocol outcome retains the entire caller result, current frontend and same original G2 chronology; every existing material-cache entry is overlaid literally. The separate actual World seed cache and role-use state remain untouched by this material completion. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocolLazy
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State project)
open RegistrationNativeG3LocalMaterialCompletion (put drop fixed)
open RegistrationNativeG3MaterializedTracedProtocol (publicProgram worldProgram hiddenGame)
open LazyOracleDiscard (LawEq)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (source : RegistrationNativeMldsa.Source) (checks : Checks)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
  (frontend : RegistrationNativePublicFrontend.State source) (before : State n KemSK ProviderState)

noncomputable def actual :=
  (fun result => result.1.1) <$>
    (simulateQ (CborRecordWorldSimulation.guarded setup codec route)
      ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
        (publicProgram setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend)).run before.1)).run before.2

/-- The actual guarded selective program with completed44 cache is exactly the original fixed material frontend after the accounting projection; only private output is omitted here. -/
theorem hidden_source (table : Slot n → Material) :
    hiddenGame table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before =
      Prod.fst <$> (simulateQ (fixed table setup codec route wire sign seed scalar candidate provider)
        (publicProgram setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend)).run (project (drop before)) := by
  have sourceEq := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3LocalMaterialCompletedSource.world_source table setup codec route wire sign seed scalar candidate provider
      (publicProgram setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend) (drop before))
  simpa only [hiddenGame, RegistrationNativeG3GuardedCoupling.hidden, worldProgram, drop, put,
    RegistrationNativeG3LocalMaterialFrame.put, RegistrationNativeG3LocalMaterialCompletedSource.cache,
    Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using sourceEq

/-- One full44 table, overlaid with the actual existing private cache, has the exact contextual law of the original guarded selective protocol. -/
theorem material_uniform :
    LawEq
      (actual setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before)
      (do let table ← $ᵗ (Slot n → Material)
          hiddenGame (OracleComp.completeTable before.1.1.keys.materials table) setup codec route wire sign seed scalar candidate provider
            source checks selectedOwner selectedAccept publicPrekey work frontend before) := by
  have original := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3LocalKeys.original_source setup codec route wire sign seed scalar candidate provider
      (publicProgram setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend) before)
  have completed := (RegistrationNativeG3LocalMaterialEager.eager setup codec route wire sign seed scalar candidate provider
    (publicProgram setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend) (project before)).map Prod.fst
  have identified : actual setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before =
      Prod.fst <$> (simulateQ (RegistrationNativeG3LocalKeys.handler setup codec route wire sign seed scalar candidate provider)
        (publicProgram setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend)).run (project before) := by
    simpa only [actual, Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using original
  rw [identified]
  simpa only [map_bind, Functor.map_map, Prod.map_def, id_eq, Function.comp_def,
    hidden_source setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before,
    project, drop, put, RegistrationNativeG3LocalMaterialFrame.put] using completed

noncomputable def fullGame := do
  let table ← $ᵗ (Slot n → Material)
  RegistrationNativeG3MaterializedTracedProtocol.fullGame (OracleComp.completeTable before.1.1.keys.materials table)
    setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before

noncomputable def auditRun (table : Slot n → Material) := do
  let seeds ← $ᵗ (RegistrationNativeG3AuditedWorld.Seeds n)
  let result ← RegistrationNativeG3GuardedCoupling.audit setup codec route
    (RegistrationNativeG3GuardedCoupling.overlay before.2 seeds)
    (worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before) before.2
  pure (seeds, result)

/-- The entire actual known108 frontend and original lazy guarded selective protocol differ only by the concrete protocol's known-side repeat audit. Both complete-table samplings and all source correspondences are derived, with no extra query, cache, seed or game-equivalence premise. -/
theorem bound :
    ENNReal.ofReal (discreteDistance
      (fullGame setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before)
      (actual setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before)) ≤
      Pr{let pair ← (do
        let table ← $ᵗ (Slot n → Material)
        let result ← auditRun setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey
          work frontend before (OracleComp.completeTable before.1.1.keys.materials table)
        pure (table, result))}[pair.2.2.2.2 = true] := by
  have compared := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent ($ᵗ (Slot n → Material))
    (fun table => RegistrationNativeG3MaterializedTracedProtocol.fullGame (OracleComp.completeTable before.1.1.keys.materials table)
      setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before)
    (fun table => hiddenGame (OracleComp.completeTable before.1.1.keys.materials table)
      setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before)
    (fun table => auditRun setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey
      work frontend before (OracleComp.completeTable before.1.1.keys.materials table))
    (fun _ result => result.2.2.2 = true) (fun table _ => by
      have pointwise := ENNReal.toReal_mono (prEvent_ne_top _)
        (RegistrationNativeG3MaterializedTracedProtocol.bound (OracleComp.completeTable before.1.1.keys.materials table)
          setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before)
      simpa only [auditRun, ENNReal.toReal_ofReal (discreteDistance_nonneg _ _)] using pointwise)
  have hiddenEq : (do
      let table ← $ᵗ (Slot n → Material)
      hiddenGame (OracleComp.completeTable before.1.1.keys.materials table) setup codec route wire sign seed scalar candidate provider
        source checks selectedOwner selectedAccept publicPrekey work frontend before) =ᵈ
      actual setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before := by
    let : MeasurableSpace ((Value × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State) := ⊤
    let : DiscreteMeasurableSpace ((Value × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State) :=
      ⟨fun _ => MeasurableSpace.measurableSet_top⟩
    exact _root_.EvalDistEq.of_evalDist_eq
      (material_uniform setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before).symm.evalDist_eq
  rw [discreteDistance_congr (.rfl) hiddenEq] at compared
  exact (ENNReal.ofReal_le_ofReal compared).trans (ENNReal.ofReal_toReal (prEvent_ne_top _)).le

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocolLazy
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocolLazy.hidden_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocolLazy.hidden_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocolLazy.material_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocolLazy.material_uniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocolLazy.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocolLazy.bound
