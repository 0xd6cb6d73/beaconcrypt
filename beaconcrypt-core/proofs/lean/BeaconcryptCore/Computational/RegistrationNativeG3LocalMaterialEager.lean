-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletion

/-! A complete material44 table has the law of the actual lazy material cache through the entire mixed adaptive native frontend. The observation omits only that private cache; every other reached service, provider, receipt and semantic World coordinate is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialEager
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State)
open RegistrationNativeG3LocalMaterialCompletion (put drop openHandler fixed lazy)
open LazyOracleDiscard (LawEq)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}

/-- Before completing the table, the whole actual mixed execution factors through precisely its opened material queries. -/
theorem program_values (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) :
    Prod.map id drop <$>
      (simulateQ (RegistrationNativeG3LocalKeys.handler setup codec route wire sign seed scalar candidate provider) work).run before =
      RegistrationNativeG3CellEager.lazyRun
        (Prod.map id drop <$> (simulateQ (openHandler setup codec route wire sign seed scalar candidate provider) work).run (drop before))
        before.1.1.keys.materials := by
  have source := congrArg (fun distribution => Prod.map id drop <$> distribution)
    (RegistrationNativeG3LocalMaterialCompletion.program_source setup codec route wire sign seed scalar candidate provider
      work (drop before) before.1.1.keys.materials)
  have associated := congrArg
    (fun distribution => (fun result => (result.1.1, drop result.1.2)) <$> distribution)
    (OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT RegistrationNativeG3CellEager.lazy
      (openHandler setup codec route wire sign seed scalar candidate provider) work (drop before) before.1.1.keys.materials)
  simp only [RegistrationNativeG3CellEager.lazyRun, StateT.run'_eq, simulateQ_map, StateT.run_map,
    Functor.map_map, drop, put, RegistrationNativeG3LocalMaterialFrame.put, lazy,
    Prod.map_def, id_eq] at source associated ⊢
  exact source.symm.trans associated.symm

/-- The full mixed fixed-table execution is the fixed interpretation of its opened slot oracle. -/
theorem fixed_values (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) :
    RegistrationNativeG3CellEager.fixedRun table
      (Prod.map id drop <$> (simulateQ (openHandler setup codec route wire sign seed scalar candidate provider) work).run before) =
      Prod.map id drop <$> (simulateQ (fixed table setup codec route wire sign seed scalar candidate provider) work).run before := by
  simp only [RegistrationNativeG3CellEager.fixedRun, fixed, simulateQ_map]
  rw [QueryImpl.simulateQ_mapStateTBase_run]

/-- One independently sampled complete material44 table replaces the actual lazy cache through every adaptive callback; initial cached cells are overlaid literally. -/
theorem eager (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) :
    LawEq
      (Prod.map id drop <$>
        (simulateQ (RegistrationNativeG3LocalKeys.handler setup codec route wire sign seed scalar candidate provider) work).run before)
      (do let table ← $ᵗ (Slot n → Material)
          Prod.map id drop <$>
            (simulateQ (fixed (OracleComp.completeTable before.1.1.keys.materials table)
              setup codec route wire sign seed scalar candidate provider) work).run (drop before)) := by
  rw [program_values]
  have completed := RegistrationNativeG3CellEager.cached_eager
    (Prod.map id drop <$> (simulateQ (openHandler setup codec route wire sign seed scalar candidate provider) work).run (drop before))
    before.1.1.keys.materials
  simpa only [fixed_values] using completed

end BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialEager
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialEager.program_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialEager.program_values
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialEager.fixed_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialEager.fixed_values
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialEager.eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialEager.eager
