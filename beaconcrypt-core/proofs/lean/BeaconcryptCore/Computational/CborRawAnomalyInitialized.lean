-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyCoupling
import BeaconcryptCore.Computational.CborRawAnomalyPool

/-! The frozen raw transcript guess reaches the concrete native pool predictor from every actual successful Server construction. No selected-cut simulation is assumed: its invariant starts at the real constructor, and the full original secrecy ledger is reassociated exactly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyInitialized
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec FullSpec FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentSecrecy (Ledger wrap ledgerImpl)
open PqxdhDeploymentIdealGuess (guessCt)
open CborRawAnomalyLedger (full)
variable {ι KemSK Reader Response A S X : Type} {baseSpec : OracleSpec ι}

/-- The original wrapped ledger and the actual flattened full interface have the same final transcript guess. -/
theorem wrap_guess (impl : QueryImpl Spec (StateT S ProbComp)) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds) {count : Nat}
    (target : Target count) (work : OracleComp FullSpec X) (state : S) :
    (fun result => guessCt codec target result.2.1.transcript) <$>
      (simulateQ (full impl crypto codec serverKid bounds) work).run (Ledger.empty, state) =
    (fun result => guessCt codec target result.1.2.transcript) <$>
      (simulateQ impl (wrap crypto codec serverKid bounds work)).run state := by
  rw [wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  rfl

/-- The private source pool at construction projects to the exact initial native state. -/
theorem native_initial (created : PqxdhLiveServerConstruction.Created Unit)
    (privatePool : PqxdhRegistrationJointPreparation.Pool KemSK) (serverKid : Std.U64) :
    CborAdmissionCompiler.merge (CborAdmissionCompiler.Local.empty serverKid)
      (PqxdhRegistrationJointSchedule.source (PqxdhDeploymentIdealCut.sourceInit created privatePool)) =
      PqxdhDeploymentNative.initial created := by
  rw [CborAdmissionCompiler.merge, CborAdmissionCompiler.Local.empty, PqxdhDeploymentCompile.merge_empty]
  rfl

/-- The actual source-owned compiler's original ledger guess is precisely the independently defined raw native pool predictor. -/
theorem pool_guess (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (privatePool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse)
      (CborAdmissionCompiler.Local.empty setup.serverKeyId) (PqxdhRegistrationSchedule.initial created))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    (fun result => guessCt (CborTaggedSimulation.boundaryWire wire parse) target result.1.2.transcript) <$>
      (simulateQ (CborRawPreScan.poolCompiler setup wire parse checks target parameters created)
        (wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds
          (asModeO mode adversary))).run
          (CborAdmissionCompiler.Local.empty setup.serverKeyId, PqxdhDeploymentIdealCut.sourceInit created privatePool) =
    CborRawAnomalyPool.atPool setup wire parse checks target parameters created bounds mode adversary := by
  let work := wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds
    (asModeO mode adversary)
  have represented := CborRawCutPrefix.native_program setup wire parse checks created.seed
    created.server.server.metadata.identityIndex (parameters.pool target) lengths parser phase1 phase2 work
    (CborAdmissionCompiler.Local.empty setup.serverKeyId) (PqxdhDeploymentIdealCut.sourceInit created privatePool) good
  have observed := congrArg (fun program =>
    (fun result => guessCt (CborTaggedSimulation.boundaryWire wire parse) target result.1.2.transcript) <$> program)
    represented
  rw [native_initial] at observed
  simp only [Functor.map_map] at observed
  rw [CborRawCutPrefix.source, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map] at observed
  exact observed

/-- Full actual raw middle execution and the native pool predictor have the same frozen original transcript guess. -/
theorem middle_pool (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (ensureInit : StateT A ProbComp Bool)
    (before after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, after) ∈ support
      ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run before))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    LazyOracleDiscard.LawEq
      ((fun result => guessCt (CborTaggedSimulation.boundaryWire wire parse) target result.1.2.transcript) <$>
        (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
          (wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds
            (asModeO mode adversary))).run
              (CborRawPublicState.ofMemory (CborAdmissionCompiler.Local.empty setup.serverKeyId),
                PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
      (CborRawAnomalyPool.atPool setup wire parse checks target parameters created bounds mode adversary) := by
  have valid := CborRawPrefixHandoff.initial_inv setup wire parse created ensureInit none before after born
  have coupled := CborRawAnomalyCoupling.program_law setup wire parse checks target parameters created phase1 phase2
    (CborRawPrefixHandoff.initial created after.1) bounds (asModeO mode adversary) Ledger.empty
    (CborRawPrefixHandoff.start setup created after.1) valid rfl (Nat.zero_le _)
  rw [wrap_guess, wrap_guess, CborRawPrefixHandoff.native_start] at coupled
  rw [CborRawPrefixHandoff.start, CborRawPreScan.pool, CborRawPrefixHandoff.initial] at coupled
  rw [pool_guess setup wire parse checks lengths parser phase1 phase2 target parameters created after.1
    (CborRawInitializedCut.initial_good setup wire parse created ensureInit none before after born)] at coupled
  exact coupled

end BeaconcryptCore.Computational.CborRawAnomalyInitialized

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyInitialized.wrap_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyInitialized.wrap_guess
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyInitialized.native_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyInitialized.native_initial
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyInitialized.pool_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyInitialized.pool_guess
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyInitialized.middle_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyInitialized.middle_pool
