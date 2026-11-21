-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual source SDK agreement and same private capture/trace run under the literal NativePlatform coin interpretation, preserving arbitrary external allocation state. All typed crypto fields are mapped individually; the whole source/controller correspondence is derived. The selected native primitive model is invoked only for the final actual Server agreement coupling. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementInterpreter (Capture handler)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK : Type} {source : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK source m
local notation "NativeRust" => RustT NativeM

@[instance_reducible] noncomputable def operations (coins : QueryImpl unifSpec m)
    (original : CryptoOperations (RustT ProbComp)) : CryptoOperations NativeRust :=
  AdapterPublicAgreementOracleInterpretation.operations (State := RegistrationNativeExperiment.State n KemSK source) coins
    (AdapterPublicAgreementNativeWorldInterpreter.operations (n := n) (KemSK := KemSK) (source := source) original)

noncomputable section
theorem execute (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (phase : agreement.AgreementEffect) (rng : R) :
    letI : CryptoOperations NativeRust := operations (n := n) (KemSK := KemSK) (source := source) coins original
    beaconcrypt_public_request.pqxdh.execute_agreement (m := NativeRust) generator phase keys rng =
      AdapterPublicAgreementOracleInterpretation.transform coins
        (letI : CryptoOperations (RustT (RegistrationNativeExperiment.M n KemSK source)) := AdapterPublicAgreementNativeWorldInterpreter.operations original
         beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT (RegistrationNativeExperiment.M n KemSK source)) generator phase keys rng) :=
  AdapterPublicAgreementOracleInterpretation.execute coins _ generator keys phase rng

theorem entry (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (start : RustM agreement.AgreementEffect) (rng : R) :
    letI : CryptoOperations NativeRust := operations (n := n) (KemSK := KemSK) (source := source) coins original
    (do let phase ← AdapterRecordRequestMonad.liftRust start
        beaconcrypt_public_request.pqxdh.execute_agreement (m := NativeRust) generator phase keys rng) =
      AdapterPublicAgreementOracleInterpretation.transform coins
        (letI : CryptoOperations (RustT (RegistrationNativeExperiment.M n KemSK source)) := AdapterPublicAgreementNativeWorldInterpreter.operations original
         (do let phase ← AdapterRecordRequestMonad.liftRust start
             beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT (RegistrationNativeExperiment.M n KemSK source)) generator phase keys rng)) :=
  AdapterPublicAgreementOracleInterpretation.entry coins _ generator keys start rng

noncomputable def captured (coins : QueryImpl unifSpec m) {R E Value : Type}
    (generator : rand_core.TryCryptoRng R E) (keys : Keys) (work : OracleComp Spec Value) (rng : R) :
    NativeRust ((Value × RegistrationAgreementQueryTrace.Trace) × Capture R) :=
  letI : CryptoOperations NativeRust := operations coins original
  (simulateQ (handler (m := NativeM) generator keys) (RegistrationAgreementQueryTrace.trace work [])).run ⟨rng, .None, .None⟩

theorem captured_eq (coins : QueryImpl unifSpec m) {R E Value : Type}
    (generator : rand_core.TryCryptoRng R E) (keys : Keys) (work : OracleComp Spec Value) (rng : R) :
    captured (n := n) (KemSK := KemSK) (source := source) coins generator keys work rng =
      AdapterPublicAgreementOracleInterpretation.transform coins
        (AdapterPublicAgreementNativeWorldInterpreter.captured generator keys work rng) :=
  AdapterPublicAgreementOracleInterpretation.program coins _ generator keys (RegistrationAgreementQueryTrace.trace work []) ⟨rng, .None, .None⟩

theorem captured_run (coins : QueryImpl unifSpec m) {R E Value : Type}
    (generator : rand_core.TryCryptoRng R E) (keys : Keys) (work : OracleComp Spec Value) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((captured coins generator keys work rng).run).run before =
      simulateQ coins (((AdapterPublicAgreementNativeWorldInterpreter.captured generator keys work rng).run).run before) := by
  rw [captured_eq]
  rfl

theorem execute_trace (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (rng : R) :
    letI : CryptoOperations NativeRust := operations (n := n) (KemSK := KemSK) (source := source) coins original
    (do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_server_agreement control status authenticated)
        beaconcrypt_public_request.pqxdh.execute_agreement (m := NativeRust) generator phase keys rng) = (do
      let ((effect, _journal), after) ← captured coins generator keys (RegistrationAgreementExecutor.server control status authenticated) rng
      let completed ← AdapterRecordRequestMonad.liftRust effect
      pure (completed, after.rng)) := by
  rw [entry, AdapterPublicAgreementNativeWorldInterpreter.execute_trace]
  rw [AdapterPublicAgreementOracleInterpretation.transform_bind, captured_eq]
  apply bind_congr
  rintro ⟨⟨effect, journal⟩, after⟩
  simp only [AdapterPublicAgreementOracleInterpretation.transform_bind,
    AdapterPublicAgreementOracleInterpretation.transform_liftRust, AdapterPublicAgreementOracleInterpretation.transform_pure]

variable {ι : Type} {base : OracleSpec ι} {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

theorem native (coins : QueryImpl unifSpec m)
    (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model) (identity : material.EdSecretKey)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (identityView : view.edSecret identity = created.seed)
    (rng : R) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (fresh : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    AdapterPublicAgreementNativeWorldInterpreter.restore view before <$>
      (((captured coins generator (AdapterPublicAgreementServerNative.keys identity)
        (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) rng).run).run before) =
      RustM.ok <$> (RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.server
          (RegistrationServerNativeSource.agree setup checks model.representation created packet authenticated))).run before := by
  rw [captured_run, ← simulateQ_map,
    AdapterPublicAgreementNativeWorldInterpreter.native model entropy identity created identityView rng packet authenticated before fresh,
    simulateQ_map]
  rfl
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.execute

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.entry

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.captured_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.captured_eq

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.captured_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.captured_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.execute_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.execute_trace

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter.native
