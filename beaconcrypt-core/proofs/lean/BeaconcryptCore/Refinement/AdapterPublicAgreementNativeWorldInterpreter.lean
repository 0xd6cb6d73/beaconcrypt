-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap
import BeaconcryptCore.Refinement.AdapterPublicAgreementCountedNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual SDK source crypto fields and complete agreement executor run in the existing full Native monad by its literal World lens. This retains every outer Native coordinate and every source RNG/private-capture result. The same reached request tree then gives the actual native Server agreement under individual primitive functional contracts. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementInterpreter (Capture handler)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK : Type} {source : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
local notation "WorldM" => StateT (PqxdhRecordLiftWorld.State n) ProbComp
local notation "NativeM" => RegistrationNativeExperiment.M n KemSK source
local notation "NativeRust" => RustT NativeM

@[instance_reducible] noncomputable def operations (original : CryptoOperations (RustT ProbComp)) : CryptoOperations NativeRust :=
  letI : AdapterPublicAgreementMonadMap.Transformation WorldM NativeM := AdapterPublicAgreementNativeWorldMap.translation
  AdapterPublicAgreementMonadCrypto.operations (left := WorldM) (right := NativeM) (AdapterPublicAgreementCountedCrypto.operations (n := n) original)

noncomputable section
theorem execute {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (phase : agreement.AgreementEffect) (rng : R) :
    letI : CryptoOperations NativeRust := operations (n := n) (KemSK := KemSK) (source := source) original
    beaconcrypt_public_request.pqxdh.execute_agreement (m := NativeRust) generator phase keys rng =
      AdapterPublicAgreementNativeWorldMap.transform (KemSK := KemSK) (source := source)
        (letI : CryptoOperations (RustT WorldM) := AdapterPublicAgreementCountedCrypto.operations (n := n) original
         beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT WorldM) generator phase keys rng) := by
  let : CryptoOperations (RustT WorldM) := AdapterPublicAgreementCountedCrypto.operations (n := n) original
  let : AdapterPublicAgreementMonadMap.Transformation WorldM NativeM := AdapterPublicAgreementNativeWorldMap.translation
  exact AdapterPublicAgreementMonadInterpreter.execute (left := WorldM) (right := NativeM) generator keys phase rng

theorem entry {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (start : RustM agreement.AgreementEffect) (rng : R) :
    letI : CryptoOperations NativeRust := operations (n := n) (KemSK := KemSK) (source := source) original
    (do let phase ← AdapterRecordRequestMonad.liftRust start
        beaconcrypt_public_request.pqxdh.execute_agreement (m := NativeRust) generator phase keys rng) =
      AdapterPublicAgreementNativeWorldMap.transform (KemSK := KemSK) (source := source)
        (letI : CryptoOperations (RustT WorldM) := AdapterPublicAgreementCountedCrypto.operations (n := n) original
         (do let phase ← AdapterRecordRequestMonad.liftRust start
             beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT WorldM) generator phase keys rng)) := by
  let : CryptoOperations (RustT WorldM) := AdapterPublicAgreementCountedCrypto.operations (n := n) original
  let : AdapterPublicAgreementMonadMap.Transformation WorldM NativeM := AdapterPublicAgreementNativeWorldMap.translation
  exact AdapterPublicAgreementMonadInterpreter.entry (left := WorldM) (right := NativeM) generator keys start rng

noncomputable def captured {R E Value : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (work : OracleComp Spec Value) (rng : R) : NativeRust ((Value × RegistrationAgreementQueryTrace.Trace) × Capture R) :=
  letI : CryptoOperations NativeRust := operations original
  (simulateQ (handler (m := NativeM) generator keys) (RegistrationAgreementQueryTrace.trace work [])).run ⟨rng, .None, .None⟩

theorem captured_eq {R E Value : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (work : OracleComp Spec Value) (rng : R) :
    captured (n := n) (KemSK := KemSK) (source := source) generator keys work rng =
      AdapterPublicAgreementNativeWorldMap.transform (AdapterPublicAgreementCountedNative.captured generator keys work rng) := by
  let : CryptoOperations (RustT WorldM) := AdapterPublicAgreementCountedCrypto.operations (n := n) original
  let : AdapterPublicAgreementMonadMap.Transformation WorldM NativeM := AdapterPublicAgreementNativeWorldMap.translation
  exact AdapterPublicAgreementMonadInterpreter.program (left := WorldM) (right := NativeM) generator keys (RegistrationAgreementQueryTrace.trace work []) ⟨rng, .None, .None⟩

theorem captured_run {R E Value : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (work : OracleComp Spec Value) (rng : R) (before : RegistrationNativeExperiment.State n KemSK source) :
    ((captured generator keys work rng).run).run before =
      (fun result => (result.1, AdapterPublicAgreementNativeWorldMap.putWorld before result.2)) <$>
        (((AdapterPublicAgreementCountedNative.captured generator keys work rng).run).run before.server.world.world.1) := by
  rw [captured_eq]
  exact AdapterPublicAgreementNativeWorldMap.world_run _ before

theorem execute_trace {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (rng : R) :
    letI : CryptoOperations NativeRust := operations (n := n) (KemSK := KemSK) (source := source) original
    (do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_server_agreement control status authenticated)
        beaconcrypt_public_request.pqxdh.execute_agreement (m := NativeRust) generator phase keys rng) = (do
      let ((effect, _journal), after) ← captured generator keys (RegistrationAgreementExecutor.server control status authenticated) rng
      let completed ← AdapterRecordRequestMonad.liftRust effect
      pure (completed, after.rng)) := by
  rw [entry, AdapterPublicAgreementCountedNative.execute_trace]
  rw [AdapterPublicAgreementNativeWorldMap.transform_bind, captured_eq]
  apply bind_congr
  rintro ⟨⟨effect, journal⟩, after⟩
  simp only [AdapterPublicAgreementNativeWorldMap.transform_bind,
    AdapterPublicAgreementNativeWorldMap.transform_liftRust, AdapterPublicAgreementNativeWorldMap.transform_pure]

noncomputable def restore {R : Type} (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (((RustM agreement.AgreementEffect) × RegistrationAgreementQueryTrace.Trace) × Capture R) ×
      RegistrationNativeExperiment.State n KemSK source) :
    RustM (RustM agreement.AgreementEffect × RegistrationNativeExperiment.State n KemSK source) :=
  AdapterPublicAgreementServerNativeWorld.restore view before (result.1, result.2.server.world.world.1)

variable {ι : Type} {base : OracleSpec ι} {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

theorem native (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model) (identity : material.EdSecretKey)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (identityView : view.edSecret identity = created.seed)
    (rng : R) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (fresh : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    restore view before <$>
      (((captured generator (AdapterPublicAgreementServerNative.keys identity)
        (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) rng).run).run before) =
      RustM.ok <$> (RegistrationNativeExperiment.server
        (RegistrationServerNativeSource.agree setup checks model.representation created packet authenticated)).run before := by
  rw [captured_run, Functor.map_map]
  exact AdapterPublicAgreementCountedNative.native model entropy identity created identityView rng packet authenticated before fresh
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.execute

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.entry

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.captured_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.captured_eq

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.captured_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.captured_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.execute_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.execute_trace

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldInterpreter.native
