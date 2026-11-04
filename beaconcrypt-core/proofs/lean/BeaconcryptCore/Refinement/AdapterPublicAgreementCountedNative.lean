-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter
import BeaconcryptCore.Refinement.AdapterPublicAgreementServerNativeWorld
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The literal SDK agreement with its field-by-field counted source dictionary has the same traced captured execution and full native Server state. The trace is private instrumentation of the same original request tree; forgetting it derives the exact actual SDK entry, with returned RNG and every failure retained. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementCountedNative
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementInterpreter (Capture handler)
open AdapterPublicAgreementPrimitiveModel (Model)
open AdapterPublicAgreementServerNative (Entropy keys)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {n : Nat}
variable [original : CryptoOperations (RustT ProbComp)]
local notation "World" => PqxdhRecordLiftWorld.State n
local notation "Counted" => RustT (StateT World ProbComp)

noncomputable def captured {R E Value : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (work : OracleComp Spec Value) (rng : R) : Counted ((Value × RegistrationAgreementQueryTrace.Trace) × Capture R) :=
  letI : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
  (simulateQ (handler (m := StateT World ProbComp) generator keys)
    (RegistrationAgreementQueryTrace.trace work [])).run ⟨rng, .None, .None⟩

noncomputable section
theorem execute_trace {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (rng : R) :
    letI : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
    (do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_server_agreement control status authenticated)
        beaconcrypt_public_request.pqxdh.execute_agreement (m := Counted) generator phase keys rng) = (do
      let ((effect, _journal), after) ← captured generator keys (RegistrationAgreementExecutor.server control status authenticated) rng
      let completed ← AdapterRecordRequestMonad.liftRust effect
      pure (completed, after.rng)) := by
  let : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
  rw [AdapterPublicAgreementSourceEntries.server]
  unfold AdapterPublicAgreementSourceEntries.run captured
  rw [← AdapterPublicAgreementCountedInterpreter.trace_erasure generator keys
    (RegistrationAgreementExecutor.server control status authenticated) ⟨rng, .None, .None⟩]
  rw [bind_map_left]

variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

theorem native (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (created : PqxdhLiveServerConstruction.Created Unit)
    (identityView : view.edSecret identity = created.seed) (rng : R) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (fresh : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    AdapterPublicAgreementServerNativeWorld.restore view before <$>
      ((captured generator (keys identity) (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) rng).run).run
        before.server.world.world.1 =
      RustM.ok <$> (RegistrationNativeExperiment.server
        (RegistrationServerNativeSource.agree setup checks model.representation created packet authenticated)).run before := by
  unfold captured
  rw [AdapterPublicAgreementCountedInterpreter.program]
  exact AdapterPublicAgreementServerNativeWorld.native model entropy identity created identityView rng packet authenticated before fresh

theorem indexed (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (created : PqxdhLiveServerConstruction.Created Unit)
    (identityView : view.edSecret identity = created.seed) (rng : R) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (fresh : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    AdapterPublicAgreementServerNativeWorld.restore view before <$>
      ((captured generator (keys identity) (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) rng).run).run
        before.server.world.world.1 =
      RustM.ok <$> (Prod.map id (fun current => RegistrationNativeKemServerState.toNative current.1 current.2) <$>
        (RegistrationNativeKemCountedTrusted.execute setup
          (RegistrationNativeKemCountedServerPrimitive.agree setup checks model.representation created authenticated)).run
            (RegistrationNativeKemCountedTrusted.project before)) := by
  rw [RegistrationNativeKemCountedServerSource.agree_native setup checks model.representation created packet authenticated before]
  exact native model entropy identity created identityView rng packet authenticated before fresh
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementCountedNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedNative.execute_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedNative.execute_trace

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedNative.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedNative.native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedNative.indexed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedNative.indexed
