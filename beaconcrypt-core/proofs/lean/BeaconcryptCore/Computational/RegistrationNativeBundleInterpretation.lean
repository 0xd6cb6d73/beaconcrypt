-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformFrontend
/-! The actual combined bundle frontend folds to independently interpreted outgoing callbacks and the literal extracted source Init writer on one complete Native state over an arbitrary common platform monad. The writer interpreter is exactly its actual independent Native-state lift, so every reservation failure preserves the full Native state and the reached external poststate. Complete Core publication, signing receipts and source writer continuations are retained without a whole-controller correspondence premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativePlatformFrontend (interpret AllowedBundle)
variable {n : Nat} {I KemSK E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Front" => RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State (OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK))

private def writerFront (query : (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E).Domain) :
    Front ((BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E).Range query) :=
  StateT.lift (StateT.lift (RegistrationNativePlatformGenericBundle.writerLift query))

theorem writer_query (query : (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E).Domain) :
    interpret (RegistrationNativePlatformExperiment.bundleHandler (n := n) coins setup checks representation created source writer)
      (writerFront (E := E) (n := n) (KemSK := KemSK) (source := source) query) = (StateT.lift (writer query) : StateT Native m _) := by
  funext before
  change (interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
    (writerFront query)).run before = (StateT.lift (writer query) : StateT Native m _).run before
  rw [RegistrationNativePlatformFrontend.run_interpret]
  simp only [writerFront, StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map,
    simulateQ_map, RegistrationNativePlatformGenericBundle.writerLift, simulateQ_spec_query,
    RegistrationNativePlatformExperiment.bundleHandler, RegistrationNativePlatformExperiment.writer,
    RegistrationNativeLocalStatePatch.assemble_self]

noncomputable def outgoing (index : Nat) (owner : Owner source) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (RegistrationNativePlatformExperiment.M n KemSK source m) := fun query =>
  interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
    (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))

noncomputable def encoder (view : registration.SignedInitView) : RegistrationNativePlatformExperiment.M n KemSK source m (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
    (RegistrationNativePlatformGenericBundle.encoder E view)

theorem encoder_source (view : registration.SignedInitView) :
    encoder (n := n) (source := source) coins setup checks representation created writer view =
      (StateT.lift (simulateQ writer (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := E) (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run) : StateT Native m _) := by
  let work := (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit
    (E := E) (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
    (RegistrationNativePlatformWriter.initPacket view)).run
  have expanded : simulateQ (writerFront (E := E) (n := n) (KemSK := KemSK) (source := source)) work =
      RegistrationNativePlatformGenericBundle.encoder E view := by
    exact RegistrationNativePlatformFrontend.double_simulate (RegistrationNativePlatformGenericBundle.writerLift (E := E) (n := n) (KemSK := KemSK)) work
  have safe : ∀ query : (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E).Domain, RegistrationNativePlatformFrontend.Work (AllowedBundle (E := E) (n := n) (KemSK := KemSK))
      (writerFront (E := E) (n := n) (KemSK := KemSK) (source := source) query) := by
    intro query
    unfold writerFront
    apply RegistrationNativePlatformFrontend.lifted_work
    simp only [RegistrationNativePlatformGenericBundle.writerLift, allQueriesSatisfy_query_iff, AllowedBundle]
  unfold encoder
  rw [← expanded, RegistrationNativePlatformFrontend.simulate_interpret _ _
    (RegistrationNativePlatformFrontend.bundle_atomic coins setup checks representation created writer) _ safe]
  simp only [writer_query coins setup checks representation created writer]
  exact simulateQ_liftTarget writer work


theorem publication (index : Nat) (owner : Owner source)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    interpret (RegistrationNativePlatformExperiment.bundleHandler (n := n) coins setup checks representation created source writer)
      (RegistrationNativePlatformBeaconPublication.begin
        (fun query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (RegistrationNativePlatformGenericBundle.encoder E) control inputs scalar pin mldsa) =
      RegistrationNativePlatformBeaconPublication.begin (outgoing coins setup checks representation created writer index owner)
        (encoder coins setup checks representation created writer) control inputs scalar pin mldsa := by
  rw [← RegistrationNativePlatformFrontend.publication_tree setup index owner control inputs scalar pin mldsa,
    RegistrationNativePlatformFrontend.simulate_interpret _ _
      (RegistrationNativePlatformFrontend.bundle_atomic coins setup checks representation created writer) _
      (RegistrationNativePlatformFrontend.joint_work setup index owner),
    RegistrationNativePlatformWriter.begin_interpret]
  have encoded : (fun view => simulateQ (fun query =>
      interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
        (writerFront (n := n) (E := E) (KemSK := KemSK) (source := source) query))
      (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := E) (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run) = encoder (n := n) (source := source) coins setup checks representation created writer := by
    funext view
    simp only [writer_query coins setup checks representation created writer]
    rw [encoder_source coins setup checks representation created writer]
    exact simulateQ_liftTarget writer _
  change RegistrationNativePlatformBeaconPublication.begin
    (outgoing coins setup checks representation created writer index owner)
    (fun view => simulateQ (fun query => interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (writerFront (n := n) (E := E) (KemSK := KemSK) (source := source) query))
      (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := E) (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run) control inputs scalar pin mldsa = _
  rw [encoded]


theorem legacy (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A) :
    interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift work) =
      RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.beacon setup checks representation created work) := by
  funext before
  change (interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
    (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift work)).run before = _
  rw [RegistrationNativePlatformFrontend.run_interpret]
  change (fun result => (result.1.1.1, RegistrationNativeFinishTerminalTree.assemble result.1.1.2 result.1.2 result.2)) <$>
    (simulateQ (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (simulateQ RegistrationNativePlatformGenericBundle.trustedLift
        ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)))).run before = _
  rw [← QueryImpl.simulateQ_compose]
  have callbacks : (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer ∘ₛ
      RegistrationNativePlatformGenericBundle.trustedLift) =
      RegistrationNativePlatformExperiment.trusted (n := n) coins setup checks representation created source := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativePlatformGenericBundle.trustedLift,
      simulateQ_spec_query, RegistrationNativePlatformExperiment.bundleHandler]
  rw [callbacks]
  have law := congrFun (RegistrationNativePlatformInterpret.state_simulate coins
    (RegistrationNativeExperiment.trusted setup checks representation created source)
    ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))) before
  change simulateQ coins ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
    ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before) =
    (simulateQ (RegistrationNativePlatformExperiment.trusted coins setup checks representation created source)
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before at law
  rw [← law]
  change _ = simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)
  rw [RegistrationNativeLocalStatePatch.beacon_run, simulateQ_map]

end BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation.writer_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation.writer_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation.encoder_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation.encoder_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation.legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation.legacy
