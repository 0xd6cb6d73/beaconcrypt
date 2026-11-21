-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInitWriterFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState

/-! Actual source publication retains its exact cache, ML receipt list, replies and persistent platform state after projecting only native accounting and owner metadata. The terminal writer remains the actual source writer program; no static encoder or full-World accounting equality is asserted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationProject
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local project)
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {E Platform Value Next ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

noncomputable def shared (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (owner : Owner source) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT RegistrationSigningShared.State (StateT Platform ProbComp)) :=
  fun query before => simulateQ coins ((RegistrationNativeMldsaShared.implementation setup owner query).run before)

noncomputable def encode
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.InitView) : StateT Platform ProbComp (RustM (Option (alloc.vec.Vec U8))) :=
  simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
    (RegistrationNativePlatformWriter.initPacket view)).run

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

/-- Literal native callback projection keeps the original source reply/cache/history and the exact external poststate. -/
theorem outgoing (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (before : Local n KemSK source) (previous : Platform) :
    Prod.map id (Prod.map project id) <$>
      (pack (RegistrationNativePlatformBundleLower.native coins setup checks representation created
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))).run (before, previous) =
      (pack (shared coins setup owner query)).run (project before, previous) := by
  have native := RegistrationNativeMldsaShared.outgoing setup checks representation created index owner query before
  have interpreted := congrArg (fun action => (simulateQ coins action).run previous) native
  simp only [simulateQ_map, StateT.run_map] at interpreted
  have same := congrArg (fun action => (fun result : (RegistrationBeaconInitExecutor.Spec.Range query × RegistrationSigningShared.State) × Platform =>
    (result.1.1, (result.1.2, result.2))) <$> action) interpreted
  simpa only [pack, RegistrationNativePlatformBundleLower.native, shared, StateT.run,
    Functor.map_map, Prod.map, id_eq] using same

/-- Actual terminal encoding preserves the entire native Local state while retaining the exact source writer result and external poststate. -/
theorem encoding
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.InitView) (before : Local n KemSK source) (previous : Platform) :
    Prod.map id (Prod.map project id) <$>
      (pack (RegistrationNativePlatformInitWriterFrame.encoder writer view)).run (before, previous) =
      (pack (StateT.lift (encode writer view) : StateT RegistrationSigningShared.State (StateT Platform ProbComp) _)).run (project before, previous) := by
  rw [RegistrationNativePlatformInitWriterFrame.encoder_frame]
  simp only [pack, encode, StateT.run, lift_apply,
    map_apply, Functor.map_map, Prod.map, id_eq]

private theorem pack_hom {Native : Type} :
    Cslib.IsMonadHom (StateT Native (StateT Platform ProbComp)) (StateT (Native × Platform) ProbComp) pack :=
  .mk' RegistrationNativePlatformPackedState.pure_pack RegistrationNativePlatformPackedState.bind_pack

private abbrev Spec := RegistrationBeaconInitExecutor.Spec +
  (registration.InitView →ₒ RustM (Option (alloc.vec.Vec U8)))
private def free : QueryImpl RegistrationBeaconInitExecutor.Spec (OracleComp Spec) := fun query => Spec.query (.inl query)
private def freeEncode (view : registration.InitView) : OracleComp Spec (RustM (Option (alloc.vec.Vec U8))) := Spec.query (.inr view)

/-- Every complete actual source publication retains the full projected signing state and external poststate, through the literal effectful terminal writer. -/
theorem begin_project (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (owner : Owner source)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (before : Local n KemSK source) (previous : Platform) :
    Prod.map id (Prod.map project id) <$>
      (pack (RegistrationNativePlatformBeaconPublication.begin
        (fun query => RegistrationNativePlatformBundleLower.native coins setup checks representation created
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (RegistrationNativePlatformInitWriterFrame.encoder writer) control inputs scalar pin)).run (before, previous) =
      (pack (RegistrationNativePlatformBeaconPublication.begin (shared coins setup owner)
        (fun view => StateT.lift (encode writer view)) control inputs scalar pin)).run (project before, previous) := by
  let native : QueryImpl Spec (StateT (Local n KemSK source × Platform) ProbComp)
    | .inl query => pack (RegistrationNativePlatformBundleLower.native coins setup checks representation created
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
    | .inr view => pack (RegistrationNativePlatformInitWriterFrame.encoder writer view)
  let projected : QueryImpl Spec (StateT (RegistrationSigningShared.State × Platform) ProbComp)
    | .inl query => pack (shared coins setup owner query)
    | .inr view => pack (StateT.lift (encode writer view) : StateT RegistrationSigningShared.State (StateT Platform ProbComp) _)
  have queries : ∀ query current, Prod.map id (Prod.map project id) <$> (native query).run current =
      (projected query).run (Prod.map project id current) := by
    intro query current
    rcases current with ⟨current, platform⟩
    cases query with
    | inl query => exact outgoing coins setup checks representation created index owner query current platform
    | inr view => exact encoding writer view current platform
  let work := RegistrationNativePlatformBeaconPublication.begin free freeEncode control inputs scalar pin
  have law := OracleComp.map_run_simulateQ_eq_of_query_map_eq native projected (Prod.map project id) queries work (before, previous)
  have nativeProgram : simulateQ native work =
      pack (RegistrationNativePlatformBeaconPublication.begin
        (fun query => RegistrationNativePlatformBundleLower.native coins setup checks representation created
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (RegistrationNativePlatformInitWriterFrame.encoder writer) control inputs scalar pin) := by
    unfold work
    rw [RegistrationNativePlatformBeaconPublication.begin_interpret]
    simp only [free, freeEncode, simulateQ_spec_query, native]
    exact (RegistrationNativePlatformBeaconMap.begin pack_hom _ _ control inputs scalar pin).symm
  have sharedProgram : simulateQ projected work =
      pack (RegistrationNativePlatformBeaconPublication.begin (shared coins setup owner)
        (fun view => StateT.lift (encode writer view)) control inputs scalar pin) := by
    unfold work
    rw [RegistrationNativePlatformBeaconPublication.begin_interpret]
    simp only [free, freeEncode, simulateQ_spec_query, projected]
    exact (RegistrationNativePlatformBeaconMap.begin pack_hom _ _ control inputs scalar pin).symm
  rw [nativeProgram, sharedProgram] at law
  exact law

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationProject

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationProject.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationProject.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationProject.encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationProject.encoding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationProject.begin_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationProject.begin_project
