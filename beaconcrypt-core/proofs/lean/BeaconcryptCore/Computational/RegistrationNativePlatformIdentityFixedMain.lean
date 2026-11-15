-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainFull
/-! The actual current indexed source dispatcher and original FullCompiler retain each owner fixed-prekey signing policy through every native, writer and persistent-platform outcome. Source interpretation is used only to obtain supported actual source-body outputs; signing-history synchronization remains the separate generated-row invariant. Literal empty owner initialization supplies Fixed without a history, row-availability or whole-controller premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret beacon assemble poolProjection)
open RegistrationNativePlatformIdentityFixedNative (Fixed)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- Source interpretation preserves a fixed-history receipt derived from the actual common-P source body, without assuming source-history synchronization. -/
theorem beacon_fixed (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value)
    (law : RegistrationNativePlatformIdentityFixedCore.Preserves Fixed work)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : Value × ((State n KemSK source × Platform) × SourceState)) (prior : Fixed before.1.1.beacons)
    (supported : result ∈ support ((interpret setup.joint (beacon setup checks representation created work)).run before)) :
    Fixed result.2.1.1.beacons := by
  have viewed := Set.mem_image_of_mem (Prod.map id poolProjection) supported
  rw [←support_map,RegistrationNativePlatformIdentityMain.beacon_execution,support_map] at viewed
  obtain ⟨inner,reached,equal⟩ := viewed
  have original : inner.1 ∈ support (((work.run before.1.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world)).run before.1.2) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created) _
      ⟨before.1.1.context,RegistrationNativeIdentityCompiler.poolView before.2⟩
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have kept := law before.1.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world) before.1.2 inner.1 prior original
  have same := congrArg (fun result => result.2.1.1.beacons) equal
  change inner.1.1.1.2=result.2.1.1.beacons at same
  exact same ▸ kept

/-- Actual ambient native/platform work retains the indexed owner history fields literally. -/
theorem ordinary_fixed (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (RegistrationNativeIdentityWorld.Context n KemSK × Platform) ProbComp Value)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : Value × ((State n KemSK source × Platform) × SourceState)) (prior : Fixed before.1.1.beacons)
    (supported : result ∈ support ((interpret joint (RegistrationNativePlatformIdentityMainOrdinary.ordinary work)).run before)) :
    Fixed result.2.1.1.beacons := by
  simp only [interpret,StateT.run,support_map] at supported
  obtain ⟨inner,reached,equal⟩ := supported
  have original : inner.1 ∈ support ((RegistrationNativePlatformIdentityMainOrdinary.ordinary (source := source) work).run before.1) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeIdentityMainSource.implementation joint) _ before.2
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  simp only [RegistrationNativePlatformIdentityMainOrdinary.ordinary,StateT.run,support_map] at original
  obtain ⟨actual,_sampled,returned⟩ := original
  have same := congrArg (fun value => value.2.1.beacons) returned
  cases equal
  exact same.symm ▸ prior

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before=Prod.map change id <$> work before := StateT.run_map change work before

private theorem interpret_map {Next : Type} (joint : PqxdhJointIdentity.Primitives) (change : Value → Next)
    (work : M n KemSK Platform source Value) (before : (State n KemSK source × Platform) × SourceState) :
    (interpret joint (change <$> work)).run before=Prod.map change id <$> (interpret joint work).run before := by
  simp only [interpret,StateT.run,map_apply,simulateQ_map,Functor.map_map,Prod.map,id_eq]

variable [primitives : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "handler" => RegistrationNativePlatformIdentityMainTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

private theorem ambient_fixed (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × ((State n KemSK source × Platform) × SourceState)) (prior : Fixed before.1.1.beacons)
    (supported : result ∈ support ((interpret setup.joint (RegistrationNativePlatformIdentityMainAmbient.step setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query)).run before)) : Fixed result.2.1.1.beacons := by
  exact ordinary_fixed setup.joint _ before result prior supported

attribute [local irreducible] RegistrationNativePlatformIdentityMainAmbient.step RegistrationNativePlatformIdentityMainAmbient.command

/-- Every literal current callback preserves fixed-prekey signing history through all writer, primitive and corrected finish outcomes. -/
theorem handler_fixed (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × ((State n KemSK source × Platform) × SourceState))
    (prior : Fixed before.1.1.beacons) (supported : result ∈ support ((interpret setup.joint (handler query)).run before)) :
    Fixed result.2.1.1.beacons := by
  cases query with
  | inl coin => exact ambient_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inl coin) before result prior supported
  | inr query => cases query with
    | create edPin mlPin keyId =>
      exact beacon_fixed setup checks representation created _
        (RegistrationNativePlatformIdentityFixedCore.native_preserves _ _ (RegistrationNativePlatformIdentityFixedNative.create_fixed setup source edPin mlPin keyId))
        before result prior supported
    | bundle index =>
      rw [RegistrationNativePlatformIdentityMainTyped.handler,RegistrationNativePlatformIdentityMainBundle.bundle,
        interpret_map,support_map] at supported
      obtain ⟨inner,reached,equal⟩ := supported
      cases equal
      exact beacon_fixed setup checks representation created _ (RegistrationNativePlatformIdentityFixedCore.bundle_fixed setup index writer)
        before inner prior reached
    | finish index packet =>
      exact beacon_fixed setup checks representation created _
        (RegistrationNativePlatformIdentityFixedCore.native_preserves _ _
          (RegistrationNativePlatformIdentityFixedFinish.finish_fixed setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet))
        before result prior supported
    | accept packet =>
      unfold RegistrationNativePlatformIdentityMainTyped.handler at supported
      rw [RegistrationNativePlatformIdentityMainOrdinary.interpret_bind,StateT.run_bind,
        RegistrationNativePlatformIdentityMainOrdinary.report_source,pure_bind] at supported
      exact ambient_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet)) before result prior supported
    | build session application => exact ambient_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build session application)) before result prior supported
    | hmac key message => exact ambient_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hmac key message)) before result prior supported
    | hash bytes => exact ambient_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hash bytes)) before result prior supported
    | serverSend keyId plaintext => exact ambient_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverSend keyId plaintext)) before result prior supported
    | serverRaw raw => exact ambient_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverRaw raw)) before result prior supported
    | beaconSend index plaintext => exact ambient_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconSend index plaintext)) before result prior supported
    | beaconRaw index raw => exact ambient_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconRaw index raw)) before result prior supported

/-- All adaptive current source prefixes retain their actual immutable-prekey signing policy. -/
theorem program_fixed (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : Value × ((State n KemSK source × Platform) × SourceState)) (prior : Fixed before.1.1.beacons)
    (supported : result ∈ support ((interpret setup.joint (simulateQ handler work)).run before)) : Fixed result.2.1.1.beacons := by
  rw [RegistrationNativePlatformIdentityMainProgram.interpret_program] at supported
  exact simulateQ_run_preservesInv _ (fun current => Fixed current.1.1.beacons)
    (fun query current valid next reached => handler_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      query current next valid reached) work before prior result supported

/-- The original full raw/secrecy compiler retains the same fixed history on every actual source outcome and complete common-P poststate. -/
theorem run_fixed (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : (Value × RegistrationNativeLedger.State) × ((State n KemSK source × Platform) × SourceState))
    (prior : Fixed before.1.1.beacons)
    (supported : result ∈ support ((interpret setup.joint (RegistrationNativePlatformIdentityMainFull.run setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work)).run before)) :
    ∀ owner ∈ result.2.1.1.beacons, RegistrationNativeEdOrigin.FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory :=
  program_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result prior supported

/-- Literal empty owner initialization establishes the actual indexed fixed history without a source-row or history premise. -/
theorem initialized (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (context : RegistrationNativeIdentityWorld.Context n KemSK) (previous : Platform) (pool : SourceState)
    (result : (Value × RegistrationNativeLedger.State) × ((State n KemSK source × Platform) × SourceState))
    (supported : result ∈ support ((interpret setup.joint (RegistrationNativePlatformIdentityMainFull.run setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work)).run ((⟨context,[]⟩,previous),pool))) :
    ∀ owner ∈ result.2.1.1.beacons, RegistrationNativeEdOrigin.FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory := by
  apply run_fixed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work _ result _ supported
  intro owner impossible
  cases impossible
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.beacon_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.beacon_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.ordinary_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.ordinary_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.handler_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.handler_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.program_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.program_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.run_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.run_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain.initialized
