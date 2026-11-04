-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealQuiet
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveUnselected
import BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace

/-! The canonical marked source has the literal original normalized CTX source marginal across every actual callback. Selected-target role, source synchronization and the genuine generated row are preserved operationally; no whole-handler equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (selected position : Nat) (placeholder : Ed25519Signature)
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve)
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "MainState" => RegistrationNativeIdentityMain.State n KemSK mlSource × Platform
local notation "view" => RegistrationNativeIdentityCensorOutgoingView.view placeholder

local notation "current" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder

local notation "entered(" query "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.entered position query before
local notation "called(" masked "," query "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.call setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked query before
local notation "run(" masked "," accept "," work "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.visit setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked accept work before


def Ready (selected : Nat) (seed : PqxdhJointIdentity.IdentitySeed) (before : FullState) : Prop :=
  RegistrationNativeIdentityCensorTargetRole.Tagged before.1.2 ∧ before.1.2.target = before.2.target ∧
    before.2.pool.seeds[selected]? = some seed

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem normalized_source (query : TypedSpec.Domain) (before : FullState) :
    (interpret setup.joint selected placeholder false (current query)).run before =
      Prod.map id view <$> (interpret setup.joint selected placeholder false (actual query)).run before := by
  simp only [RegistrationNativeIdentityCensorAdaptivePostselection.normalized,interpret,StateT.run,simulateQ_map,map_apply,
    bind_pure_comp,Functor.map_map,RegistrationNativeIdentityCensorOutgoingView.view,Prod.map_def,id_eq]

private theorem plain_normalized (query : TypedSpec.Domain)
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform mlSource) :
    (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (current query)).run before =
      Prod.map id (RegistrationNativeIdentityCensorPrefixOwned.view placeholder) <$>
        (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (actual query)).run before := by
  simp only [RegistrationNativeIdentityCensorAdaptivePostselection.normalized,RegistrationNativePlatformIdentityCtxMain.interpret,
    StateT.run,simulateQ_map,map_apply,Functor.map_map,RegistrationNativeIdentityCensorPrefixOwned.view,Prod.map_def,id_eq]

private theorem actual_source (query : TypedSpec.Domain) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState) (inactive : before.1.2.active = false) (prior : Ready selected seed before) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (interpret setup.joint selected placeholder false (actual query)).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (actual query)).run
        (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  by_cases bundleQuery : ∃ index, query = .inr (.bundle index)
  · obtain ⟨index,rfl⟩ := bundleQuery
    cases target : before.1.2.target with
    | none =>
      exact RegistrationNativeIdentityCensorPreselectionBundleSource.callback_original setup checks representation created selected index placeholder reserve
        before target (prior.2.1.symm.trans target) inactive (by intro owner _lookup _same; exact ⟨seed,prior.2.2⟩)
    | some message =>
      exact RegistrationNativeIdentityCensorPostselectionBundleCut.callback_original setup checks representation created selected index placeholder reserve
        message (prior.1 message target) before seed target (prior.2.1.symm.trans target) inactive prior.2.2
  · exact RegistrationNativeIdentityCensorRealQuiet.callback setup checks wire route representation created credential keys failure allocation reserveRegistration
      reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve) selected placeholder false query
      (fun index same => bundleQuery ⟨index,same⟩) before inactive

omit primitive in
private theorem main_row (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (found : before.2.pool.seeds[selected]? = some seed)
    (result : A × FullState) (reached : result ∈ support ((interpret setup.joint selected placeholder false work).run before)) :
    result.2.2.pool.seeds[selected]? = some seed := by
  simp only [interpret,StateT.run,bind_pure_comp,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  exact RegistrationNativeIdentityCensorSelectedInvariant.row_program setup.joint selected placeholder false seed _ before.2 found inner called

omit primitive in
private theorem entry_ready (query : TypedSpec.Domain) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState) (prior : Ready selected seed before) : Ready selected seed (entered(query,before)) := by
  refine ⟨RegistrationNativeIdentityCensorTargetRole.enter position query before.1.2 prior.1,?_,prior.2.2⟩
  rcases query with coin | command
  · exact prior.2.1
  · cases command <;> exact prior.2.1

private theorem call_ready (query : TypedSpec.Domain) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState) (prior : Ready selected seed before) (result : TypedSpec.Range query × FullState)
    (reached : result ∈ support called(false,query,before)) : Ready selected seed result.2 := by
  have entry := entry_ready selected position query seed before prior
  exact ⟨RegistrationNativeIdentityCensorTargetRole.main setup.joint selected placeholder false (current query) _ entry.1 result reached,
    RegistrationNativeIdentityCensorTargetSyncMain.main setup.joint selected placeholder false (current query) _ entry.2.1 result reached,
    main_row setup selected placeholder (current query) _ seed entry.2.2 result reached⟩

/-- One actual canonical marked callback has the complete original normalized source marginal, including its current reply, source audit, cache, draw counters and platform state. -/
theorem query_source (query : TypedSpec.Domain) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState) (prior : Ready selected seed before) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> called(false,query,before) =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (current query)).run
        (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  simp only [RegistrationNativeIdentityCensorAdaptivePostselection.call,normalized_source,Functor.map_map]
  rw [plain_normalized]
  have original := actual_source setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
    erased helper reserve selected placeholder query seed (entered(query,before))
      (RegistrationNativeIdentityCensorCompiler.enter_inactive position query before.1.2) (entry_ready selected position query seed before prior)
  have observed := congrArg (Functor.map (Prod.map id (RegistrationNativeIdentityCensorPrefixOwned.view placeholder))) original
  simpa only [Functor.map_map,RegistrationNativeIdentityCensorOutgoingView.view,RegistrationNativeIdentityCensorPrefixOwned.view,
    RegistrationNativeIdentityCensorActualHashSource.project,RegistrationNativeIdentityCensorAdaptivePostselection.entered,Prod.map_def,id_eq] using observed

noncomputable def handler : QueryImpl TypedSpec (StateT FullState ProbComp) := fun query before => called(false,query,before)
local notation "canonical" => handler setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer
  reserveFrame erased helper reserve selected position placeholder

/-- Every adaptive canonical marked source run from the reached first-issued row has the literal complete original normalized CTX marginal. This retains every current reply, failed call, source observation, physical hash query and platform state through arbitrary later callback choices. -/
theorem program_source (work : OracleComp TypedSpec A) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState) (prior : Ready selected seed before) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (simulateQ canonical work).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (simulateQ current work)).run
        (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  rw [RegistrationNativePlatformIdentityCtxProgram.interpret_program]
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure,Prod.map_def,id_eq]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
    conv_rhs => rw [←query_source setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
      erased helper reserve selected position placeholder query seed before prior]
    rw [bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro returned reached
    exact ih returned.1 returned.2
      (call_ready setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position placeholder query seed before prior returned reached)

local notation "PlainState" => RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform mlSource
local notation "plain" => (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (current query))

private theorem observed_step (query : TypedSpec.Domain) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState × List (RegistrationNativeStageTrace.Call TypedSpec PlainState)) (prior : Ready selected seed before.1) :
    Prod.map id (Prod.map RegistrationNativeIdentityCensorActualHashSource.project id) <$>
      (RegistrationNativeObservedStageTrace.handler RegistrationNativeIdentityCensorActualHashSource.project canonical query).run before =
      (RegistrationNativeStageTrace.handler plain query).run
        (RegistrationNativeIdentityCensorActualHashSource.project before.1,before.2) := by
  simp only [RegistrationNativeObservedStageTrace.handler,RegistrationNativeStageTrace.handler,StateT.run,Functor.map_map,Prod.map_def,id_eq]
  have law := congrArg (fun distribution =>
    (fun result : TypedSpec.Range query × PlainState => (result.1,(result.2,before.2 ++
      [⟨query,RegistrationNativeIdentityCensorActualHashSource.project before.1,result.1,result.2⟩]))) <$> distribution)
    (query_source setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder query seed before.1 prior)
  simpa only [Functor.map_map,Prod.map_def,id_eq,handler,StateT.run] using law

/-- The same canonical/original source equation retains the exact chronological private callback journal. The live source backend remains complete, and the journal is proof state rather than executable E state. -/
theorem observed_source (work : OracleComp TypedSpec A) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState) (leading : List (RegistrationNativeStageTrace.Call TypedSpec PlainState)) (prior : Ready selected seed before) :
    Prod.map id (Prod.map RegistrationNativeIdentityCensorActualHashSource.project id) <$>
      (simulateQ (RegistrationNativeObservedStageTrace.handler RegistrationNativeIdentityCensorActualHashSource.project canonical) work).run (before,leading) =
      (simulateQ (RegistrationNativeStageTrace.handler plain) work).run
        (RegistrationNativeIdentityCensorActualHashSource.project before,leading) := by
  induction work using OracleComp.inductionOn generalizing before leading with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure,Prod.map_def,id_eq]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
    conv_rhs => rw [←observed_step setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder query seed (before,leading) prior]
    rw [bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro returned reached
    have ready : Ready selected seed returned.2.1 := by
      simp only [RegistrationNativeObservedStageTrace.handler,StateT.run,support_map] at reached
      obtain ⟨inner,called,rfl⟩ := reached
      exact call_ready setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position placeholder query seed before prior inner called
    exact ih returned.1 returned.2.1 returned.2.2 ready

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource.observed_source
