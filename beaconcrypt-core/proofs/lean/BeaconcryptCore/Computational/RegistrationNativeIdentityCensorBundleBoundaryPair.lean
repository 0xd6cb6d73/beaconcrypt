-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveUnselected

/-! At the original first-issued public bundle boundary, the genuine selected row suffices for the full real/censored adaptive before-accept comparison. The current source callback derives the selected-target or unused-guess suffix case, with every failure and private source state retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleBoundaryPair
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

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem normalized_source (masked : Bool) (query : TypedSpec.Domain) (before : FullState) :
    (interpret setup.joint selected placeholder masked (current query)).run before =
      Prod.map id view <$> (interpret setup.joint selected placeholder masked (actual query)).run before := by
  simp only [RegistrationNativeIdentityCensorAdaptivePostselection.normalized,interpret,StateT.run,simulateQ_map,map_apply,
    bind_pure_comp,Functor.map_map,RegistrationNativeIdentityCensorOutgoingView.view,Prod.map_def,id_eq]

omit primitive in
private theorem main_count (masked : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : FullState) (result : A × FullState)
    (reached : result ∈ support ((interpret setup.joint selected placeholder masked work).run before)) :
    result.2.1.2.bundles = before.1.2.bundles := by
  simp only [interpret,StateT.run,bind_pure_comp,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  exact RegistrationNativeIdentityCensorBundleCounter.source selected placeholder _ (work.run before.1.1) before.1.2 before.2 inner called

omit primitive in
private theorem main_row (masked : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (found : before.2.pool.seeds[selected]? = some seed)
    (result : A × FullState)
    (reached : result ∈ support ((interpret setup.joint selected placeholder masked work).run before)) :
    result.2.2.pool.seeds[selected]? = some seed := by
  simp only [interpret,StateT.run,bind_pure_comp,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  exact RegistrationNativeIdentityCensorSelectedInvariant.row_program setup.joint selected placeholder masked seed _ before.2 found inner called

/-- The actual first guessed bundle has the same public surviving reply, including all unsuccessful current calls and dynamic writer failures. -/
theorem call_cut (index : Nat) (before : FullState)
    (held : before.1.2.target = none) (sourceHeld : before.2.target = none)
    (seed : PqxdhJointIdentity.IdentitySeed) (found : before.2.pool.seeds[selected]? = some seed) :
    RegistrationNativeIdentityCensorAdaptivePostselection.cut (.inr (.bundle index)) <$> called(false,.inr (.bundle index),before) =
      RegistrationNativeIdentityCensorAdaptivePostselection.cut (.inr (.bundle index)) <$> called(true,.inr (.bundle index),before) := by
  simp only [RegistrationNativeIdentityCensorAdaptivePostselection.call,normalized_source,Functor.map_map]
  change RegistrationNativeIdentityCensorPostselectionBundleCut.replyCut placeholder <$>
      (interpret setup.joint selected placeholder false
        (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created
          (RegistrationNativePlatformConcreteSource.writer reserve) index)).run (entered(.inr (.bundle index),before)) =
    RegistrationNativeIdentityCensorPostselectionBundleCut.replyCut placeholder <$>
      (interpret setup.joint selected placeholder true
        (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created
          (RegistrationNativePlatformConcreteSource.writer reserve) index)).run (entered(.inr (.bundle index),before))
  exact RegistrationNativeIdentityCensorPreselectionBundleCut.callback setup checks representation created selected index placeholder reserve
    (entered(.inr (.bundle index),before)) held sourceHeld
    (RegistrationNativeIdentityCensorCompiler.enter_inactive position (.inr (.bundle index)) before.1.2)
    (by intro owner _lookup _selected; exact ⟨seed,found⟩)

private theorem after_cut (index : Nat) (before : FullState) (atBundle : before.1.2.bundles = position)
    (held : before.1.2.target = none) (sourceHeld : before.2.target = none)
    (seed : PqxdhJointIdentity.IdentitySeed) (found : before.2.pool.seeds[selected]? = some seed)
    (kept : TypedSpec.Range (.inr (.bundle index)) × FullState)
    (reached : some kept ∈ support (RegistrationNativeIdentityCensorAdaptivePostselection.cut (.inr (.bundle index)) <$>
      called(true,.inr (.bundle index),before))) :
    RegistrationNativeIdentityCensorAdaptiveUnselected.Passed position kept.2 ∨
      ∃ target, RegistrationNativeIdentitySigningRole.oneTime target = true ∧
        RegistrationNativeIdentityCensorAdaptivePostselection.Selected selected target seed kept.2 := by
  rw [support_map] at reached
  obtain ⟨result,called,same⟩ := reached
  unfold RegistrationNativeIdentityCensorAdaptivePostselection.cut at same
  split at same
  · cases same
  · have literal : result = kept := Option.some.inj same
    subst result
    have count := main_count setup selected placeholder true (current (.inr (.bundle index)))
      (entered(.inr (.bundle index),before)) kept called
    change kept.2.1.2.bundles = before.1.2.bundles + 1 at count
    rw [atBundle] at count
    have sync := RegistrationNativeIdentityCensorTargetSyncMain.main setup.joint selected placeholder true (current (.inr (.bundle index)))
      (entered(.inr (.bundle index),before)) (held.trans sourceHeld.symm) kept called
    have tagged := RegistrationNativeIdentityCensorTargetRole.main setup.joint selected placeholder true (current (.inr (.bundle index)))
      (entered(.inr (.bundle index),before)) (by intro target same; change before.1.2.target = some target at same; rw [held] at same; cases same) kept called
    have row := main_row setup selected placeholder true (current (.inr (.bundle index)))
      (entered(.inr (.bundle index),before)) seed found kept called
    cases target : kept.2.1.2.target with
    | none => exact Or.inl ⟨by omega,target⟩
    | some targetValue => exact Or.inr ⟨targetValue,tagged targetValue target,target,sync.symm.trans target,row⟩


private theorem visit_query (masked : Bool) (accept : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : FullState × Nat) :
    run(masked, accept, (TypedSpec.query query >>= next), before) =
      (match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query before.2 with
      | some packet => pure (before.1.1.2.target.map fun message => (message, packet))
      | none => do
          let selectedCut ← RegistrationNativeIdentityCensorAdaptivePostselection.cut query <$> called(masked, query, before.1)
          match selectedCut with
          | none => pure none
          | some kept => run(masked, accept, (next kept.1), (kept.2, before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0))) := by rfl

private theorem bundle_step (masked : Bool) (accept index : Nat)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : FullState × Nat) :
    run(masked,accept,(TypedSpec.query (.inr (.bundle index)) >>= next),before) = (do
      let selectedCut ← RegistrationNativeIdentityCensorAdaptivePostselection.cut (.inr (.bundle index)) <$> called(masked,.inr (.bundle index),before.1)
      match selectedCut with
      | none => pure none
      | some kept => run(masked,accept,(next kept.1),(kept.2,before.2))) := by
  rw [visit_query]
  simp only [RegistrationNativeIdentityCensorAdaptivePostselection.attempt,RegistrationNativeIdentityCensorPublicClient.IsAccept,ite_false,Nat.add_zero]
  apply bind_congr
  intro selectedCut
  cases selectedCut <;> rfl

/-- At the first-issued public b boundary, the real and placeholder source have identical complete before-a packet observations. A failed selection leaves an unused guess; a successful selection derives its tagged target and genuine row for every later adaptive callback. -/
theorem paired (accept index : Nat)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A)
    (before : FullState × Nat) (atBundle : before.1.1.2.bundles = position)
    (held : before.1.1.2.target = none) (sourceHeld : before.1.2.target = none)
    (seed : PqxdhJointIdentity.IdentitySeed) (found : before.1.2.pool.seeds[selected]? = some seed) :
    run(false,accept,(TypedSpec.query (.inr (.bundle index)) >>= next),before) =
      run(true,accept,(TypedSpec.query (.inr (.bundle index)) >>= next),before) := by
  rw [bundle_step,bundle_step,call_cut setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder index before.1 held sourceHeld seed found]
  apply bind_congr_of_forall_mem_support
  intro selectedCut reached
  cases selectedCut with
  | none => rfl
  | some kept =>
    rcases after_cut setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder index before.1 atBundle held sourceHeld seed found kept reached with passed | selectedAfter
    · exact RegistrationNativeIdentityCensorAdaptiveUnselected.paired setup checks wire route representation created credential keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder accept (next kept.1) (kept.2,before.2) passed
    · obtain ⟨target,role,prior⟩ := selectedAfter
      exact RegistrationNativeIdentityCensorAdaptivePostselection.paired setup checks wire route representation created credential keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder accept (next kept.1) target role seed (kept.2,before.2) prior

/-- Retain the same surviving bundle reply and full poststate beside its entire before-accept observation. Publication refusal remains an ordinary absent branch. -/
noncomputable def retained (masked : Bool) (accept index : Nat)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : FullState × Nat) := do
  let selectedCut ← RegistrationNativeIdentityCensorAdaptivePostselection.cut (.inr (.bundle index)) <$>
    called(masked,.inr (.bundle index),before.1)
  match selectedCut with
  | none=>pure none
  | some kept=>(fun found=>some (kept,found)) <$> run(masked,accept,(next kept.1),(kept.2,before.2))

/-- The same first-issued public bundle preserves its surviving reply, complete reached state and later packet jointly through the real/censored comparison. -/
theorem paired_joint (accept index : Nat)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A)
    (before : FullState × Nat) (atBundle : before.1.1.2.bundles=position)
    (held : before.1.1.2.target=none) (sourceHeld : before.1.2.target=none)
    (seed : PqxdhJointIdentity.IdentitySeed) (found : before.1.2.pool.seeds[selected]?=some seed) :
    retained setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder false accept index next before=
    retained setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder true accept index next before := by
  unfold retained
  rw [call_cut setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder index before.1 held sourceHeld seed found]
  apply bind_congr_of_forall_mem_support
  intro selectedCut reached
  cases selectedCut with
  | none=>rfl
  | some kept=>
    rcases after_cut setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder index before.1 atBundle held sourceHeld seed found kept reached with passed|selectedAfter
    · exact congrArg (Functor.map (fun answer=>some (kept,answer)))
        (RegistrationNativeIdentityCensorAdaptiveUnselected.paired setup checks wire route representation created credential keys failure allocation
          reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder accept (next kept.1) (kept.2,before.2) passed)
    · obtain ⟨target,role,prior⟩ := selectedAfter
      exact congrArg (Functor.map (fun answer=>some (kept,answer)))
        (RegistrationNativeIdentityCensorAdaptivePostselection.paired setup checks wire route representation created credential keys failure allocation
          reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder accept (next kept.1) target role seed (kept.2,before.2) prior)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleBoundaryPair

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleBoundaryPair.call_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleBoundaryPair.call_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleBoundaryPair.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleBoundaryPair.paired

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleBoundaryPair.paired_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleBoundaryPair.paired_joint
