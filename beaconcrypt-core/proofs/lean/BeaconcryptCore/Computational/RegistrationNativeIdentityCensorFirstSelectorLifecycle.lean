-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelector
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource
/-! Actual owner lookup and fresh or supplied scalar dispatch retain the same first operational selector and private cut. Only ordinary uniform requests precede the captured body. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorLifecycle
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorSource (State)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (poolMessages)
open PqxdhEd25519EufCma (Ed25519Signature)
open PqxdhServerAuthExperiment (Setup Checks)
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
abbrev Cut := RegistrationNativeIdentityTemplateSelectionCut.Original.Cut
variable {A B : Type}

private def NoSelector : Old.Domain → Prop
  | .inl (.inl (.inl (.inr _))) => False
  | _ => True

private theorem stop_bind (work : OracleComp Old A) (next : A → OracleComp Old B)
    (quiet : work.AllQueriesSatisfy NoSelector) :
    RegistrationNativeIdentityTemplateSelectionCut.Original.stop (work >>= next) =
      work >>= fun result=>RegistrationNativeIdentityTemplateSelectionCut.Original.stop (next result) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [pure_bind]
  | query_bind query later ih =>
      rw [allQueriesSatisfy_query_bind_iff] at quiet
      rw [bind_assoc,RegistrationNativeIdentityTemplateSelectionCut.Original.step]
      rcases query with (((protocol|message)|scanned)|hash)|marker
      · simp only [bind_assoc]
        exact bind_congr (fun reply=>ih reply (quiet.2 reply))
      · exact False.elim quiet.1
      · simp only [bind_assoc]
        exact bind_congr (fun reply=>ih reply (quiet.2 reply))
      · simp only [bind_assoc]
        exact bind_congr (fun reply=>ih reply (quiet.2 reply))
      · simp only [bind_assoc]
        exact bind_congr (fun reply=>ih reply (quiet.2 reply))

private theorem uniform_quiet (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Source A) (quiet : work.AllQueriesSatisfy RegistrationNativePlatformIdentityCtxMldsaCoins.Coin)
    (mode : Mode) :
    ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode).AllQueriesSatisfy NoSelector := by
  induction work using OracleComp.inductionOn generalizing mode with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind request next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at quiet
      rcases request with ((coin|request)|report)|bytes
      · simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
        change (do
          let reply ← (Old.query (.inl (.inl (.inl (.inl (.inl (.inl coin)))))) : OracleComp Old _)
          (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (next reply)).run mode : OracleComp Old (A × Mode)).AllQueriesSatisfy _
        exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,fun reply=>ih reply (quiet.2 reply) mode⟩
      · exact False.elim quiet.1
      · exact False.elim quiet.1
      · exact False.elim quiet.1

variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "NativeState" => RegistrationNativeIdentityMain.State n KemSK source × Platform
local notation "Action" => RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source

def Receipt (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (wanted : Pqxdh.Bytes) (work : Action A) (nativeBefore : NativeState) (mode : Mode) (before : State) : Prop :=
  ∀ (cut : Cut ((A × NativeState) × Mode) × State),
    cut∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run nativeBefore)).run mode))).run before) →
  ∀ (result : ((A × NativeState) × Mode) × State),
    result∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2) →
    wanted∈poolMessages selected result.2.pool →
      ∃ continued,cut.1=RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected wanted continued ∧
        wanted∉poolMessages selected cut.2.pool

private theorem pure_receipt (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (wanted : Pqxdh.Bytes) (value : A) (nativeBefore : NativeState) (mode : Mode) (before : State)
    (fresh : wanted∉poolMessages selected before.pool) :
    Receipt joint selected placeholder masked wanted (pure value) nativeBefore mode before := by
  intro cut stopped result resumed member
  change cut∈support (pure (.returned ((value,nativeBefore),mode),before)) at stopped
  obtain rfl := eq_of_mem_support_pure _ stopped
  change result∈support (pure (((value,nativeBefore),mode),before)) at resumed
  obtain rfl := eq_of_mem_support_pure _ resumed
  exact False.elim (fresh member)

private theorem uniform_bind (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (wanted : Pqxdh.Bytes) (work : Action A) (next : A → Action B)
    (coins : ∀ current,(work.run current).AllQueriesSatisfy RegistrationNativePlatformIdentityCtxMldsaCoins.Coin)
    (later : ∀ value current mode before,RegistrationNativeIdentityCensorFirstSelectorPrefix.Armed mode →
      wanted∉poolMessages selected before.pool → Receipt joint selected placeholder masked wanted (next value) current mode before)
    (nativeBefore : NativeState) (mode : Mode) (held : RegistrationNativeIdentityCensorFirstSelectorPrefix.Armed mode)
    (before : State) (fresh : wanted∉poolMessages selected before.pool) :
    Receipt joint selected placeholder masked wanted (work >>= next) nativeBefore mode before := by
  intro cut stopped result resumed member
  simp only [StateT.run_bind,simulateQ_bind] at stopped
  rw [stop_bind _ _ (uniform_quiet selected placeholder (work.run nativeBefore) (coins nativeBefore) mode)] at stopped
  simp only [simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at stopped
  obtain ⟨middle,drawn,stopped⟩ := stopped
  have framed := RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_frame joint selected placeholder masked
    (work.run nativeBefore) (coins nativeBefore) mode before middle drawn
  have modeSame : middle.1.2=mode := congrArg Prod.fst framed
  have history := congrArg (fun current=>PqxdhJointIdentity.signedMessages
    (RegistrationNativeIdentityHistory.history selected current.2.pool.transcript)) framed
  simp only [RegistrationNativeIdentityCensorMldsaOutgoingSource.stable,RegistrationNativeIdentityHistoryObservation.pool_view_history] at history
  have freshAt : wanted∉poolMessages selected middle.2.pool := by
    intro old
    change wanted∈PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected middle.2.pool.transcript) at old
    rw [history] at old
    exact fresh old
  exact later middle.1.1.1 middle.1.1.2 middle.1.2 middle.2 (modeSame ▸ held) freshAt cut stopped result resumed member

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected index : Nat) (placeholder : Ed25519Signature) (masked : Bool) (wanted : Pqxdh.Bytes)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := source) setup checks representation created

/-- Actual fresh sampling or supplied scalar reuse reaches the same retained selector before the original bundled body. -/
theorem start (owner : RegistrationNativeIdentityFrontend.Owner source)
    (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (nativeBefore : NativeState) (mode : Mode) (held : RegistrationNativeIdentityCensorFirstSelectorPrefix.Armed mode)
    (before : State) (fresh : wanted∉poolMessages selected before.pool) :
    Receipt setup.joint selected placeholder masked wanted
      (Main (RegistrationNativePlatformIdentityBundleRun.start setup index owner writer)) nativeBefore mode before := by
  cases phase : owner.phase with
  | fresh =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start,phase]
      rw [RegistrationNativePlatformIdentityCtxOutgoingFold.bind_source setup checks representation created _ _
        (fun scalar=>RegistrationNativePlatformIdentityCtxBundleScope.bundled setup index owner scalar writer)]
      apply uniform_bind setup.joint selected placeholder masked wanted _ _
        (RegistrationNativePlatformIdentityCtxSampleCoins.sample setup checks representation created PqxdhJointGapDh.sampleScalar) _ nativeBefore mode held before fresh
      intro scalar current nextMode currentPrivate armed newFresh
      exact RegistrationNativeIdentityCensorFirstSelector.bundled setup checks representation created selected index owner scalar writer placeholder masked wanted role
        current nextMode armed currentPrivate newFresh
  | freshWithCoins scalar =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start,phase,pure_bind]
      exact RegistrationNativeIdentityCensorFirstSelector.bundled setup checks representation created selected index owner scalar writer placeholder masked wanted role
        nativeBefore mode held before fresh
  | initSent pending scalar | established completed | aborted aborted =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start,phase,
        RegistrationNativePlatformIdentityCtxOutgoingFold.pure_source]
      exact pure_receipt setup.joint selected placeholder masked wanted _ nativeBefore mode before fresh

/-- The complete original owner lookup excludes missing and rejected branches by the actual new-history crossing, including every failed writer. -/
theorem bundle (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (nativeBefore : NativeState) (mode : Mode) (held : RegistrationNativeIdentityCensorFirstSelectorPrefix.Armed mode)
    (before : State) (fresh : wanted∉poolMessages selected before.pool) :
    Receipt setup.joint selected placeholder masked wanted
      (Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer)) nativeBefore mode before := by
  have lookup : (Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer)).run nativeBefore =
      (match nativeBefore.1.beacons[index]? with
      | none => pure (.ok none,nativeBefore)
      | some owner => (Main (RegistrationNativePlatformIdentityBundleRun.start setup index owner writer)).run nativeBefore) := by
    rw [RegistrationNativePlatformIdentityCtxBundleScope.bundle_fold,StateT.run_bind]
    change (do let p ← (pure (nativeBefore.1.beacons,nativeBefore) :
                 OracleComp Source (RegistrationNativeIdentityFrontend.State source × NativeState))
               _) = _
    rw [pure_bind]
    cases nativeBefore.1.beacons[index]? <;> rfl
  unfold Receipt
  rw [lookup]
  cases found : nativeBefore.1.beacons[index]? with
  | none =>
      exact pure_receipt setup.joint selected placeholder masked wanted (.ok none : RustM (Option (alloc.vec.Vec U8))) nativeBefore mode before fresh
  | some owner =>
      exact start setup checks representation created selected index placeholder masked wanted writer owner role nativeBefore mode held before fresh

private def mapCut (change : A → B) : Cut A → Cut B
  | .returned value => .returned (change value)
  | .selected message next => .selected message (fun reply=>change <$> next reply)

private theorem stop_map (change : A → B) (work : OracleComp Old A) :
    RegistrationNativeIdentityTemplateSelectionCut.Original.stop (change <$> work)=
      mapCut change <$> RegistrationNativeIdentityTemplateSelectionCut.Original.stop work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [map_pure,RegistrationNativeIdentityTemplateSelectionCut.Original.stop]; rfl
  | query_bind query next ih =>
      rw [map_bind,RegistrationNativeIdentityTemplateSelectionCut.Original.step,
        RegistrationNativeIdentityTemplateSelectionCut.Original.step]
      rcases query with (((protocol|message)|scanned)|hash)|marker
      · simp only [map_bind,ih]
      · simp only [map_pure]; rfl
      · simp only [map_bind,ih]
      · simp only [map_bind,ih]
      · simp only [map_bind,ih]

private theorem resume_map (change : A → B) (cut : Cut A) :
    RegistrationNativeIdentityTemplateSelectionCut.Original.resume (mapCut change cut)=
      change <$> RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut := by
  cases cut with
  | returned value => simp only [mapCut,RegistrationNativeIdentityTemplateSelectionCut.Original.resume,map_pure]
  | selected message next => simp only [mapCut,RegistrationNativeIdentityTemplateSelectionCut.Original.resume,map_bind]; rfl

private theorem mapped_receipt (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (wanted : Pqxdh.Bytes) (change : A → B) (work : Action A)
    (nativeBefore : NativeState) (mode : Mode) (before : State)
    (original : Receipt joint selected placeholder masked wanted work nativeBefore mode before) :
    Receipt joint selected placeholder masked wanted (change <$> work) nativeBefore mode before := by
  intro cut stopped result resumed member
  simp only [StateT.run_map,simulateQ_map] at stopped
  rw [stop_map,simulateQ_map,StateT.run_map,support_map] at stopped
  obtain ⟨originalCut,called,same⟩ := stopped
  subst cut
  rw [resume_map,simulateQ_map,StateT.run_map,support_map] at resumed
  obtain ⟨originalResult,reached,same⟩ := resumed
  subst result
  obtain ⟨next,selected,fresh⟩ := original originalCut called originalResult reached member
  dsimp only
  rw [selected]
  exact ⟨_,rfl,fresh⟩

/-- The literal lifecycle byte conversion preserves the same first-selector receipt and all reached source/platform state. -/
theorem lifecycle (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (nativeBefore : NativeState) (mode : Mode) (held : RegistrationNativeIdentityCensorFirstSelectorPrefix.Armed mode)
    (before : State) (fresh : wanted∉poolMessages selected before.pool) :
    Receipt setup.joint selected placeholder masked wanted
      (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index) nativeBefore mode before := by
  unfold RegistrationNativePlatformIdentityCtxLifecycle.bundle
  exact mapped_receipt setup.joint selected placeholder masked wanted _ _ nativeBefore mode before
    (bundle setup checks representation created selected index placeholder masked wanted writer role nativeBefore mode held before fresh)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorLifecycle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorLifecycle.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorLifecycle.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorLifecycle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorLifecycle.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorLifecycle.lifecycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorLifecycle.lifecycle
