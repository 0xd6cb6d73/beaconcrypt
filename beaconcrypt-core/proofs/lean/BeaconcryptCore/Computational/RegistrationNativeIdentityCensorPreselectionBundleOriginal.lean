-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNonselectedOriginal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleBeginSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBundleSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary

/-! Exhaustive original source marginal for a captured current bundle before target selection. Public entry inactivity, owner lookup and actual first/stale selection branches retain the same reply, full native/pool/hash/platform poststate and terminal owner effect. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleOriginal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E A Q : Type} {base : OracleSpec I} {queries : OracleSpec Q} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "original(" work ")" => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint work
local notation "tree(" scalar ")" => RegistrationNativePlatformWriter.begin E (pqxdh.BeaconFresh.mk owner.pin.binding)
  (RegistrationNativeIdentityFrontend.inputs owner) (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) owner.pin owner.mldsa.publicKey
local notation "publication(" scalar ")" => Main (simulateQ
  (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
    setup index owner (RegistrationNativePlatformConcreteSource.writer reserve)) (tree(scalar)))
local notation "body(" scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar (RegistrationNativePlatformConcreteSource.writer reserve))

private theorem original_program
    (impl : QueryImpl queries (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource)) (work : OracleComp queries A) :
    original(simulateQ impl work) = simulateQ (fun query => original(impl query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure setup.joint value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, ih]

private theorem terminal (censored : Bool) (scalar : PqxdhJointGapDh.ScalarBytes) (reply : RegistrationNativePlatformIdentityBundle.Reply)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    let action := Main (RegistrationNativePlatformIdentityBundle.next index owner scalar reply)
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(censored, action)).run before =
      (original(action)).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  dsimp only
  have real := RegistrationNativeIdentityCensorRealSigning.main setup.joint selected placeholder
    (Main (RegistrationNativePlatformIdentityBundle.next index owner scalar reply)) before (by
      rw [RegistrationNativeIdentityCensorBundleTerminal.next_run]
      trivial)
  cases censored with
  | false => exact real
  | true =>
    rw [RegistrationNativeIdentityCensorBundleTerminal.source] at real ⊢
    exact real

/-- A captured bundle under another opaque owner handle has its original source marginal before or after selection, including failed writes. -/
theorem other (different : owner.identity.handle ≠ selected) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (inactive : before.1.2.active = false) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(false, body(scalar))).run before =
      (original(body(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  have initial : Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(false, publication(scalar))).run before =
      (original(publication(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
    rw [RegistrationNativeIdentityCensorSourceFold.publication]
    conv_rhs => rw [RegistrationNativePlatformIdentityCtxOutgoingFold.publication, original_program]
    exact RegistrationNativeIdentityCensorNonselectedOriginal.program setup checks representation created selected index owner placeholder
      (RegistrationNativePlatformConcreteSource.writer reserve) different (tree(scalar)) before inactive
  simp only [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold, RegistrationNativeIdentityCensorSourceFold.bind_source,
    RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind, map_bind]
  rw [← initial, bind_map_left]
  apply bind_congr
  intro result
  simpa only [Prod.map, id_eq] using terminal setup checks representation created selected index owner placeholder false scalar result.1 result.2

/-- A stale selected captured bundle declines target selection and retains its full original source marginal through begin, publication and terminal owner updates. -/
theorem stale (scalar : PqxdhJointGapDh.ScalarBytes) (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (issued : absBytes started.message.one_time_key ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(false, body(scalar))).run before =
      (original(body(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  have initial : Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(false, publication(scalar))).run before =
      (original(publication(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
    rw [RegistrationNativeIdentityCensorPublicationSource.source setup checks representation created selected index owner placeholder reserve false,
      RegistrationNativeIdentityCensorOriginalPublication.source setup checks representation created index owner reserve]
    exact RegistrationNativeIdentityCensorStaleBeginSource.begin setup checks representation created index owner
      (RegistrationNativeIdentityCensorConcreteWriter.encode reserve) selected placeholder _ _ _ _ _ started built rfl
      before seed handle held sourceTarget issued found
  simp only [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold, RegistrationNativeIdentityCensorSourceFold.bind_source,
    RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind, map_bind]
  rw [← initial, bind_map_left]
  apply bind_congr
  intro result
  simpa only [Prod.map, id_eq] using terminal setup checks representation created selected index owner placeholder false scalar result.1 result.2

/-- At an actual inactive bundle entry with no prior target, every different-owner, unarmed, fresh-selected and stale-selected branch has the original full source marginal. -/
theorem before_selection (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (inactive : before.1.2.active = false) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (row : owner.identity.handle = selected → ∃ seed, before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(false, body(scalar))).run before =
      (original(body(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  classical
  obtain ⟨started, built⟩ := BeaconcryptCore.PanicFreedom.beacon_start_ok (pqxdh.BeaconFresh.mk owner.pin.binding)
    (RegistrationNativeIdentityFrontend.inputs owner)
    (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)))
  by_cases handle : owner.identity.handle = selected
  · obtain ⟨seed, found⟩ := row handle
    by_cases armed : before.1.2.armed = true
    · by_cases issued : absBytes started.message.one_time_key ∈ PqxdhJointIdentity.signedMessages
          (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript)
      · exact stale setup checks representation created selected index owner placeholder reserve scalar started built before seed handle held sourceTarget issued found
      · exact RegistrationNativeIdentityCensorRealBundleSource.first setup checks representation created selected index owner placeholder reserve
          scalar started built before seed handle armed held sourceTarget issued found
    · exact RegistrationNativeIdentityCensorUnarmedMain.source setup.joint selected placeholder false (body(scalar)) before
        ⟨Bool.eq_false_iff.mpr armed, held, inactive⟩
  · exact other setup checks representation created selected index owner placeholder reserve handle scalar before inactive

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleOriginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleOriginal.other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleOriginal.other

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleOriginal.stale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleOriginal.stale

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleOriginal.before_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleOriginal.before_selection
