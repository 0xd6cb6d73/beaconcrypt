-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedActive
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleStopCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient

/-! Repeated selected-message source bundles have the same actual public stopping cut. All failed returns retain their exact continued state; a genuine selected successful publication stops before its different encoded bytes enter the adversary continuation. No rearming, new freshness or private event test is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedStopCut
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOutgoingView (view)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Outcome" => RustM (Option (alloc.vec.Vec U8)) × FullState

open RegistrationNativeIdentityCensorBundleStopCut (RawReply published cut)

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "body(" oneTime ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner oneTime (RegistrationNativePlatformConcreteSource.writer reserve))

/-- The entire actual selected bundle has the same failed-publication subdistribution at its original public boundary, with genuine first-message freshness and the complete Native/private/P poststate. -/
theorem failure_paired (oneTime : PqxdhJointGapDh.ScalarBytes)
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) = .ok started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = some (absBytes started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed) :
    RegistrationNativeIdentityCensorBundleFailureSource.failure placeholder <$> (source(false, body(oneTime))).run before =
      RegistrationNativeIdentityCensorBundleFailureSource.failure placeholder <$> (source(true, body(oneTime))).run before := by
  rw [RegistrationNativeIdentityCensorBundleFailureSource.source, RegistrationNativeIdentityCensorBundleFailureSource.source]
  have same := RegistrationNativeIdentityCensorRepeatedSource.publication setup checks representation created selected index owner placeholder reserve
    (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
    (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) owner.pin owner.mldsa.publicKey
    started built rfl before seed handle held sourceTarget found
  have mapped := congrArg (fun distribution => (fun returned => returned.1.map (fun _ => returned.2)) <$> distribution) same
  have observed : (fun returned : RegistrationNativePlatformIdentityBundle.Reply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource) =>
      (RegistrationNativeIdentityReadyFailure.observe returned.1).map (fun _ => view placeholder returned.2)) = RegistrationNativeIdentityCensorBundleFailureSource.publication placeholder := by
    funext returned
    rcases returned with ⟨reply, state⟩
    cases reply with
    | fail error | div => rfl
    | ok value => cases value <;> rfl
  simpa only [Functor.map_map, Prod.map_def, observed] using mapped

private theorem cut_failure (censored : Bool) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) = .ok started)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (held : before.1.2.target = some (absBytes started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed) (result : Outcome)
    (possible : result ∈ support ((source(censored, body(oneTime))).run before)) :
    cut placeholder result = (RegistrationNativeIdentityCensorBundleFailureSource.failure placeholder result).map
      (fun after => ((RustM.ok none : RawReply), after)) := by
  have normal := RegistrationNativeIdentityCensorBundleFailureSource.normal setup checks representation created selected index owner placeholder reserve censored oneTime before result possible
  rcases result with ⟨returned, after⟩
  cases returned with
  | fail error | div => cases normal
  | ok optional => cases optional with
    | none =>
      simp only [cut, published, RegistrationNativePlatformIdentityNativeBundle.reply, bind_tc_ok,
        RegistrationNativeRawAdapter.resultOption, RegistrationNativeIdentityCensorBundleFailureSource.failure,
        Option.isSome_none, Bool.and_false, Bool.false_eq_true, ite_false, Option.map_none, Option.map_some]
    | some encoded =>
      have active := RegistrationNativeIdentityCensorRepeatedActive.bundled setup checks representation created selected index owner placeholder reserve censored oneTime
        started built before seed handle held sourceTarget found encoded after possible
      simp only [cut, published, RegistrationNativePlatformIdentityNativeBundle.reply, bind_tc_ok,
        RegistrationNativeRawAdapter.resultOption, RegistrationNativeIdentityCensorBundleFailureSource.failure,
        active, Option.map_some, Option.isSome_some, Bool.and_self, ite_true, Option.map_none]

private theorem cut_source (censored : Bool) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) = .ok started)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (held : before.1.2.target = some (absBytes started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed) :
    cut placeholder <$> (source(censored, body(oneTime))).run before =
      (fun state => state.map (fun after => ((RustM.ok none : RawReply), after))) <$>
        RegistrationNativeIdentityCensorBundleFailureSource.failure placeholder <$> (source(censored, body(oneTime))).run before := by
  rw [Functor.map_map]
  simp only [map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro result possible
  dsimp only [Function.comp_def]
  exact congrArg (fun value => (pure value : ProbComp _))
    (cut_failure setup checks representation created selected index owner placeholder reserve censored oneTime started built before seed handle held sourceTarget found result possible)

/-- At the actual public stopping cut, the full captured selected source bundle has identical canonical/placeholder behavior. Failed returns retain their public reply and full projected Native/private/P state; successful active returns stop before a differing byte string can enter the adversary continuation. -/
theorem paired (oneTime : PqxdhJointGapDh.ScalarBytes)
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) = .ok started)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (held : before.1.2.target = some (absBytes started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed) :
    cut placeholder <$> (source(false, body(oneTime))).run before =
      cut placeholder <$> (source(true, body(oneTime))).run before := by
  rw [cut_source setup checks representation created selected index owner placeholder reserve false oneTime started built before seed handle held sourceTarget found,
    cut_source setup checks representation created selected index owner placeholder reserve true oneTime started built before seed handle held sourceTarget found]
  rw [failure_paired setup checks representation created selected index owner placeholder reserve
    oneTime started built before seed handle held sourceTarget found]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedStopCut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedStopCut.failure_paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedStopCut.failure_paired
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedStopCut.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedStopCut.paired
