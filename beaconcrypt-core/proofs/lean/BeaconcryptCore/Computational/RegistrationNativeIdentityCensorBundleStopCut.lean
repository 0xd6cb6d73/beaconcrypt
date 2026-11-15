-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationActive
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient

/-! The selected source body is compared at the real public bundle stopping cut: unsuccessful returns retain their exact public reply and projected state, while an active successful publication is absorbed. Actual source normality/flag facts discharge that classification. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleStopCut
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOutgoingView (view)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Outcome" => RustM (Option (alloc.vec.Vec U8)) × FullState

abbrev RawReply := RustM (Option Pqxdh.Bytes)

def published (result : Outcome) : Bool :=
  result.2.1.2.active && (RegistrationNativeRawAdapter.resultOption (RegistrationNativePlatformIdentityNativeBundle.reply result.1)).isSome

def cut (placeholder : Ed25519Signature) (result : Outcome) : Option (RawReply × FullState) :=
  if published result then none else some (RegistrationNativePlatformIdentityNativeBundle.reply result.1, view placeholder result.2)

/-- The cut uses exactly the existing public source callback observer; no private target-publication membership or bad-accept selector is consulted. -/
theorem public_stop (accept index beforeCount afterCount : Nat) (before : FullState) (result : Outcome) :
    (RegistrationNativeIdentityCensorPublicClient.observe
      (S := RegistrationNativeIdentityMain.State n KemSK mlSource × Platform) accept (.inr (.bundle index))
      (before.1, beforeCount) (RegistrationNativePlatformIdentityNativeBundle.reply result.1) (result.2.1, afterCount)).isSome = published result := by
  cases active : result.2.1.2.active <;>
    cases returned : (RegistrationNativeRawAdapter.resultOption (RegistrationNativePlatformIdentityNativeBundle.reply result.1)).isSome <;>
    simp only [RegistrationNativeIdentityCensorPublicClient.observe, published, active, returned,
      Bool.false_eq_true, false_and, true_and, ite_false, ite_true,
      Option.isSome_none, Option.isSome_some, Bool.false_and, Bool.true_and]

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "body(" oneTime ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner oneTime (RegistrationNativePlatformConcreteSource.writer reserve))

private theorem cut_failure (censored : Bool) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) = .ok started)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
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
      have active := RegistrationNativeIdentityCensorPublicationActive.bundled setup checks representation created selected index owner placeholder reserve censored oneTime
        started built before seed handle armed held sourceTarget fresh found encoded after possible
      simp only [cut, published, RegistrationNativePlatformIdentityNativeBundle.reply, bind_tc_ok,
        RegistrationNativeRawAdapter.resultOption, RegistrationNativeIdentityCensorBundleFailureSource.failure,
        active, Option.map_some, Option.isSome_some, Bool.and_self, ite_true, Option.map_none]

private theorem cut_source (censored : Bool) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) = .ok started)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
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
    (cut_failure setup checks representation created selected index owner placeholder reserve censored oneTime started built before seed handle armed held sourceTarget fresh found result possible)

/-- At the actual public stopping cut, the full captured selected source bundle has identical canonical/placeholder behavior. Failed returns retain their public reply and full projected Native/private/P state; successful active returns stop before a differing byte string can enter the adversary continuation. -/
theorem paired (oneTime : PqxdhJointGapDh.ScalarBytes)
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) = .ok started)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed) (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    cut placeholder <$> (source(false, body(oneTime))).run before =
      cut placeholder <$> (source(true, body(oneTime))).run before := by
  rw [cut_source setup checks representation created selected index owner placeholder reserve false oneTime started built before seed handle armed held sourceTarget fresh found,
    cut_source setup checks representation created selected index owner placeholder reserve true oneTime started built before seed handle armed held sourceTarget fresh found]
  rw [RegistrationNativeIdentityCensorBundleFailureSource.paired setup checks representation created selected index owner placeholder reserve
    oneTime started built before seed handle armed held sourceTarget fresh found]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleStopCut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleStopCut.public_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleStopCut.public_stop
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleStopCut.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleStopCut.paired
