-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal

/-! The actual selected bundle has the same failed-publication subdistribution after canonical or placeholder delivery. Successful source publications are absorbed by the public stopping observation; their encoded bytes and installed pending states are not equated. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleFailureSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOutgoingView (view)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

def failure (placeholder : Ed25519Signature)
    (result : RustM (Option (alloc.vec.Vec U8)) × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    Option (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :=
  match result.1 with
  | .ok none => some (view placeholder result.2)
  | _ => none

def publication (placeholder : Ed25519Signature)
    (result : RegistrationNativePlatformIdentityBundle.Reply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    Option (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :=
  match result.1 with
  | .ok (.Err _) => some (view placeholder result.2)
  | _ => none

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "body(" oneTime ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner oneTime (RegistrationNativePlatformConcreteSource.writer reserve))
local notation "publish(" oneTime ")" => Main (simulateQ
  (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
    setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
  (RegistrationNativePlatformWriter.begin E (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
    (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) owner.pin))

private theorem terminal (censored : Bool) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RegistrationNativePlatformIdentityBundle.Reply)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    failure placeholder <$> (source(censored, Main (RegistrationNativePlatformIdentityBundle.next index owner oneTime reply))).run before =
      pure (publication placeholder (reply, before)) := by
  rw [RegistrationNativeIdentityCensorBundleTerminal.source setup checks representation created index owner oneTime reply selected placeholder censored before, map_pure]
  cases reply with
  | fail error | div => rfl
  | ok value => cases value <;> rfl

/-- The literal terminal controller preserves each failed source state. Its successful branches are absorbed exactly at publication, after their real phase/World transition. -/
theorem source (censored : Bool) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    failure placeholder <$> (source(censored, body(oneTime))).run before =
      publication placeholder <$> (source(censored, publish(oneTime))).run before := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold,
    RegistrationNativeIdentityCensorSourceFold.bind_source]
  simp only [StateT.run_bind, map_bind]
  rw [map_eq_bind_pure_comp]
  apply bind_congr
  intro returned
  exact terminal setup checks representation created selected index owner placeholder censored oneTime returned.1 returned.2

/-- The entire actual selected bundle has the same failed-publication subdistribution at its original public boundary, with genuine first-message freshness and the complete Native/private/P poststate. -/
theorem paired (oneTime : PqxdhJointGapDh.ScalarBytes)
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) = .ok started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    failure placeholder <$> (source(false, body(oneTime))).run before =
      failure placeholder <$> (source(true, body(oneTime))).run before := by
  rw [source, source]
  have same := RegistrationNativeIdentityCensorPublicationSource.paired setup checks representation created selected index owner placeholder reserve
    (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
    (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) owner.pin
    started built rfl before seed handle armed held sourceTarget fresh found
  have mapped := congrArg (fun distribution => (fun returned => returned.1.map (fun _ => returned.2)) <$> distribution) same
  have observed : (fun returned : RegistrationNativePlatformIdentityBundle.Reply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource) =>
      (RegistrationNativeIdentityReadyFailure.observe returned.1).map (fun _ => view placeholder returned.2)) = publication placeholder := by
    funext returned
    rcases returned with ⟨reply, state⟩
    cases reply with
    | fail error | div => rfl
    | ok value => cases value <;> rfl
  simpa only [Functor.map_map, Prod.map_def, observed] using mapped

/-- The literal complete bundle returns normally on every reached result. It cannot manufacture a non-publication stop by abnormal termination. -/
theorem normal (censored : Bool) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (result : RustM (Option (alloc.vec.Vec U8)) × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (possible : result ∈ support ((source(censored, body(oneTime))).run before)) :
    RegistrationNativeIdentityCensorPublicationNormal.Normal result.1 := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold,
    RegistrationNativeIdentityCensorSourceFold.bind_source, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨⟨reply, middle⟩, published, continued⟩ := possible
  have returned := RegistrationNativeIdentityCensorPublicationSource.normal setup checks representation created selected index owner placeholder reserve censored
    (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
    (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime))) owner.pin before (reply, middle) published
  have value := (RegistrationNativeIdentityCensorBundleTerminal.frame setup checks representation created index owner oneTime reply selected placeholder censored middle result continued).1
  rw [value]
  cases reply with
  | fail error | div => cases returned
  | ok reply => cases reply <;> trivial

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleFailureSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleFailureSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleFailureSource.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleFailureSource.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleFailureSource.paired
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleFailureSource.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleFailureSource.normal
