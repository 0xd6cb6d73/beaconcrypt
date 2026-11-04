-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconCryptoBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformFrontend
import BeaconcryptCore.Computational.RegistrationNativeBundleCosts
/-! The actual dynamic Init writer adds no old/global cost. One possible scalar draw, all six source crypto callbacks and the retained phase capability give the native bundle bill; external writer coins remain separately accounted. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (EffectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_simulate weighted_run weighted_indicator weighted_bind weighted_mono)
open RegistrationNativePlatformGenericBundle (Spec M trustedLift liftLegacy)
open RegistrationNativeBundleCosts (outgoingCost bundleBill)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativeCreateCosts (administrativeCost)
variable {n : Nat} {I KemSK Auxiliary E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def bill (qKem : Nat) (kind : EffectKind) : (Spec E n KemSK).Domain → Nat
  | .inl query => RegistrationNativeTrustedCosts.bill (KemSK := KemSK) qKem kind query
  | .inr _ => 0

private theorem legacy_bound (qKem : Nat) (kind : EffectKind)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A) (cap : Nat)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (bounded : Weighted (RegistrationNativeTrustedCosts.bill qKem kind) ((work.run owners).run env) cap) :
    Weighted (bill (E := E) qKem kind) (((liftLegacy trustedLift work).run owners).run env) cap := by
  apply weighted_simulate _ _ _ _ _ bounded
  intro query
  simp [trustedLift, Weighted, bill, isQueryBound_query_iff]

/-- The actual shared crypto/writer publication pays only its six source crypto callback bills. -/
theorem publication_bound (setup : Setup base KemSK) (qSign qKem : Nat)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (kind : EffectKind) :
    Weighted (bill (E := E) (n := n) (KemSK := KemSK) qKem kind)
      (((RegistrationNativePlatformBeaconPublication.begin
        (fun query => liftLegacy trustedLift (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (RegistrationNativePlatformGenericBundle.encoder E) ⟨owner.pin.binding⟩
        (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey).run owners).run env)
      (outgoingCost qSign kind * 6) := by
  rw [← RegistrationNativePlatformFrontend.publication_tree]
  apply RegistrationNativeWeightedContext.run_bound
    (fun query => if RegistrationNativePlatformBeaconCryptoBounds.IsCrypto query then outgoingCost qSign kind else 0)
    _ _ _ _ owners env
  · exact weighted_indicator _ _ _ 6 (RegistrationNativePlatformBeaconCryptoBounds.begin_bound _ _ _ _ _)
  · intro query current environment
    cases query with
    | inl query =>
        exact legacy_bound qKem kind _ _ _ _
          (RegistrationNativeBundleCosts.outgoing_bound setup source qSign qKem signing index owner query current environment kind)
    | inr query =>
        simp [RegistrationNativePlatformFrontend.joint, StateT.run_lift, StateT.run_map,
          RegistrationNativePlatformGenericBundle.writerLift, Weighted, bill, isQueryBound_map_iff,
          isQueryBound_query_iff, RegistrationNativePlatformBeaconCryptoBounds.IsCrypto]
private noncomputable def suffix (setup : Setup base KemSK) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    M source RegistrationServerRoleBackend.State (OracleComp (Spec E n KemSK)) (RustM (Option (alloc.vec.Vec U8))) := do
  let published ← RegistrationNativePlatformBeaconPublication.begin
    (fun query => liftLegacy trustedLift (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
    (RegistrationNativePlatformGenericBundle.encoder E) ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
    liftLegacy trustedLift (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime))
    let _ ← liftLegacy trustedLift (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
    pure (.ok (some finished.encoded))

private theorem legacy_modify (change : RegistrationNativeBeaconFrontend.State source → RegistrationNativeBeaconFrontend.State source) :
    liftLegacy (trustedLift (E := E) (n := n) (KemSK := KemSK))
      (modify change : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Unit) = modify change := by
  funext owners env
  rfl

private theorem suffix_bound (setup : Setup base KemSK) (qSign qKem : Nat)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (kind : EffectKind) :
    Weighted (bill (E := E) (n := n) (KemSK := KemSK) qKem kind) (((suffix setup index owner oneTime).run owners).run env)
      (outgoingCost qSign kind * 6 + administrativeCost kind) := by
  simp only [suffix, StateT.run_bind]
  apply weighted_bind _ _ _ _ _ (publication_bound setup qSign qKem signing index owner oneTime owners env kind)
  intro published
  rcases published with ⟨⟨published, after⟩, afterEnvironment⟩
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok finished =>
      simp only [StateT.run_bind, RegistrationNativeBeaconFrontend.updatePhase, legacy_modify,
        StateT.run_modify, pure_bind]
      rw [← Nat.add_zero (administrativeCost kind)]
      apply weighted_bind _ _ _ _ _ (legacy_bound qKem kind _ _ _ _ (by
        cases kind <;> exact RegistrationNativeTrustedCosts.effect_bound source qKem _
          (.inr (.advanceOwner owner.worldOwner .initSent)) _ _))
      intro _
      trivial

attribute [local irreducible] PqxdhJointGapDh.sampleScalar RegistrationNativePlatformBeaconPublication.begin

/-- The literal free dynamic bundle has its native scalar/publication/phase bill on every outcome. -/
theorem program_bound (setup : Setup base KemSK) (qSign qKem : Nat)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (index : Nat) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (kind : EffectKind) :
    Weighted (bill (E := E) (n := n) (KemSK := KemSK) qKem kind)
      (((RegistrationNativePlatformGenericBundle.program E setup source index).run owners).run env)
      (bundleBill qSign kind) := by
  simp only [RegistrationNativePlatformGenericBundle.program, RegistrationNativePlatformGenericBundle.bundle,
    StateT.run_bind, StateT.run_get, pure_bind]
  cases found : owners[index]? with
  | none => simp only [StateT.run_pure]; trivial
  | some owner =>
    simp only []
    cases phase : owner.phase with
    | initSent pending oneTime | established completed | aborted aborted =>
      all_goals simp only [StateT.run_pure]; trivial
    | fresh =>
      simp only [StateT.run_bind]
      have first := legacy_bound (E := E) (n := n) (KemSK := KemSK) qKem kind _ _ owners env
        (RegistrationNativeTrustedCosts.sample_bound (n := n) (KemSK := KemSK) source qKem kind _ 32 PqxdhJointGapDh.sampleScalar_uniform owners env)
      have combined := weighted_bind (bill (E := E) (n := n) (KemSK := KemSK) qKem kind)
        (((liftLegacy trustedLift (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)).run owners).run env)
        (fun sampled => ((suffix setup index owner sampled.1.1).run sampled.1.2).run sampled.2)
        (coinCost 32 kind) (outgoingCost qSign kind * 6 + administrativeCost kind) first
        (fun sampled => suffix_bound (n := n) (KemSK := KemSK) setup qSign qKem signing index owner sampled.1.1 sampled.1.2 sampled.2 kind)
      convert combined using 1
      simp only [suffix, StateT.run_bind]
      apply bind_congr
      intro sampled
      apply bind_congr
      rintro ⟨⟨published, after⟩, afterEnvironment⟩
      cases published with
      | fail error | div => rfl
      | ok result => cases result <;> rfl
      all_goals rfl
    | freshWithCoins oneTime =>
      have bounded := weighted_mono _ _ (outgoingCost qSign kind * 6 + administrativeCost kind)
        (bundleBill qSign kind) (suffix_bound (E := E) (n := n) (KemSK := KemSK) setup qSign qKem signing index owner oneTime owners env kind)
        (by unfold bundleBill; omega)
      convert bounded using 1
      simp only [suffix, StateT.run_bind]
      apply bind_congr
      rintro ⟨⟨published, after⟩, afterEnvironment⟩
      cases published with
      | fail error | div => rfl
      | ok result => cases result <;> rfl
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The actual common-P owner callback keeps the same native bill under every stateful Init writer. -/
theorem owner_bound {Platform : Type} (setup : Setup base KemSK) (qSign qKem : Nat)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment)
    (previous : Platform) (kind : EffectKind) :
    Weighted (RegistrationNativePlatformPublicNativeLocal.bill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((((RegistrationNativePlatformPublicOwners.bundle RegistrationNativePlatformPublicFrontend.trusted
        (RegistrationNativePlatformPublicFrontend.writer implementation) setup source selected publicPrekey index).run owners).run env).run previous)
      (bundleBill qSign kind) := by
  let joint : QueryImpl (Spec E n KemSK) (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform)
    | .inl query => RegistrationNativePlatformPublicFrontend.trusted query
    | .inr query => RegistrationNativePlatformPublicFrontend.writer implementation query
  have actual := RegistrationNativePlatformGenericBundle.program_evaluate
    (source := source) (Auxiliary := RegistrationServerRoleBackend.State) joint setup index
  change RegistrationNativePlatformGenericBundle.evaluate joint _ =
    RegistrationNativePlatformGenericBundle.bundle RegistrationNativePlatformPublicFrontend.trusted setup source
      (RegistrationNativePlatformGenericBundle.encoderWith (RegistrationNativePlatformPublicFrontend.writer implementation)) index at actual
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, Weighted, isQueryBound_map_iff]
  rw [← actual]
  unfold RegistrationNativePlatformGenericBundle.evaluate
  apply weighted_run _ _ joint _ _ previous (program_bound setup qSign qKem signing index _ env kind)
  intro query current
  cases query with
  | inl query =>
    change Weighted (RegistrationNativePlatformPublicNativeLocal.bill qSign qKem kind)
      ((RegistrationNativePlatformPublicFrontend.trusted query).run current)
      (RegistrationNativeTrustedCosts.bill (n := n) (KemSK := KemSK) qKem kind query)
    simpa only [simulateQ_spec_query] using
      RegistrationNativePlatformPublicNativeLocal.trusted_program qSign qKem kind
        ((RegistrationNativeBeaconFrontend.Trusted n KemSK).query query : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) _)
        (RegistrationNativeTrustedCosts.bill (n := n) (KemSK := KemSK) qKem kind query)
        (RegistrationNativeWeightedContext.query_bound _ _) current
  | inr query => exact RegistrationNativePlatformPublicNativeLocal.platform_zero qSign qKem kind _ current

/-- Literal corrected frontend bundle, including exact byte readback, has its derived native/global weighted bill. -/
theorem bundle_bound {Platform : Type} (setup : Setup base KemSK) (qSign qKem : Nat)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform) (kind : EffectKind) :
    Weighted (RegistrationNativePlatformPublicWorldBills.nativeBill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.bundleBytes <$>
        RegistrationNativePlatformPublicFrontend.beacon
          (RegistrationNativePlatformPublicOwners.bundle RegistrationNativePlatformPublicFrontend.trusted
            (RegistrationNativePlatformPublicFrontend.writer implementation) setup source selected publicPrekey index))).run before)
      (bundleBill qSign kind) := by
  have bounded := RegistrationNativePlatformPublicNativeLocal.beacon_bound (n := n) (KemSK := KemSK) qSign qKem kind _ before _
    (owner_bound (n := n) (KemSK := KemSK) setup qSign qKem signing implementation selected publicPrekey index before.1.beacons before.1.environment before.2 kind)
  simpa only [RegistrationNativePlatformPublicFrontend.executeLocal, StateT.run_map, StateT.run,
    map_apply, simulateQ_map, Weighted, isQueryBound_map_iff] using bounded
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle.publication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle.publication_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle.owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle.owner_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle.bundle_bound
