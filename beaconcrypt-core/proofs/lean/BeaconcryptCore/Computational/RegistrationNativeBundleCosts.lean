-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCreateCosts
import BeaconcryptCore.Computational.RegistrationNativeInitCosts

/-! The actual outgoing bundle retains its one-time scalar draw, original six-callback Init controller, complete signing history and final owner-phase capability. The conservative callback multiplicity charges every source slot with its maximum hash/sign bill; failed source operations keep their original prefix costs. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeBundleCosts
open PqxdhRecordLiftInterface (EffectKind effectKind)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePublicationCosts (hashCost)
open RegistrationNativeCreateCosts (administrativeCost)
open RegistrationNativeTrustedCosts (bill sample_bound effect_bound)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_mono weighted_indicator)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

def outgoingCost (qSign : Nat) (kind : EffectKind) := hashCost kind + coinCost qSign kind

def bundleBill (qSign : Nat) (kind : EffectKind) := coinCost 32 kind + (outgoingCost qSign kind * 6 + administrativeCost kind)

/-- Each actual Init callback retains its source hash/signing draws and mutable chronological receipts. -/
theorem outgoing_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (qSign qKem : Nat) (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (query : RegistrationBeaconInitExecutor.Spec.Domain)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (kind : EffectKind) :
    Weighted (bill (n := n) qKem kind)
      (((RegistrationNativeBeaconFrontend.outgoing setup source index owner query).run owners).run env)
      (outgoingCost qSign kind) := by
  classical
  cases query with
  | inl query =>
      cases query with
      | hash request =>
          apply weighted_mono _ _ (hashCost kind) _ ?_ (Nat.le_add_right _ _)
          unfold RegistrationNativeBeaconFrontend.outgoing RegistrationNativeBeaconFrontend.hash
          cases kind <;> exact effect_bound source qKem _ (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))) owners env
      | sign request payload digest =>
          simp only [RegistrationNativeBeaconFrontend.outgoing, StateT.run_bind]
          apply weighted_mono _ _ (coinCost qSign kind + 0) _ ?_ (by unfold outgoingCost; omega)
          apply weighted_bind _ _ _ _ _ (sample_bound source qKem kind _ qSign
            (RegistrationNativePrimitiveCosts.signing_bound source qSign signing owner.mldsa request) owners env)
          intro reply
          simp only [RegistrationNativeBeaconFrontend.updateEnv, StateT.run_lift, StateT.run_bind,
            StateT.run_modify, StateT.run_pure, pure_bind]
          trivial
  | inr request =>
      simp only [RegistrationNativeBeaconFrontend.outgoing]
      split
      · simp only [RegistrationNativeBeaconFrontend.logEd, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        trivial
      · trivial

/-- The actual six-slot executor is interpreted on both original state coordinates. -/
theorem program_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (qSign qKem : Nat) (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (kind : EffectKind) :
    Weighted (bill (n := n) qKem kind)
      (((simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)).run owners).run env)
      (outgoingCost qSign kind * 6) := by
  apply RegistrationNativeWeightedContext.run_bound (fun _ => outgoingCost qSign kind) _ _ _ _ owners env
  · simpa only [ite_true] using weighted_indicator (fun _ => True) (outgoingCost qSign kind) _ 6
      ((isQueryBoundP_true_iff _ _).mpr (RegistrationNativeInitCosts.begin_bound _ _ _ _ _ _))
  · intro query current environment
    exact outgoing_bound setup source qSign qKem signing index owner query current environment kind

private noncomputable def suffix (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let published ← simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
      RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime)
      let _ ← RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))
      pure (.ok (some finished.encoded))

private theorem suffix_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (qSign qKem : Nat) (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (kind : EffectKind) :
    Weighted (bill (n := n) qKem kind) (((suffix setup source wire index owner oneTime).run owners).run env)
      (outgoingCost qSign kind * 6 + administrativeCost kind) := by
  simp only [suffix, StateT.run_bind]
  apply weighted_bind _ _ _ _ _ (program_bound setup source qSign qKem signing wire index owner oneTime owners env kind)
  intro published
  rcases published with ⟨⟨published, after⟩, afterEnvironment⟩
  cases published with
  | fail error => trivial
  | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok finished =>
        simp only [StateT.run_bind, RegistrationNativeBeaconFrontend.updatePhase,
          StateT.run_modify, pure_bind]
        rw [← Nat.add_zero (administrativeCost kind)]
        apply weighted_bind _ _ _ _ _ (by
          cases kind <;> exact effect_bound source qKem _ (.inr (.advanceOwner owner.worldOwner .initSent)) _ _)
        intro _
        trivial

/-- Native bundle creation includes one possible one-time scalar, every original signing callback and the final phase capability. -/
theorem bundle_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (qSign qKem : Nat) (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (kind : EffectKind) :
    Weighted (bill (n := n) qKem kind) (((RegistrationNativeBeaconFrontend.bundle setup source wire index).run owners).run env)
      (bundleBill qSign kind) := by
  simp only [RegistrationNativeBeaconFrontend.bundle, StateT.run_bind, StateT.run_get, pure_bind]
  cases found : owners[index]? with
  | none => simp only [StateT.run_pure]; trivial
  | some owner =>
      simp only []
      cases phase : owner.phase with
      | initSent pending oneTime | established completed | aborted aborted =>
          all_goals simp only [StateT.run_pure]; trivial
      | fresh =>
          simp only [StateT.run_bind]
          change Weighted (bill qKem kind) (do
            let sampled ← ((RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar).run owners).run env
            ((suffix setup source wire index owner sampled.1.1).run sampled.1.2).run sampled.2) (bundleBill qSign kind)
          apply weighted_bind _ _ _ _ _ (sample_bound source qKem kind _ 32 PqxdhJointGapDh.sampleScalar_uniform owners env)
          intro sampled
          exact suffix_bound setup source qSign qKem signing wire index owner sampled.1.1 sampled.1.2 sampled.2 kind
      | freshWithCoins oneTime =>
          simp only []
          exact weighted_mono _ _ _ _ (suffix_bound setup source qSign qKem signing wire index owner oneTime owners env kind) (by unfold bundleBill; omega)

/-- The actual public-reference bundle callback retains the same source cost after owner/address projection. -/
theorem frontend_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (qSign qKem : Nat) (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (index : Nat) (before : RegistrationNativePublicFrontend.State source) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeRestrictedCosts.bill qSign qKem query kind)
      ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.bundle index))).run before) (bundleBill qSign kind) := by
  have actual := RegistrationNativeTrustedCosts.embedded_program qSign qKem kind _ _
    (bundle_bound (n := n) setup source qSign qKem signing wire index
      (before.beacons.map RegistrationNativePublicOwners.restore) before.environment kind)
  simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon,
    RegistrationNativePublicOwners.bundle, RegistrationNativePublicOwners.executeLocal, StateT.run,
    simulateQ_map, Weighted, isQueryBound_map_iff] using actual

end BeaconcryptCore.Computational.RegistrationNativeBundleCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleCosts.outgoing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleCosts.outgoing_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleCosts.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleCosts.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleCosts.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleCosts.bundle_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleCosts.frontend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleCosts.frontend_bound
