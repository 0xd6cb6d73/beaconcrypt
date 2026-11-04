-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeFrontendBills
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeOrdinary
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeCaps
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicFrontend
open RegistrationNativePlatformPublicWorldBills (nativeBill)
open PqxdhRecordLiftInterface (EffectKind effectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePublicationCosts (hashCost)
variable {n : Nat} {E Platform I KemSK A : Type} {base : OracleSpec I}
def cost (qGenerate qSign qKem : Nat) (kind : EffectKind) (tag : Fin 12) : Nat :=
  match tag.val with
  | 0 => coinCost 1 kind
  | 1 => RegistrationNativeCreateCosts.createBill qGenerate qKem kind
  | 2 => RegistrationNativeBundleCosts.bundleBill qSign kind
  | 3 => RegistrationNativePlatformPublicNativeAccept.acceptBill qKem kind
  | 4 => RegistrationNativePlatformNativeFrontendBills.buildCost qSign kind
  | 5 => RegistrationNativePlatformBeaconMaterialBills.finishBill qKem kind
  | 7 => hashCost kind
  | _ => 0
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
private theorem map_iff {J X Y : Type} {spec : OracleSpec J}
    (cost : J → Nat) (work : OracleComp spec X) (change : X → Y) (cap : Nat) :
    Weighted cost (change <$> work) cap ↔ Weighted cost work cap :=
  isQueryBound_map_iff work change cap _ _
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (erased : commitment.CommitmentTranscript) (qGenerate qSign qKem : Nat)
variable (generation : source.generate.IsTotalQueryBound qGenerate)
variable (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
variable (signed : ∀ request, (sign request).IsTotalQueryBound qSign)
local notation "callback" => handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
include generation signing signed in
/-- Every literal corrected public callback has a derived native/global weighted bill from source controllers and primitive sampler caps, with all P histories retained. -/
theorem handler_bound (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source Platform) (kind : EffectKind) :
    Weighted (nativeBill (n := n) (KemSK := KemSK) qSign qKem kind) ((callback query).run before)
      (cost qGenerate qSign qKem kind (RegistrationNativeRawAdapter.kind query)) := by
  unfold handler
  cases query with
  | inl coin =>
    have bounded := RegistrationNativePlatformPublicNativeLocal.embed_bound qSign qKem kind _ _
      (RegistrationNativePlatformPublicNativeOrdinary.effect_bound (n := n) (KemSK := KemSK) qSign qKem kind (.inl coin) before)
    cases kind <;> simpa [effectKind, coinCost, cost, RegistrationNativeRawAdapter.kind, executeLocal, StateT.run, lift_apply, simulateQ_map] using bounded
  | inr query => cases query with
    | create edPin mlPin keyId =>
      exact RegistrationNativePlatformPublicNativeCreate.create_bound setup source selectedOwner publicPrekey
        qGenerate qSign qKem generation edPin mlPin keyId before kind
    | bundle index => exact RegistrationNativePlatformPublicNativeBundle.bundle_bound setup qSign qKem signing writer selectedOwner publicPrekey index before kind
    | accept packet =>
      change Weighted _ (simulateQ embedLocal (_ : OracleComp (LocalSpec n KemSK) _)) _
      apply RegistrationNativePlatformPublicNativeLocal.embed_bound qSign qKem kind
      simp only [StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
      simp only [serverOpen, StateT.run, map_iff]
      exact RegistrationNativePlatformPublicNativeAccept.accept_bound (n := n) (KemSK := KemSK)
        (decide (before.1.parsedAccepts = selectedAccept)) reserveRegistration setup checks source.verify packet
        before.1.server before.1.environment before.2 qSign qKem kind
    | build handle application =>
      change Weighted _ (simulateQ embedLocal (_ : OracleComp (LocalSpec n KemSK) _)) _
      apply RegistrationNativePlatformPublicNativeLocal.embed_bound qSign qKem kind
      exact RegistrationNativePlatformNativeFrontendBills.build_bound view failure allocation helper writer sign qSign signed erased
        setup qKem kind reservePeer handle application source before
    | finish index packet => exact RegistrationNativePlatformPublicNativeFinish.finish_bound setup wire source packet index before qSign qKem kind
    | hmac key bytes => trivial
    | hash bytes =>
      have bounded := RegistrationNativePlatformPublicNativeLocal.embed_bound qSign qKem kind _ _
        (RegistrationNativePlatformPublicNativeOrdinary.effect_bound (n := n) (KemSK := KemSK) qSign qKem kind (.inr (.hash bytes)) before)
      cases kind <;> simpa [effectKind, hashCost, cost, RegistrationNativeRawAdapter.kind, executeLocal, StateT.run, lift_apply, simulateQ_map] using bounded
    | serverSend keyId plaintext => exact RegistrationNativePlatformPublicNativeOrdinary.record_bound qSign qKem kind reserveFrame (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact RegistrationNativePlatformPublicNativeOrdinary.record_bound qSign qKem kind reserveFrame (.inl (.inr raw)) before
    | beaconSend index plaintext => exact RegistrationNativePlatformPublicNativeOrdinary.record_bound qSign qKem kind reserveFrame (.inr (index, .inl plaintext)) before
    | beaconRaw index raw => exact RegistrationNativePlatformPublicNativeOrdinary.record_bound qSign qKem kind reserveFrame (.inr (index, .inr raw)) before
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeCaps.handler_bound
