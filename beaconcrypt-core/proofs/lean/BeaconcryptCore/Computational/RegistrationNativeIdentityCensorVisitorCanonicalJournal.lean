-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorJournal
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

/-! The actual closed canonical source visitor is the exact public journal fold of that same complete source execution. Every original suffix callback remains on the complete-run side; distribution transport uses only genuine losslessness. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorCanonicalJournal
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
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "canonical" => RegistrationNativeIdentityCensorCanonicalSource.handler setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder
omit primitive in
def getTarget (before : FullState) : Option Pqxdh.Bytes := before.1.2.target
local notation "target" => getTarget (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "published" => RegistrationNativeIdentityCensorAdaptivePostselection.published (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "actualVisit" => RegistrationNativeIdentityCensorAdaptivePostselection.visit setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder false

/-- The generic public stopping traversal is literally the current canonical source visitor, through every failed accept and failed publication. -/
theorem visit_eq (accept : Nat) (work : OracleComp TypedSpec A) (before : FullState) (cursor : Nat) :
    RegistrationNativeIdentityCensorVisitorJournal.visit canonical target published accept work before cursor =
      actualVisit accept work (before,cursor) := by
  induction work using OracleComp.inductionOn generalizing before cursor with
  | pure value => rfl
  | query_bind query next ih =>
      change (match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor with
        | some packet => pure ((target before).map (fun message => (message,packet)))
        | none => do
            let reached ← (canonical query).run before
            if published query reached.1 reached.2 then pure none else
              RegistrationNativeIdentityCensorVisitorJournal.visit canonical target published accept (next reached.1) reached.2
                (cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)) =
        (match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor with
        | some packet => pure ((target before).map (fun message => (message,packet)))
        | none => do
            let selectedCut ← RegistrationNativeIdentityCensorAdaptivePostselection.cut query <$> (canonical query).run before
            match selectedCut with
            | none => pure none
            | some kept => (actualVisit accept (next kept.1)
                (kept.2,cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)))
      cases chosen : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor with
      | some packet => rfl
      | none =>
          simp only [bind_map_left]
          apply bind_congr
          intro reached
          unfold RegistrationNativeIdentityCensorAdaptivePostselection.cut
          cases stopped : published query reached.1 reached.2 with
          | true => simp only [ite_true]
          | false =>
              simpa only [stopped,Bool.false_eq_true,ite_false] using
                (ih reached.1 reached.2 (cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0))

/-- Folding the full ORIGINAL canonical callback journal has exactly the literal before-a visitor distribution; no original later source query is removed from the full-run game. -/
theorem source (accept : Nat) (work : OracleComp TypedSpec A) (before : FullState) (cursor : Nat) :
    (fun result => RegistrationNativeIdentityCensorVisitorJournal.fold target published accept cursor result.2.2) <$>
      RegistrationNativeIdentityCensorVisitorJournal.full canonical work before =ᵈ actualVisit accept work (before,cursor) := by
  rw [←visit_eq setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    selected position placeholder accept work before cursor]
  exact RegistrationNativeIdentityCensorVisitorJournal.source canonical target published accept work before cursor

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorCanonicalJournal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorCanonicalJournal.visit_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorCanonicalJournal.visit_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorCanonicalJournal.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorCanonicalJournal.source
