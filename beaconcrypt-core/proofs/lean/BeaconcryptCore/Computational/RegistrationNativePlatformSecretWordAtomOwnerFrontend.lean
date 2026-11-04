-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerCount
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution
/-! The complete actual mixed-roster corrected finish retains its original current environment, private provider, chronology and public platform state. Its atom attempts use the derived current handle alignment and spend exactly the selected owner’s native terminal credit; no source controller or handle equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordService (Combined)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

open RegistrationNativePlatformSecretWordExecution (TracedState drop)
open RegistrationNativeSecretWordOwnerCredit (cost)
open RegistrationNativeSecretWordAtomInstallTrace (count)


variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (route : RawCtxServerRouting.SenderDecoder) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) (publicKey : PqxdhKemIndCca.MlKem768PublicKey)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selectedOwner pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "untraced" => RegistrationNativePlatformSecretWordExecution.typed setup wire route sign input inside provider outer controller
abbrev Front (source : RegistrationNativeMldsa.Source) (Platform : Type) := RegistrationNativePlatformSecretWordOrdinary.State source Platform

local notation "typed" => RegistrationNativePlatformSecretWordExecution.traced setup wire route sign input inside provider outer controller

open RegistrationNativeSecretWordAtomOwnerSource (State)
attribute [local irreducible] RegistrationNativePlatformSecretWordFinish.finish

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _

private theorem finish_present (before : TracedState (Front source Platform) n KemSK) (index : Nat)
    (packet : Option registration.ResponsePacket) (owner : RegistrationNativePublicOwners.Owner source)
    (found : before.1.1.beacons[index]? = some owner) :
    (typed (.inr (.finish index packet))).run before =
      (fun result => (result.1.1,
        (({ before.1.1 with beacons := before.1.1.beacons.set index { owner with view := result.1.2 }, environment := result.2.1 }, before.1.2),
          (result.2.2.1, result.2.2.2)))) <$>
        (RegistrationNativeSecretWordAtomOwnerSource.lower setup wire route sign input inside provider outer owner.scalar
          ((RegistrationNativePlatformSecretWordFinish.finish setup wire source packet).run owner.view)).run
            (before.1.1.environment, (before.2.1, before.2.2)) := by
  rw [RegistrationNativePlatformSecretWordExecution.traced, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.finish,
    StateT.run, found, simulateQ_map, map_apply, Functor.map_map,
    RegistrationNativeSecretWordAtomOwnerSource.lower, RegistrationNativeSecretWordAtomOwnerSource.routing]
  cases owner.scalar with
  | none => rfl
  | some scalar =>
    simp only [QueryImpl.simulateQ_compose]
    rfl

/-- The actual complete mixed-roster callback pays for every Beacon atom attempt from its selected retained owner's terminal credit. -/
theorem finish_count (before : TracedState (Front source Platform) n KemSK) (index : Nat)
    (packet : Option registration.ResponsePacket)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned before.1.1.beacons before.2.2.kem.1.keys)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range (.inr (.finish index packet)) × TracedState (Front source Platform) n KemSK)
    (supported : result ∈ support ((typed (.inr (.finish index packet))).run before)) :
    count .beacon result.2.2.1 ≤ count .beacon before.2.1 + cost selectedOwner (.inr (.finish index packet)) before.1.1 := by
  cases found : before.1.1.beacons[index]? with
  | none =>
    rw [RegistrationNativePlatformSecretWordExecution.traced, QueryImpl.flattenStateT_mapStateTBase_apply_run] at supported
    simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.finish,
      StateT.run, found, simulateQ_pure] at supported
    cases supported
    dsimp only
    omega
  | some owner =>
    rw [finish_present setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer route input inside pairs publicKey challenge outer before index packet owner found, support_map] at supported
    obtain ⟨reached, called, equal⟩ := supported
    cases equal
    exact RegistrationNativePlatformSecretWordAtomOwnerCount.local_finish setup wire route sign input inside selectedOwner pairs publicKey challenge outer
      before.1.1 index owner packet (before.1.1.environment, (before.2.1, before.2.2)) reached aligned found called

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerFrontend.finish_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerFrontend.finish_count
