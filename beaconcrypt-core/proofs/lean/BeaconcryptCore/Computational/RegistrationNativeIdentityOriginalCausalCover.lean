-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalProfile
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProfile
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedConditional
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! The original initialized final-owner causal event has its same complete chronological unissued-or-issued cover. Canonical fallback frame encoding is removed only by a derived literal source dictionary law; every dynamic writer and allocation outcome remains unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalCover
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
variable {Value : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (CoreModels.core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (previous : Platform)





open RegistrationNativeIdentityUnissuedOriginalCore (Original original)
open RegistrationNativePlatformIdentityCtxKeyJournal (drop)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire

def Historical (result : Original n KemSK Platform Value source) : Prop :=
  RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.Historical setup.source.crypto canonical
    (RegistrationNativePlatformOrdinaryCausalReservedCover.identities setup.joint (drop result.2.2.1)) result.2.1.transcript

def Issued (budget : PqxdhDeploymentInterface.Budget) (result : Original n KemSK Platform Value source) : Prop :=
  ∃ attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint canonical budget result.2.2.2 result.2.2.1,
    Nonempty (RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)

/-- Replacing only the mathematical fallback frame encoder leaves the complete literal original journal unchanged, by the derived actual source dictionary equality. -/
theorem canonical_run (initial : RegistrationNativeExperiment.Initial n KemSK source) :
    original setup checks canonical route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial =
    original setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial := by
  unfold original
  rw [RegistrationNativePlatformIdentityCtxCanonicalWire.handler setup wire reserveFrame checks route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer erased helper writer]
  rfl

/-- Original Respects and ordinary attached-signature parsing derive the exact same-result causal branch cover, including final owner aliases created after acceptance. -/
theorem cover (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget (adversary initial.public))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64 → setup.source.crypto.verify publicKey.toList bytes=none)
    (result : Original n KemSK Platform Value source)
    (supported : result ∈ support (original setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial)) (failed : Historical setup wire source result) :
    RegistrationNativeIdentityUnissuedOriginalMarginal.Unissued setup wire source budget result ∨ Issued setup wire source budget result := by
  have actual : result ∈ support (original setup checks canonical route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial) := by
    rw [canonical_run]
    exact supported
  obtain ⟨attempt,branch⟩ := RegistrationNativePlatformIdentityCtxFiniteCover.causal_cover setup checks canonical route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer shortRejects initial.created.server.server.metadata.sender bounds mode (adversary initial.public) budget bounded
    (RegistrationNativeIdentityMainProfile.fromInitial initial,previous) rfl
    (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]) result actual failed
  rcases branch with unissued | issued
  · exact Or.inl ⟨attempt,unissued⟩
  · exact Or.inr ⟨attempt,issued⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalCover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalCover.canonical_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalCover.canonical_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalCover.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalCover.cover
