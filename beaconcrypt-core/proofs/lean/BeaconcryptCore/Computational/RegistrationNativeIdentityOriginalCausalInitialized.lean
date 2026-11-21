-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalCover
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProfile
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedConditional
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! The literal original initialized native final-owner causal event is split on its same complete journal. The Unissued component is charged to the explicit ordinary reduction family; the actual issued component remains named for its separate causal stopping bound. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalInitialized
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






open RegistrationNativeIdentityUnissuedOriginalCore (Original)
local notation "actual" => RegistrationNativeIdentityUnissuedOriginalInitialized.game (n := n) setup checks wire route representation view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
attribute [local irreducible] RegistrationNativeIdentityUnissuedOriginalInitialized.game RegistrationNativeIdentityUnissuedInitialized.loss

def Historical (result : Option (Original n KemSK Platform Value source)) : Prop :=
  result.elim False (RegistrationNativeIdentityOriginalCausalCover.Historical setup wire source)

def Issued (budget : PqxdhDeploymentInterface.Budget) (result : Option (Original n KemSK Platform Value source)) : Prop :=
  result.elim False (RegistrationNativeIdentityOriginalCausalCover.Issued setup wire source budget)

noncomputable def event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool := fun result => by
  classical
  exact decide (RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.Historical setup.source.crypto canonical
    (result.2.2.beacons.map (fun owner => (setup.joint.publicKeys owner.identitySeed).ed25519)) result.2.1.transcript)

/-- Original whole-prefix budget and ordinary signature parsing derive both causal branches on every actual initialized same-run source outcome. -/
theorem source_split (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64 → setup.source.crypto.verify publicKey.toList bytes=none) :
    Pr{let result ← actual}[Historical setup wire source result] ≤
      Pr{let result ← actual}[RegistrationNativeIdentityUnissuedOriginalInitialized.Unissued setup wire source budget result] +
      Pr{let result ← actual}[Issued setup wire source budget result] := by
  have cover : Pr{let result ← actual}[Historical setup wire source result] ≤
      Pr{let result ← actual}[RegistrationNativeIdentityUnissuedOriginalInitialized.Unissued setup wire source budget result ∨ Issued setup wire source budget result] := by
    apply prEvent_mono_of_support
    intro result supported failed
    simp only [RegistrationNativeIdentityUnissuedOriginalInitialized.game,mem_support_bind_iff] at supported
    obtain ⟨initialized,_startup,called⟩ := supported
    cases initialized with
    | none =>
        simp only [mem_support_pure_iff] at called
        subst result
        cases failed
    | some initial =>
        rw [support_map] at called
        obtain ⟨finished,reached,rfl⟩ := called
        exact RegistrationNativeIdentityOriginalCausalCover.cover setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source bounds mode adversary previous initial budget (bounded initial.public) shortRejects finished reached failed
  exact cover.trans (prEvent_or_le _ _ _)

/-- The original initialized final-owner causal observation has exactly the complete actual native profile probability. -/
theorem profile_source :
    Pr{let result ← ((RegistrationNativePlatformOrdinaryExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (event (n := n) setup wire source)).run previous)}[result.1=true] =
    Pr{let result ← actual}[Historical setup wire source result] := by
  classical
  have law := congrArg (fun distribution => Pr{let result ← distribution}[result.1=true])
    (RegistrationNativeIdentityUnissuedOriginalProfile.profile_source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous (event (n := n) setup wire source))
  rw [prEvent_map] at law
  refine law.symm.trans ?_
  apply prEvent_congr
  intro result
  cases result with
  | none => simp only [RegistrationNativeIdentityUnissuedOriginalProfile.observe,Historical,Option.elim_none,Bool.false_eq_true]
  | some result => simp only [RegistrationNativeIdentityUnissuedOriginalProfile.observe,Historical,Option.elim_some,
      event,decide_eq_true_eq,RegistrationNativeIdentityOriginalCausalCover.Historical,RegistrationNativePlatformOrdinaryCausalReservedCover.identities]

/-- The literal initialized native causal event pays its ordinary unissued-field loss plus the unchanged original same-run issued-event mass. -/
theorem unissued_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64 → setup.source.crypto.verify publicKey.toList bytes=none)
    (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← ((RegistrationNativePlatformOrdinaryExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (event (n := n) setup wire source)).run previous)}[result.1=true] ≤
    RegistrationNativeIdentityUnissuedInitialized.loss (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget fallback +
      Pr{let result ← actual}[Issued setup wire source budget result] := by
  rw [profile_source]
  exact (source_split setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded shortRejects).trans
      (add_le_add (RegistrationNativeIdentityUnissuedOriginalInitialized.bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded fallback) le_rfl)

end BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalInitialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalInitialized.source_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalInitialized.source_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalInitialized.profile_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalInitialized.profile_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalInitialized.unissued_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalInitialized.unissued_bound
