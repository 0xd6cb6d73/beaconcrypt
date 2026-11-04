-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdUnselectedSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicHashSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame

/-! Before selection, inactive routing preserves the original public fingerprint and Init hash source. The actual role-separated PQ request retains inactivity into the complete native ML/writer continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorInactiveTail
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorRealSigning (NoHash)
variable {n : Nat} {I KemSK Platform E A B : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] registration.BeaconFingerprint.resume registration.BeaconInitHash.resume registration.BeaconMldsaSigning.resume

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
variable (writer : registration.SignedInitView → StateT Platform ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "callback" => (fun query => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query)))
local notation "encoder" => (fun fields => Main (RegistrationNativePlatformIdentityProgram.external (writer fields)))

private def hashNext {m : Type → Type} [Monad m]
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (encode : registration.SignedInitView → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (pending : registration.BeaconInitHash) (request : registration.HashRequest) (digest : CtxRomAuth.CtxDigest) :
    m (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformBeaconPublication.continueWith
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .MldsaSigningRequested next => RegistrationNativePlatformBeaconPublication.fromSigning impl encode
          ⟨.beacon, BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request⟩ digest next
      | _ => pure .div

/-- Inactive Init hashing and the complete ML/writer suffix have the same original source marginal. -/
theorem hash (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconInitHash) (request : registration.HashRequest) (requested : pending.request = .ok request)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (inactive : before.1.2.active = false) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (RegistrationNativePlatformBeaconPublication.fromHash
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromHash
        (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  obtain ⟨actualRequest, actualRequested, _bytes, _routed⟩ := RegistrationNativeIdentityHashRoute.transcript pending
  have same : actualRequest = request := RustM.ok.inj (actualRequested.symm.trans requested)
  subst actualRequest
  simp only [RegistrationNativePlatformBeaconPublication.fromHash, requested, RegistrationNativePlatformBeaconPublication.continueWith]
  simp only [StateT.run_bind, map_bind]
  have current := RegistrationNativeIdentityCensorActualHashSource.inactive setup checks representation created selected placeholder request before inactive
  change Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
    (interpret setup.joint selected placeholder false (callback (.inl (.hash request)))).run before =
    (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback (.inl (.hash request)))).run
      (RegistrationNativeIdentityCensorActualHashSource.project before) at current
  rw [← current, bind_map_left]
  apply bind_congr
  rintro ⟨digest, after⟩
  change Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
    (hashNext (fun query => interpret setup.joint selected placeholder false (callback query))
      (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending request digest).run after =
    (hashNext (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
      (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending request digest).run
        (RegistrationNativeIdentityCensorActualHashSource.project after)
  unfold hashNext
  cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
  | fail error | div =>
    simp only [RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | ok effect => cases effect with
    | MldsaSigningRequested next =>
      exact RegistrationNativeIdentityCensorRealTail.signing setup checks representation created index owner writer selected placeholder
        ⟨.beacon, BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request⟩ digest next after
    | _ =>
      simp only [RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_pure, map_pure, Prod.map_apply, id_eq]

private def fingerprintNext {m : Type → Type} [Monad m]
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (encode : registration.SignedInitView → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (pending : registration.BeaconFingerprint) (digest : CtxRomAuth.CtxDigest) :
    m (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformBeaconPublication.continueWith
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .HashRequested next => RegistrationNativePlatformBeaconPublication.fromHash impl encode next
      | _ => pure .div

/-- The actual public fingerprint preserves inactivity into every successful Init hash continuation. -/
theorem fingerprint (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconFingerprint)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (inactive : before.1.2.active = false) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (RegistrationNativePlatformBeaconPublication.fromFingerprint
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromFingerprint
        (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  obtain ⟨request, requested, bytes, _routed⟩ := RegistrationNativeIdentityHashRoute.fingerprint pending
  have width : (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request).length = 1952 := by
    rw [bytes, PqxdhRefinement.absBytes_length]
    rfl
  simp only [RegistrationNativePlatformBeaconPublication.fromFingerprint, requested, RegistrationNativePlatformBeaconPublication.continueWith,
    StateT.run_bind, map_bind]
  have current := RegistrationNativeIdentityCensorPublicHashSource.fingerprint setup checks representation created selected placeholder request before width
  change Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
    (interpret setup.joint selected placeholder false (callback (.inl (.hash request)))).run before =
    (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback (.inl (.hash request)))).run
      (RegistrationNativeIdentityCensorActualHashSource.project before) at current
  rw [← current, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨digest, after⟩ reached
  have frame := RegistrationNativeIdentityCensorHashFrame.outgoing setup checks representation created selected placeholder request false before (digest, after) reached
  have stillInactive : after.1.2.active = false := (congrArg (fun value => value.1.active) frame).trans inactive
  change Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
    (fingerprintNext (fun query => interpret setup.joint selected placeholder false (callback query))
      (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending digest).run after =
    (fingerprintNext (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
      (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending digest).run
        (RegistrationNativeIdentityCensorActualHashSource.project after)
  unfold fingerprintNext
  cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
  | fail error | div =>
    simp only [RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | ok effect => cases effect with
    | HashRequested next =>
      obtain ⟨nextRequest, nextRequested, _bytes, _route⟩ := RegistrationNativeIdentityHashRoute.transcript next
      exact hash setup checks representation created index owner writer selected placeholder next nextRequest nextRequested after stillInactive
    | _ =>
      simp only [RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_pure, map_pure, Prod.map_apply, id_eq]

/-- Before selection, the actual PQ signing request forwards its optional reply and retains the complete original fingerprint/hash/writer marginal. -/
theorem pq (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconEd25519Signing) (stage : pending.stage = .PqKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (held : before.1.2.target = none) (inactive : before.1.2.active = false) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (RegistrationNativePlatformBeaconPublication.fromEd
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromEd
        (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  obtain ⟨request, requested, role⟩ := RegistrationNativeIdentitySigningRole.request pending tagged
  have currentRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = false := by
    simpa only [RegistrationNativeIdentitySigningRole.slot, stage] using role
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, map_bind]
  have current := RegistrationNativeIdentityCensorRealSigning.outgoing setup checks representation created selected index owner request placeholder before
  dsimp only at current
  rw [← current, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨reply, after⟩ reached
  have frame := RegistrationNativeIdentityCensorEdUnselectedSource.frame setup checks representation created selected index owner request placeholder false before held currentRole (reply, after) reached
  have stillInactive : after.1.2.active = false := (congrArg (fun value => value.1.active) frame).trans inactive
  obtain ⟨effect, resumed, facts⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_resume_refines pending reply
  simp only [Prod.map, id_eq]
  rw [resumed]
  cases effect <;> simp only [BeaconcryptCore.Refinement.RegistrationSigning.EdReplyTransition, stage] at facts
  case Rejected previous => simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  case Ed25519SigningRequested next => exact facts.2.elim
  case FingerprintRequested next =>
    exact fingerprint setup checks representation created index owner writer selected placeholder next after stillInactive

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorInactiveTail

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorInactiveTail.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorInactiveTail.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorInactiveTail.fingerprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorInactiveTail.fingerprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorInactiveTail.pq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorInactiveTail.pq
