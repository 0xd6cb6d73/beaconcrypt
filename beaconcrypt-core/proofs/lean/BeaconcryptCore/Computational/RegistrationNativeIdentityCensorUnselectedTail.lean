-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashOutgoingSource

/-! With identical pending source data, the hash/Ready/writer tail makes no omitted Ed signing call. Real and private-censored interpretation therefore agree on complete replies, Native/private/P states and every failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnselectedTail
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "action(" query ")" => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))
local notation "callback(" censored ")" => (fun query => source(censored, action(query)))
local notation "encoder(" censored ")" => (fun fields => source(censored, Main (RegistrationNativePlatformIdentityProgram.external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields))))

private theorem crypto_equal (query : RegistrationSigningShared.Spec.Domain) :
    callback(false) (.inl query) = callback(true) (.inl query) := by
  cases query with
  | hash request =>
    funext before
    exact RegistrationNativeIdentityCensorHashOutgoingSource.hash_same setup checks representation created selected placeholder request before
  | sign request payload digest =>
    funext before
    have same := congrArg (fun distribution => (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$> distribution)
      (RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_equal setup.joint selected placeholder _
        (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before.1.1) before.1.2 before.2)
    simpa only [interpret, StateT.run, RegistrationNativeIdentityCensorMldsaOutgoingSource.run, bind_pure_comp] using same

private theorem encoder_equal : encoder(false) = encoder(true) := by
  funext fields
  exact RegistrationNativeIdentityCensorExternalSource.source_equal setup.joint selected placeholder setup checks representation created _

theorem request_hash (pending : registration.BeaconInitHash) :
    RegistrationNativePlatformBeaconPublication.fromHash (callback(false)) (encoder(false)) pending =
      RegistrationNativePlatformBeaconPublication.fromHash (callback(true)) (encoder(true)) pending := by
  unfold RegistrationNativePlatformBeaconPublication.fromHash
  apply congrArg (RegistrationNativePlatformBeaconPublication.continueWith pending.request)
  funext request
  rw [crypto_equal setup checks representation created selected index owner placeholder (.hash request)]
  apply congrArg (Bind.bind (callback(true) (.inl (.hash request))))
  funext digest
  apply congrArg (RegistrationNativePlatformBeaconPublication.continueWith _)
  funext effect
  cases effect with
  | Ready next => rw [encoder_equal setup checks representation created selected placeholder reserve]
  | _ => rfl

/-- Before any target is selected, the actual PQ signing stage and its full original hash suffix have identical real/censored source behavior, including rejected keys and missing rows. -/
theorem pq (pending : registration.BeaconEd25519Signing) (stage : pending.stage = .PqKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (held : before.1.2.target = none) :
    (RegistrationNativePlatformBeaconPublication.fromEd (callback(false)) (encoder(false)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromEd (callback(true)) (encoder(true)) pending).run before := by
  obtain ⟨request, requested, role⟩ := RegistrationNativeIdentitySigningRole.request pending tagged
  have currentRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = false := by
    simpa only [RegistrationNativeIdentitySigningRole.slot, stage] using role
  have current := RegistrationNativeIdentityCensorEdUnselectedSource.outgoing setup checks representation created selected index owner request placeholder before held currentRole
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind]
  rw [current]
  apply bind_congr
  rintro ⟨reply, middle⟩
  obtain ⟨effect, resumed, facts⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_resume_refines pending reply
  rw [resumed]
  cases effect <;> simp only [BeaconcryptCore.Refinement.RegistrationSigning.EdReplyTransition, stage] at facts
  case Rejected previous => rfl
  case Ed25519SigningRequested next => exact facts.2.elim
  case HashRequested next =>
    exact congrArg (fun work => work.run middle) (request_hash setup checks representation created selected index owner placeholder reserve next)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnselectedTail
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnselectedTail.pq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnselectedTail.pq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnselectedTail.request_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnselectedTail.request_hash
