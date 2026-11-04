-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold

/-! The literal actual outgoing Ed callback is one indexed service followed by its exact native history append. Its full Main/P source tree has no hidden seed, hash or counter action. The prior-history observation masks the current appended signature while retaining its message and every other state field; the delivered current reply is kept separately for the source Core resume. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdOutgoing
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def updated (index : Nat) (message : Pqxdh.Bytes) (signature : Option Ed25519Signature)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :=
  match signature with
  | none => before
  | some signature =>
    let owners := RegistrationNativeIdentityHistoryView.update index
      (fun owner => {owner with edHistory := owner.edHistory ++ [PqxdhJointIdentity.Event.signed message signature]}) before.1.beacons
    ({before.1 with beacons := owners}, before.2)

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (change : S → S) (before : S) :
    (modify change : StateT S m Unit) before = pure ((), change before) := rfl
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

noncomputable def expected (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (request : registration.Ed25519SigningRequest) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    OracleComp Spec (RegistrationSigningShared.SignReply × (RegistrationNativeIdentityMain.State n KemSK source × Platform)) := by
  classical
  exact
      if request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519 then do
        let signature ← (Spec.query (.inl (.inl (.inr (.service owner.identity.handle
          (.sign (TranscriptAuthParts.absSlice request.message)))))) : OracleComp Spec (Option Ed25519Signature))
        pure (match signature with
          | none => .None
          | some signature => RegistrationAuthenticationShared.openedBytes
              (some (signature.toList ++ TranscriptAuthParts.absSlice request.message)),
          updated index (TranscriptAuthParts.absSlice request.message) signature before)
      else pure (.None, before)

/-- Full source normalization of the actual outgoing callback, including missing source rows and the original public-key gate. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (request : registration.Ed25519SigningRequest)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.native
        (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup source index owner (.inr request)))).run before =
      expected index owner request before := by
  classical
  unfold expected
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.run]
  simp only [RegistrationNativePlatformIdentityProgram.native, RegistrationNativeIdentityFrontend.outgoing, StateT.run,
    map_apply, simulateQ_map]
  split
  · simp only [bind_apply, lift_apply, map_apply, simulateQ_bind, map_bind, bind_map_left,
      RegistrationNativeIdentityInterface.sign, RegistrationNativePlatformIdentityProgram.nativeLift,
      RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
      RegistrationNativePlatformIdentityCtxCompiler.joint, simulateQ_spec_query, Functor.map_map]
    apply bind_congr
    intro signature
    cases signature with
    | none => simp only [Prod.map, id_eq, simulateQ_pure, pure_apply, map_pure, updated, RegistrationNativePlatformIdentityCtxOutgoingFold.close,
        RegistrationNativePlatformIdentityCtxEnvPatch.patch, RegistrationWorldAgreementCompiler.join_erase]
    | some signature =>
      simp only [Prod.map, id_eq, RegistrationNativeIdentityFrontend.logEd, bind_apply, modify_apply, pure_apply, pure_bind,
        simulateQ_pure, map_pure, updated, RegistrationNativeIdentityHistoryView.update, RegistrationNativePlatformIdentityCtxOutgoingFold.close,
        RegistrationNativePlatformIdentityCtxEnvPatch.patch, RegistrationWorldAgreementCompiler.join_erase]
      rfl
  · simp only [Prod.map, id_eq, simulateQ_pure, pure_apply, map_pure, RegistrationNativePlatformIdentityCtxOutgoingFold.close,
      RegistrationNativePlatformIdentityCtxEnvPatch.patch, RegistrationWorldAgreementCompiler.join_erase]

/-- The actual current canonical/placeholder append has the identical history Main observation, with both actual message positions retained. -/
theorem projected_append (placeholder left right : Ed25519Signature) (index : Nat) (message : Pqxdh.Bytes)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    RegistrationNativePlatformIdentityCtxHistoryView.view placeholder (updated index message (some left) before) =
      RegistrationNativePlatformIdentityCtxHistoryView.view placeholder (updated index message (some right) before) := by
  simp only [updated, RegistrationNativePlatformIdentityCtxHistoryView.view, RegistrationNativeIdentityHistoryView.append]

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdOutgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdOutgoing.projected_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdOutgoing.projected_append
