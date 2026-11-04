-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds
import BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts

/-! Literal ML signing-slot bounds for the original publication controllers. The bound counts the complete attempted request before any optional reply or publication failure, and uses no primitive success or security assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaSignSyntax

namespace Beacon
open RegistrationBeaconInitExecutor
variable {Encoded Input : Type}

def IsSign : Spec.Domain → Prop
  | .inl (.sign _ _ _) => True
  | _ => False
instance : DecidablePred IsSign := fun query => by
  rcases query with shared | ed
  · cases shared <;> first | exact instDecidableFalse | exact instDecidableTrue
  · exact instDecidableFalse

attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume

private theorem continue_bound (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded))) (count : Nat)
    (bounded : ∀ value, (next value).IsQueryBoundP IsSign count) :
    (continueWith action next).IsQueryBoundP IsSign count := by
  cases action with
  | ok value => exact bounded value
  | fail error => trivial
  | div => trivial

private theorem ready_bound (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitReady) : (ready encode pending).IsQueryBoundP IsSign 0 := by
  unfold ready
  exact continue_bound _ _ _ (fun _ => by trivial)

private theorem signing_bound (encode : registration.SignedInitView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    (fromSigning encode payload digest pending).IsQueryBoundP IsSign 1 := by
  unfold fromSigning
  apply continue_bound
  intro request
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by decide), fun signature => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | Ready selected => exact ready_bound encode selected
  | _ => trivial

private theorem hash_bound (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) : (fromHash encode pending).IsQueryBoundP IsSign 1 := by
  unfold fromHash
  apply continue_bound
  intro request
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (fun impossible => impossible.elim), fun digest => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing_bound encode _ _ selected
  | _ => trivial

private theorem fingerprint_bound (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) : (fromFingerprint encode pending).IsQueryBoundP IsSign 1 := by
  unfold fromFingerprint
  apply continue_bound
  intro request
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (fun impossible => impossible.elim), fun digest => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | HashRequested selected => exact hash_bound encode selected
  | _ => trivial

/-- Every original attached-signing loop path reaches at most one ML signing request. -/
theorem ed (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) : (fromEd encode pending).IsQueryBoundP IsSign 1 := by
  rw [fromEd.eq_def]
  apply continue_bound
  intro request
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (fun impossible => impossible.elim), fun reply => ?_⟩
  cases actual : pending.resume reply with
  | fail error => trivial
  | div => trivial
  | ok effect =>
      cases effect with
      | Ed25519SigningRequested next => exact ed encode next
      | FingerprintRequested selected => exact fingerprint_bound encode selected
      | _ => trivial
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

attribute [local irreducible] registration.begin_beacon_init

/-- The native Init controller attempts at most one ML signature, including failed replies and encoders. -/
theorem begin_bound (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    (begin encode control inputs coins pin mldsa).IsQueryBoundP IsSign 1 := by
  unfold begin
  apply continue_bound
  intro effect
  cases effect with
  | Ed25519SigningRequested pending => exact ed encode pending
  | _ => trivial
end Beacon

namespace Server
open RegistrationWorldServerPublication
open RegistrationSigningShared (Spec)
variable {Encoded Input : Type}

def IsSign : Spec.Domain → Prop
  | .sign _ _ _ => True
  | _ => False
instance : DecidablePred IsSign := fun query => by
  cases query <;> first | exact instDecidableFalse | exact instDecidableTrue

attribute [local irreducible] registration.ServerResponseHash.resume registration.ServerResponseSigning.resume

private theorem continue_bound (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded))) (count : Nat)
    (bounded : ∀ value, (next value).IsQueryBoundP IsSign count) :
    (continueWith action next).IsQueryBoundP IsSign count := by
  cases action with
  | ok value => exact bounded value
  | fail error => trivial
  | div => trivial

private theorem result_bound (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp Spec (RustM (Result Encoded))) (count : Nat)
    (bounded : ∀ value, (next value).IsQueryBoundP IsSign count) :
    (continueResult action next).IsQueryBoundP IsSign count := by
  cases action with
  | ok result => cases result with
    | Ok value => exact bounded value
    | Err previous => trivial
  | fail error => trivial
  | div => trivial

private theorem ready_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) : (ready encode pending).IsQueryBoundP IsSign 0 := by
  rw [RegistrationWorldServerPublication.ready_pure]
  trivial

private theorem signing_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    (signing encode payload digest pending).IsQueryBoundP IsSign 1 := by
  unfold signing
  apply continue_bound
  intro request
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr (by decide), fun _ => result_bound _ _ 0 (ready_bound encode)⟩

/-- Actual response publication attempts at most one ML signing request before all later failures. -/
theorem program (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    (RegistrationWorldServerPublication.program encode pending).IsQueryBoundP IsSign 1 := by
  unfold RegistrationWorldServerPublication.program
  apply continue_bound
  intro request
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (fun impossible => impossible.elim), fun _ => result_bound _ _ 1 (signing_bound encode _ _)⟩
end Server
end BeaconcryptCore.Computational.RegistrationNativeMldsaSignSyntax

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignSyntax.Beacon.ed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignSyntax.Beacon.ed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignSyntax.Beacon.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignSyntax.Beacon.begin_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignSyntax.Server.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignSyntax.Server.program
