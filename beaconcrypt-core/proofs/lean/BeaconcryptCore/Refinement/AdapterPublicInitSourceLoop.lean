-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationSigning
import BeaconcryptCore.Refinement.RegistrationSigningContinuations

/-! The actual public Init-ready loop follows the three Ed stages and transcript hash in source order. Every continued source iteration strictly reduces the rank, independently of primitive success; finite source-body driving equals the original extracted loop. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop

def edRank (pending : registration.BeaconEd25519Signing) : Nat :=
  match pending.stage with
  | .PreKey => 3
  | .OneTimeKey => 2
  | .PqKey => 1

def rank : registration.BeaconInitEffect → Nat
  | .Rejected _ | .Ready _ => 0
  | .Ed25519SigningRequested pending => edRank pending + 1
  | .HashRequested _ => 1

private theorem bind_cut {A B : Type} (first : RustM A) (next : A → RustM B) (result : B)
    (actual : (first >>= next) = .ok result) : ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | fail error | div => cases actual
  | ok value => exact ⟨value, rfl, actual⟩

theorem ed_progress (pending : registration.BeaconEd25519Signing) (reply : Option (Slice U8))
    (after : registration.BeaconInitEffect) (actual : pending.resume reply = .ok after) :
    rank after < rank (.Ed25519SigningRequested pending) := by
  obtain ⟨result, resumed, allowed⟩ := RegistrationSigning.ed_resume_refines pending reply
  have same : result = after := RustM.ok.inj (resumed.symm.trans actual)
  subst result
  cases after with
  | Ed25519SigningRequested next =>
      cases stage : pending.stage <;>
        simp only [RegistrationSigning.EdReplyTransition, stage] at allowed
      · simp only [rank, edRank, allowed.2.1, stage]; omega
      · simp only [rank, edRank, allowed.2.1, stage]; omega
      · exact allowed.2.elim
  | Rejected _ =>
      cases stage : pending.stage <;> simp only [rank, edRank, stage] <;> omega
  | HashRequested _ =>
      simp only [RegistrationSigning.EdReplyTransition] at allowed
      simp only [rank, edRank, allowed.2.1]; omega
  | Ready _ => exact allowed.elim

theorem hash_progress (pending : registration.BeaconInitHash) (reply : Option (Std.Array U8 64#usize))
    (after : registration.BeaconInitEffect) (actual : pending.resume reply = .ok after) :
    rank after < rank (.HashRequested pending) := by
  cases reply with
  | none => cases actual; simp only [rank]; omega
  | some digest => cases actual; simp only [rank]; omega

variable [PublicWrapperPlatform.Material] [AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.CryptoOperations] [beaconcrypt.auth.Operations]
abbrev body := beaconcrypt_public_wrapper.beacon._proof_beacon_init_ready_loop.body

theorem body_progress (beacon : beaconcrypt_public_wrapper.beacon.Beacon) (before after : registration.BeaconInitEffect)
    (actual : body beacon before = .ok (.cont after)) : rank after < rank before := by
  cases before with
  | Rejected _ | Ready _ => cases actual
  | Ed25519SigningRequested pending =>
      obtain ⟨request, _, called⟩ := bind_cut _ _ _ actual
      obtain ⟨publicKey, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨bytes, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨comparison, _, called⟩ := bind_cut _ _ _ called
      cases comparison with
      | true =>
          obtain ⟨secretKey, _, called⟩ := bind_cut _ _ _ called
          obtain ⟨signed, _, called⟩ := bind_cut _ _ _ called
          obtain ⟨optional, _, called⟩ := bind_cut _ _ _ called
          obtain ⟨borrowed, _, called⟩ := bind_cut _ _ _ called
          obtain ⟨next, resumed, returned⟩ := bind_cut _ _ _ called
          cases returned
          exact ed_progress pending borrowed after resumed
      | false =>
          obtain ⟨borrowed, _, called⟩ := bind_cut _ _ _ called
          obtain ⟨next, resumed, returned⟩ := bind_cut _ _ _ called
          cases returned
          exact ed_progress pending borrowed after resumed
  | HashRequested pending =>
      obtain ⟨request, _, called⟩ := bind_cut _ _ _ actual
      obtain ⟨digest, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨next, resumed, returned⟩ := bind_cut _ _ _ called
      cases returned
      exact hash_progress pending digest after resumed

def drive (beacon : beaconcrypt_public_wrapper.beacon.Beacon) :
    Nat → registration.BeaconInitEffect → RustM (Option registration.BeaconInitReady)
  | 0, _ => .div
  | fuel + 1, effect => do
      let decision ← body beacon effect
      match decision with
      | .cont next => drive beacon fuel next
      | .done result => .ok result

theorem loop_specializes (beacon : beaconcrypt_public_wrapper.beacon.Beacon) (fuel : Nat)
    (effect : registration.BeaconInitEffect) (enough : rank effect < fuel) :
    drive beacon fuel effect = beaconcrypt_public_wrapper.beacon._proof_beacon_init_ready_loop effect beacon := by
  induction fuel generalizing effect with
  | zero => omega
  | succ fuel ih =>
      change drive beacon (fuel + 1) effect = loop (body beacon) effect
      rw [drive, loop.eq_def]
      cases actual : body beacon effect with
      | fail error | div => rfl
      | ok decision => cases decision with
        | done result => rfl
        | cont next =>
            have smaller := body_progress beacon effect next actual
            change drive beacon fuel next = loop (body beacon) next
            exact ih next (by omega)

def execute (beacon : beaconcrypt_public_wrapper.beacon.Beacon) (effect : registration.BeaconInitEffect) :
    RustM (Option registration.BeaconInitReady) := drive beacon (rank effect + 1) effect

theorem specializes (beacon : beaconcrypt_public_wrapper.beacon.Beacon) (effect : registration.BeaconInitEffect) :
    execute beacon effect = beaconcrypt_public_wrapper.beacon._proof_beacon_init_ready_loop effect beacon :=
  loop_specializes beacon _ effect (by omega)

end BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop.body_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop.body_progress

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop.loop_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop.loop_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop.specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop.specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop.ed_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop.ed_progress


/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop.hash_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop.hash_progress
