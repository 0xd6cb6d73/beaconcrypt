-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Funs
import BeaconcryptCore.Computational.RegistrationAgreementTermination
import BeaconcryptCore.PanicFreedom.KeyAgreement

/-! Every actual public agreement continuation decreases the source phase rank, retaining the private local identity, ephemeral key and RNG state in the same iteration. Primitive Rust failures and divergence stop before another iteration. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop
open BeaconcryptCore.Computational RegistrationAgreementExecutor

private theorem bind_cut {A B : Type} (first : RustM A) (next : A → RustM B) (result : B)
    (actual : (first >>= next) = .ok result) : ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | fail error | div => cases actual
  | ok value => exact ⟨value, rfl, actual⟩

private theorem progress {before after : agreement.AgreementEffect} (edge : Step before after)
    (positive : 0 < rank before) : rank after < rank before := by
  rcases step_progress edge with smaller | ⟨zero, _⟩
  · exact smaller
  · omega

variable [PublicWrapperPlatform.Material] [AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
abbrev State (R : Type) := agreement.AgreementEffect × R × Option (zeroize.Zeroizing (Std.Array U8 32#usize)) ×
  Option beaconcrypt_crypto.crypto_kx.KeyPair

def body {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : beaconcrypt_public_wrapper.pqxdh.RegistrationKeys)
    (state : State R) : RustM (ControlFlow (State R) (agreement.AgreementEffect × R)) :=
  beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop.body generator keys.identity_secret keys.beacon_prekey
    keys.beacon_one_time keys.beacon_kem state.1 state.2.1 state.2.2.1 state.2.2.2

theorem body_progress {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : beaconcrypt_public_wrapper.pqxdh.RegistrationKeys) (before after : State R)
    (actual : body generator keys before = .ok (.cont after)) : rank after.1 < rank before.1 := by
  rcases before with ⟨phase, coins, localIdentity, ephemeral⟩
  rcases after with ⟨next, nextCoins, nextLocal, nextEphemeral⟩
  cases phase with
  | Rejected _ | ServerComplete _ | BeaconComplete _ => cases actual
  | ConvertPublic pending =>
      obtain ⟨requested, request, called⟩ := bind_cut _ _ _ actual
      obtain ⟨slice, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨parsed, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨optional, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨reply, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨finished, resumed, returned⟩ := bind_cut _ _ _ called
      cases returned
      exact progress (.convertPublic pending requested reply next request resumed) (by simp only [rank]; omega)
  | ConvertSecret pending =>
      obtain ⟨converted, _, called⟩ := bind_cut _ _ _ actual
      obtain ⟨optional, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨saved, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨present, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨finished, resumed, returned⟩ := bind_cut _ _ _ called
      cases returned
      obtain ⟨role, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_role_total pending
      exact progress (.convertSecret pending role present next requested resumed) (by simp only [rank]; omega)
  | GenerateEphemeral pending =>
      obtain ⟨generated, _, called⟩ := bind_cut _ _ _ actual
      rcases generated with ⟨reply, nextCoins⟩
      obtain ⟨saved, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨borrowed, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨publicKey, _, called⟩ := bind_cut _ _ _ called
      obtain ⟨finished, resumed, returned⟩ := bind_cut _ _ _ called
      cases returned
      obtain ⟨role, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_role_total pending
      exact progress (.generate pending role publicKey next requested resumed) (by simp only [rank]; omega)
  | Encapsulate pending =>
      obtain ⟨calledResult, _, called⟩ := bind_cut _ _ _ actual
      rcases calledResult with ⟨reply, capture, back⟩
      obtain ⟨finished, resumed, returned⟩ := bind_cut _ _ _ called
      cases returned
      obtain ⟨publicKey, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_key_total pending
      exact progress (.encapsulate pending publicKey reply next requested resumed) (by simp only [rank]; omega)
  | Decapsulate pending =>
      obtain ⟨reply, _, called⟩ := bind_cut _ _ _ actual
      obtain ⟨finished, resumed, returned⟩ := bind_cut _ _ _ called
      cases returned
      obtain ⟨ciphertext, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_ciphertext_total pending
      exact progress (.decapsulate pending ciphertext reply next requested resumed) (by simp only [rank]; omega)
  | Dh pending =>
      obtain ⟨request, requested, called⟩ := bind_cut _ _ _ actual
      cases role : request.secret_role with
      | LocalIdentity | ServerEphemeral =>
          simp only [role] at called
          obtain ⟨borrowed, _, called⟩ := bind_cut _ _ _ called
          obtain ⟨reply, _, called⟩ := bind_cut _ _ _ called
          obtain ⟨finished, resumed, returned⟩ := bind_cut _ _ _ called
          cases returned
          exact progress (.dh pending request reply next requested resumed) (by cases position : pending.position <;> simp only [rank, position] <;> omega)
      | BeaconPrekey | BeaconOneTime =>
          simp only [role] at called
          obtain ⟨reply, _, called⟩ := bind_cut _ _ _ called
          obtain ⟨finished, resumed, returned⟩ := bind_cut _ _ _ called
          cases returned
          exact progress (.dh pending request reply next requested resumed) (by cases position : pending.position <;> simp only [rank, position] <;> omega)
  | RootKdf pending =>
      obtain ⟨reply, _, called⟩ := bind_cut _ _ _ actual
      obtain ⟨finished, resumed, returned⟩ := bind_cut _ _ _ called
      cases returned
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_request_total pending
      exact progress (.root pending request reply next requested resumed) (by simp only [rank]; omega)

def drive {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : beaconcrypt_public_wrapper.pqxdh.RegistrationKeys) :
    Nat → State R → RustM (agreement.AgreementEffect × R)
  | 0, _ => .div
  | fuel + 1, state => do
      let decision ← body generator keys state
      match decision with
      | .cont next => drive generator keys fuel next
      | .done result => .ok result

theorem loop_specializes {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : beaconcrypt_public_wrapper.pqxdh.RegistrationKeys) (fuel : Nat) (state : State R)
    (enough : rank state.1 < fuel) : drive generator keys fuel state =
      beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop generator state.1 keys.identity_secret keys.beacon_prekey
        keys.beacon_one_time keys.beacon_kem state.2.1 state.2.2.1 state.2.2.2 := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      change drive generator keys (fuel + 1) state = loop (body generator keys) state
      rw [drive, loop.eq_def]
      cases actual : body generator keys state with
      | fail error | div => rfl
      | ok decision => cases decision with
        | done result => rfl
        | cont next =>
            have smaller := body_progress generator keys state next actual
            change drive generator keys fuel next = loop (body generator keys) next
            exact ih next (by omega)

def execute {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : beaconcrypt_public_wrapper.pqxdh.RegistrationKeys)
    (state : State R) : RustM (agreement.AgreementEffect × R) := drive generator keys (rank state.1 + 1) state

theorem specializes {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : beaconcrypt_public_wrapper.pqxdh.RegistrationKeys) (state : State R) :
    execute generator keys state =
      beaconcrypt_public_wrapper.pqxdh.execute_agreement_loop generator state.1 keys.identity_secret keys.beacon_prekey
        keys.beacon_one_time keys.beacon_kem state.2.1 state.2.2.1 state.2.2.2 :=
  loop_specializes generator keys _ state (by omega)

end BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop.body_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop.body_progress

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop.loop_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop.loop_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop.specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop.specializes
