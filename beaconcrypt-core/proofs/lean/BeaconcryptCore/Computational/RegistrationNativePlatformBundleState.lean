-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationReplay
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap

/-! Actual nested owner/environment/native/platform effects form one joint state. The product transformation is an exact monad homomorphism through every source publication stage, retaining each state component and every failed prefix. This permits same-prefix tuple receipts without a terminal writer-purity premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundleState
variable {Owners Env Native Platform Value Next Encoded : Type}
abbrev M := StateT Owners (StateT Env (StateT Native (StateT Platform ProbComp)))
abbrev State := Owners × (Env × (Native × Platform))
local notation "JointState" => State (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform)

def arrange (result : (((Value × Owners) × Env) × Native) × Platform) : Value × JointState :=
  (result.1.1.1.1, (result.1.1.1.2, (result.1.1.2, (result.1.2, result.2))))

def joint (work : M (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform) Value) :
    StateT JointState ProbComp Value := fun before =>
  arrange <$> ((((work.run before.1).run before.2.1).run before.2.2.1).run before.2.2.2)

private theorem joint_pure (value : Value) :
    joint (pure value : M (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform) Value) = pure value := by
  funext before
  simp only [joint, StateT.run_pure, map_pure]
  rfl

/-- All four actual state components are threaded in source order through arbitrary adaptive continuations. -/
theorem joint_bind (work : M (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform) Value)
    (next : Value → M (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform) Next) :
    joint (work >>= next) = (joint work >>= fun value => joint (next value)) := by
  funext before
  simp only [joint, StateT.run, StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]
  rfl

private theorem joint_hom :
    Cslib.IsMonadHom (M (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform))
      (StateT JointState ProbComp) joint := .mk' joint_pure joint_bind

/-- Source begin is unchanged by the exact product-state transformation, including recursive signing and the reached terminal writer. -/
theorem begin_joint
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform)))
    (encode : registration.SignedInitView → M (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform)
      (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    joint (RegistrationNativePlatformBeaconPublication.begin impl encode control inputs coins pin mldsa) =
      RegistrationNativePlatformBeaconPublication.begin (fun query => joint (impl query)) (fun view => joint (encode view))
        control inputs coins pin mldsa :=
  RegistrationNativePlatformBeaconMap.begin joint_hom impl encode control inputs coins pin mldsa

/-- Literal nested callback support and its joint-state support describe the same complete source outcome. -/
theorem joint_support (work : M (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform) Value)
    (before after : JointState) (value : Value) :
    (value, after) ∈ support ((joint work).run before) ↔
      ((((value, after.1), after.2.1), after.2.2.1), after.2.2.2) ∈ support
        ((((work.run before.1).run before.2.1).run before.2.2.1).run before.2.2.2) := by
  simp only [joint, StateT.run, support_map]
  constructor
  · rintro ⟨⟨⟨⟨⟨v, owners⟩, env⟩, native⟩, platform⟩, called, same⟩
    cases same
    exact called
  · intro called
    exact ⟨((((value, after.1), after.2.1), after.2.2.1), after.2.2.2), called, rfl⟩


/-- Every actual supported nested source publication retains the reached raw Init tuple and complete crypto prefix together with its subsequent effectful writer support. -/
theorem tuple
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform)))
    (encode : registration.SignedInitView → M (Owners := Owners) (Env := Env) (Native := Native) (Platform := Platform)
      (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (published : registration.PublishedBeaconInit Encoded) (before after : JointState)
    (supported : ((((.ok (.Ok published), after.1), after.2.1), after.2.2.1), after.2.2.2) ∈ support
      ((((RegistrationNativePlatformBeaconPublication.begin impl encode control inputs coins pin mldsa).run before.1).run before.2.1).run before.2.2.1 |>.run before.2.2.2)) :
    ∃ atEncoder view started pending fingerprint atFingerprint,
      (.ok (.Some published.encoded), after) ∈ support ((joint (encode view)).run atEncoder) ∧
      pqxdh.beacon_start control inputs coins = .ok started ∧
      pqxdh.validate_init_kex started.message = .ok (.Ok {
        beacon_identity_public_key := inputs.identity_public_key,
        beacon_prekey_public_key := inputs.prekey_public_key,
        beacon_one_time_public_key := coins.one_time_public_key,
        beacon_pq_public_key := inputs.pq_public_key }) ∧
      registration.begin_beacon_init control inputs coins pin mldsa = .ok (.Ed25519SigningRequested pending) ∧
      RegistrationNativeInitTupleSource.EdLead (fun query => joint (impl query)) pending before fingerprint atFingerprint ∧
      RegistrationNativeInitTupleSource.Fixed started pin inputs.identity_public_key mldsa fingerprint.state ∧
      RegistrationNativeInitTupleSource.Attached started fingerprint.state ∧
      RegistrationNativeInitTupleSource.FingerprintCut (fun query => joint (impl query)) (fun _ => .Some published.encoded)
        fingerprint atFingerprint published atEncoder := by
  have actual := (joint_support (RegistrationNativePlatformBeaconPublication.begin impl encode control inputs coins pin mldsa)
    before after (.ok (.Ok published))).mpr supported
  rw [begin_joint] at actual
  exact RegistrationNativePlatformPublicationReplay.begin_tuple (fun query => joint (impl query)) (fun view => joint (encode view))
    control inputs coins pin mldsa published before after actual

end BeaconcryptCore.Computational.RegistrationNativePlatformBundleState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleState.joint_bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleState.joint_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleState.begin_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleState.begin_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleState.joint_support' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleState.joint_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleState.tuple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleState.tuple
