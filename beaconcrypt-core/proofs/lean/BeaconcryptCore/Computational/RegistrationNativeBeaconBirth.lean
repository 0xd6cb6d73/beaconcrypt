-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend

/-! Birth receipts expose the actual indexed key-creation callback and owner-allocation callback at their reached states. The new owner stores those replies exactly; local owner indices, generated-key handles and record-World owner indices remain separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconBirth
open RegistrationNativeBeaconFrontend
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Private : Type} {base : OracleSpec ι} {n : Nat}

def owner (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (pin : session.ServerAuthenticationPin)
    (identity : IdentitySeed) (prekey : ScalarBytes)
    (born : Nat × PqxdhKemIndCca.MlKem768PublicKey) (worldOwner : Nat) : Owner mlSource :=
  ⟨pin, identity, prekey,
    PqxdhRootTableInitialization.rootArray (setup.dh.publicKey prekey), born.1, born.2, worldOwner, .fresh, []⟩

/-- No native state or environment log is replaced while the two actual external callbacks execute. -/
theorem append_program (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (keyId : U64)
    (pin : session.ServerAuthenticationPin)
    (identity : IdentitySeed) (prekey : ScalarBytes) (owners : State mlSource) (env : EnvState Auxiliary) :
    ((appendBorn (n := n) setup mlSource edPin keyId pin identity prekey).run owners).run env = (do
      let born : Nat × PqxdhKemIndCca.MlKem768PublicKey ← (Trusted n KemSK).query (.inr (.inr (.inl .create)))
      let worldOwner : Nat ← (Trusted n KemSK).query (.inl (.inr (.appendOwner keyId edPin .fresh)))
      pure ((.ok (some owners.length), owners ++ [owner setup mlSource pin identity prekey born worldOwner]), env)) := by
  simp only [appendBorn, kem, effect, StateT.run_bind, StateT.run_lift, StateT.run_pure,
    StateT.run_get, bind_pure_comp, owner]
  rfl

/-- A successful owner birth carries the actual reached indexed-KEM and World-allocation query supports. -/
theorem append_supported (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (implementation : QueryImpl (Trusted n KemSK) (StateT Private ProbComp))
    (edPin : Std.Array U8 32#usize) (keyId : U64)
    (pin : session.ServerAuthenticationPin)
    (identity : IdentitySeed) (prekey : ScalarBytes) (owners : State mlSource) (env : EnvState Auxiliary)
    (before : Private)
    (result : ((RustM (Option Nat) × State mlSource) × EnvState Auxiliary) × Private)
    (supported : result ∈ support ((simulateQ implementation
      (((appendBorn setup mlSource edPin keyId pin identity prekey).run owners).run env)).run before)) :
    ∃ born middle worldOwner after,
      (born, middle) ∈ support ((implementation (.inr (.inr (.inl .create)))).run before) ∧
      (worldOwner, after) ∈ support ((implementation (.inl (.inr (.appendOwner keyId edPin .fresh)))).run middle) ∧
      result = (((.ok (some owners.length), owners ++
        [owner setup mlSource pin identity prekey born worldOwner]), env), after) := by
  rw [append_program] at supported
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨⟨born, middle⟩, generated, ⟨⟨worldOwner, after⟩, allocated, final⟩⟩ := supported
  exact ⟨born, middle, worldOwner, after, generated, allocated, final⟩

/-- The public constructor reaches indexed birth only after its actual successful source prefix. -/
theorem create_program (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State mlSource) (env : EnvState Auxiliary) :
    ((create (n := n) setup mlSource edPin mlPin keyId).run owners).run env = (do
      let earlier ← ((prepare (n := n) (KemSK := KemSK) mlSource edPin mlPin keyId).run owners).run env
      match earlier.1.1 with
      | .ok (some prepared) =>
          ((appendBorn setup mlSource edPin keyId prepared.pin prepared.identity prepared.prekey).run earlier.1.2).run earlier.2
      | .ok none => pure ((.ok none, earlier.1.2), earlier.2)
      | .fail error => pure ((.fail error, earlier.1.2), earlier.2)
      | .div => pure ((.div, earlier.1.2), earlier.2)) := by
  simp only [create, StateT.run_bind]
  congr 1
  funext earlier
  rcases earlier with ⟨⟨action, leadingOwners⟩, leadingEnv⟩
  cases action with
  | fail error => rfl
  | div => rfl
  | ok selected => cases selected <;> rfl

theorem create_supported (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (implementation : QueryImpl (Trusted n KemSK) (StateT Private ProbComp))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State mlSource) (env : EnvState Auxiliary) (before : Private)
    (index : Nat) (ownersAfter : State mlSource) (envAfter : EnvState Auxiliary) (after : Private)
    (supported : (((.ok (some index), ownersAfter), envAfter), after) ∈ support
      ((simulateQ implementation (((create setup mlSource edPin mlPin keyId).run owners).run env)).run before)) :
    ∃ prepared leadingOwners leadingEnv middle,
      (((.ok (some prepared), leadingOwners), leadingEnv), middle) ∈ support
        ((simulateQ implementation (((prepare mlSource edPin mlPin keyId).run owners).run env)).run before) ∧
      (((.ok (some index), ownersAfter), envAfter), after) ∈ support
        ((simulateQ implementation (((appendBorn setup mlSource edPin keyId prepared.pin
          prepared.identity prepared.prekey).run leadingOwners).run leadingEnv)).run middle) := by
  rw [create_program] at supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨⟨earlier, leadingOwners⟩, leadingEnv⟩, middle⟩, reached, continued⟩ := supported
  cases earlier with
  | fail error => simp [simulateQ_pure, StateT.run_pure] at continued
  | div => simp [simulateQ_pure, StateT.run_pure] at continued
  | ok selected => cases selected with
    | none => simp [simulateQ_pure, StateT.run_pure] at continued
    | some prepared => exact ⟨prepared, leadingOwners, leadingEnv, middle, reached, continued⟩

end BeaconcryptCore.Computational.RegistrationNativeBeaconBirth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconBirth.append_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconBirth.append_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconBirth.append_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconBirth.append_supported

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconBirth.create_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconBirth.create_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconBirth.create_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconBirth.create_supported
