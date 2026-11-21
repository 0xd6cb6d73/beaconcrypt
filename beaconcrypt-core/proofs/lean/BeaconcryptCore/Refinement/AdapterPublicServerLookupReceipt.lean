-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerReservationNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The literal actual source replay lookup surrounds reservation and agreement with private receipt instrumentation. The requested identifier is the unique successful result derived from the original Core request; consumed requests skip all allocation and primitive work, retaining their original role state. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerAgreementReceipt (Word)
open AdapterPublicServerReservationReceipt (Receipt)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

omit material platform ed in
noncomputable def identifier (pending : peer.RegistrationLookup) : pqxdh.RegistrationId :=
  Classical.choose (PeerOwnership.registration_lookup_request_bytes pending)

omit material platform ed in
theorem requested (pending : peer.RegistrationLookup) : pending.request = .ok (identifier pending) :=
  (Classical.choose_spec (PeerOwnership.registration_lookup_request_bytes pending)).1

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [original : CryptoOperations (RustT ProbComp)]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]
local notation "NativeM" => StateT (RegistrationNativeExperiment.State n KemSK mlSource) m

noncomputable def program (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : peer.RegistrationLookup) (rng : R) :
    NativeM (Receipt R × RustM (Word R)) := do
  let observed ← (AdapterPublicServerReplayPrefix.contains (m := NativeM) self.consumed_registrations (identifier pending).bytes).run
  match observed with
  | .fail error => pure (none, .fail error)
  | .div => pure (none, .div)
  | .ok true => pure (none, .ok (.None, self, rng))
  | .ok false => AdapterPublicServerReservationReceipt.program coins generator self pending.control pending.authenticated rng

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [LawfulMonad m] original containers in
private theorem lift_ok {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : RustT NativeM A) = pure value := rfl

theorem sdk (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : peer.RegistrationLookup) (rng : R) :
    letI : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
    Prod.snd <$> program (n := n) (KemSK := KemSK) (mlSource := mlSource) coins generator self pending rng =
      (AdapterPublicServerAcceptBody.acceptLookup (m := NativeM) generator self pending rng).run := by
  let : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  unfold program AdapterPublicServerAcceptBody.acceptLookup
  rw [requested]
  simp only [lift_ok, pure_bind, pqxdh.RegistrationId.as_bytes]
  rw [map_bind, RustT.run_bind]
  apply bind_congr
  intro observed
  cases observed with
  | fail error | div => simp only [map_pure]
  | ok present =>
    cases present with
    | true => simp only [PeerOwnership.registration_lookup_consumed, lift_ok, pure_bind, RustT.run_pure, map_pure]
    | false =>
      rw [AdapterPublicServerReservationReceipt.sdk]
      obtain ⟨phase, started⟩ := AdapterPublicServerReplayPrefix.begin_fresh pending.control pending.authenticated
      simp only [PeerOwnership.registration_lookup_fresh, started, lift_ok, pure_bind]

theorem member (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : peer.RegistrationLookup) (rng : R)
    (present : Bool)
    (operation : AdapterPublicServerReplayPrefix.contains (m := NativeM) self.consumed_registrations (identifier pending).bytes = pure present) :
    program (n := n) (KemSK := KemSK) (mlSource := mlSource) coins generator self pending rng =
      if present then pure (none, .ok (.None, self, rng))
      else AdapterPublicServerReservationReceipt.program coins generator self pending.control pending.authenticated rng := by
  unfold program
  rw [operation, RustT.run_pure, pure_bind]
  cases present <;> rfl

end BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt.requested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt.requested

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt.sdk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt.sdk

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt.member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt.member
