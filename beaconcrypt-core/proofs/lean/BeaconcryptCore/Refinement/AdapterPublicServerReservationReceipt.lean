-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention
import BeaconcryptCore.Refinement.AdapterPublicServerReplayPrefix
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The literal source replay-set reservation precedes the same captured SDK agreement and one-use insertion. Every failed reservation keeps its returned opaque set and full platform poststate; the private receipt is absent exactly on paths where agreement is skipped. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerReservationReceipt
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerAgreementReceipt (Word)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [original : CryptoOperations (RustT ProbComp)]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]
local notation "NativeM" => StateT (RegistrationNativeExperiment.State n KemSK mlSource) m
abbrev Receipt (R : Type) := Option (AdapterPublicServerAgreementReceipt.Receipt R)

noncomputable def program (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beaconcrypt_public_wrapper.server.Server) (control : pqxdh.ServerState)
    (authenticated : registration.AuthenticatedInit) (rng : R) : NativeM (Receipt R × RustM (Word R)) := do
  let allocated ← (AdapterPublicServerAcceptBody.setReserve (m := NativeM) self.consumed_registrations).run
  match allocated with
  | .fail error => pure (none, .fail error)
  | .div => pure (none, .div)
  | .ok (allocation, history) =>
    let current := {self with consumed_registrations := history}
    match allocation with
    | .Err _ => pure (none, .ok (.None, current, rng))
    | .Ok _ =>
      (fun result => (some result.1, result.2)) <$>
        AdapterPublicServerAgreementReceipt.program coins generator
          (AdapterPublicAgreementServerNative.keys (platform.arcView self.identity).identity_key.secret_key)
          current (RegistrationAgreementExecutor.server control .Fresh authenticated) rng

theorem sdk (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beaconcrypt_public_wrapper.server.Server) (control : pqxdh.ServerState)
    (authenticated : registration.AuthenticatedInit) (rng : R) :
    letI : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
    Prod.snd <$> program coins generator self control authenticated rng =
      (do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_server_agreement control .Fresh authenticated)
          AdapterPublicServerAcceptBody.reserved (m := NativeM) generator self rng phase).run := by
  let : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  obtain ⟨phase, started⟩ := AdapterPublicServerReplayPrefix.begin_fresh control authenticated
  rw [started]
  simp only [RustT.run_bind, RustT.run_liftRust, pure_bind]
  unfold program AdapterPublicServerAcceptBody.reserved
  rw [map_bind, RustT.run_bind]
  apply bind_congr
  intro allocated
  cases allocated with
  | fail error | div => simp only [map_pure]
  | ok pair =>
    rcases pair with ⟨allocation, history⟩
    cases allocation with
    | Err error => simp only [map_pure, RustT.run_pure]
    | Ok _ =>
      simp only [Functor.map_map]
      change Prod.snd <$> AdapterPublicServerAgreementReceipt.program coins generator
        (AdapterPublicAgreementServerNative.keys (platform.arcView self.identity).identity_key.secret_key)
        {self with consumed_registrations := history} (RegistrationAgreementExecutor.server control .Fresh authenticated) rng = _
      rw [AdapterPublicServerAgreementReceipt.sdk]
      rw [started]
      simp only [RustT.run_bind, RustT.run_liftRust, pure_bind]
      have getter : beaconcrypt_public_request.server.Server.identity_sk (m := RustT NativeM)
          {self with consumed_registrations := history} = pure (platform.arcView self.identity).identity_key.secret_key := by
        change (do
          let identity ← (AdapterRecordRequestMonad.liftRust (.ok (platform.arcView self.identity)) : RustT NativeM _)
          AdapterRecordRequestMonad.liftRust (.ok identity.identity_key.secret_key)) = _
        apply RustT.ext
        simp only [RustT.run_bind, RustT.run_liftRust, RustT.run_pure, pure_bind]
      rw [getter, RustT.run_pure, pure_bind]
      rfl

end BeaconcryptCore.Refinement.AdapterPublicServerReservationReceipt

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerReservationReceipt.sdk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerReservationReceipt.sdk
