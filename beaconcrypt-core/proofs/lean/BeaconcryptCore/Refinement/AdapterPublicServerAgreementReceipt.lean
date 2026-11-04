-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame
import BeaconcryptCore.Refinement.AdapterPublicServerRetainPlatform
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Private instrumentation of the actual source agreement retains its same captured request/reply tree across the literal replay insertion. Erasing the receipt recovers the actual SDK start, execute and replay body, with complete Rust results, returned RNG and shared Native/platform poststate. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAgreementReceipt
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementInterpreter (Capture)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK : Type} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [original : CryptoOperations (RustT ProbComp)]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) m))]
local notation "NativeM" => StateT (RegistrationNativeExperiment.State n KemSK source) m
abbrev Receipt (R : Type) := RustM (((RustM agreement.AgreementEffect) × RegistrationAgreementQueryTrace.Trace) × Capture R)
abbrev Word (R : Type) := core.option.Option beaconcrypt_public_wrapper.server.RegistrationOutput × beaconcrypt_public_wrapper.server.Server × R

noncomputable def replay {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (receipt : Receipt R) : NativeM (RustM (Word R)) :=
  match receipt with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok ((effect, _journal), capture) =>
    (do let completed ← AdapterRecordRequestMonad.liftRust effect
        AdapterPublicServerAcceptBody.record (m := NativeM) self capture.rng completed).run

noncomputable def program (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : Keys) (self : beaconcrypt_public_wrapper.server.Server)
    (work : OracleComp Spec (RustM agreement.AgreementEffect)) (rng : R) : NativeM (Receipt R × RustM (Word R)) := do
  let receipt ← (AdapterPublicAgreementNativePlatformInterpreter.captured coins generator keys work rng).run
  let returned ← replay self receipt
  pure (receipt, returned)

theorem erasure (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : Keys) (self : beaconcrypt_public_wrapper.server.Server)
    (work : OracleComp Spec (RustM agreement.AgreementEffect)) (rng : R) :
    Prod.snd <$> program (n := n) (KemSK := KemSK) (source := source) coins generator keys self work rng =
      (do let ((effect, _journal), capture) ← AdapterPublicAgreementNativePlatformInterpreter.captured coins generator keys work rng
          let completed ← AdapterRecordRequestMonad.liftRust effect
          AdapterPublicServerAcceptBody.record (m := NativeM) self capture.rng completed).run := by
  unfold program
  rw [map_bind]
  simp only [RustT.run_bind]
  apply bind_congr
  intro receipt
  cases receipt with
  | fail error | div => simp only [replay, pure_bind, map_pure]
  | ok pair =>
    rcases pair with ⟨⟨effect, journal⟩, capture⟩
    simp only [replay, bind_pure_comp, Functor.map_map]
    change (id <$> replay (n := n) (KemSK := KemSK) (source := source) self (.ok ((effect, journal), capture))) = _
    rw [id_map]
    rfl

theorem sdk (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : Keys) (self : beaconcrypt_public_wrapper.server.Server)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (rng : R) :
    letI : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
    Prod.snd <$> program coins generator keys self (RegistrationAgreementExecutor.server control status authenticated) rng =
      (do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_server_agreement control status authenticated)
          let (effect, nextRng) ← beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT NativeM) generator phase keys rng
          AdapterPublicServerAcceptBody.record (m := NativeM) self nextRng effect).run := by
  let : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  rw [erasure]
  have actual := congrArg (fun action => (action >>= fun result => AdapterPublicServerAcceptBody.record (m := NativeM) self result.2 result.1).run)
    (AdapterPublicAgreementNativePlatformInterpreter.execute_trace (n := n) (KemSK := KemSK) (source := source) coins generator keys control status authenticated rng)
  simpa only [bind_assoc, pure_bind] using actual.symm
end BeaconcryptCore.Refinement.AdapterPublicServerAgreementReceipt

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementReceipt.erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementReceipt.erasure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementReceipt.sdk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementReceipt.sdk
