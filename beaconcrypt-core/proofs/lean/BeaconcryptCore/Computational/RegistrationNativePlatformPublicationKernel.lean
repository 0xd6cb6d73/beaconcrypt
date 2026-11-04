-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication
import BeaconcryptCore.Computational.RegistrationPublicationKernelErasure
/-! The actual effectful Server publication suffix never exposes or reads its retained private ratchet kernel. Source hash/sign requests and the signed-view writer are identical after kernel replacement, including every enclosing writer failure and common platform poststate. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationKernel
open RegistrationNativePlatformServerPublication (continueWith continueResult ready signing program)
open RegistrationPublicationKernelErasure (mapOk result published)
variable {Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem publish (kernel : ConcreteRatchetKernel) (pending : registration.ServerResponseReady)
    (encoded : core.option.Option Encoded) :
    ({ pending with kernel } : registration.ServerResponseReady).publish encoded =
      result kernel (pending.publish encoded) := by
  rw [BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines,
    BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines]
  cases encoded <;> rfl

/-- Actual effectful encoding receives the same signed view and retains every reached writer poststate. -/
theorem ready_map (kernel : ConcreteRatchetKernel)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseReady) :
    ready encode { pending with kernel } = result kernel <$> ready encode pending := by
  have message : ({ pending with kernel } : registration.ServerResponseReady).message = pending.message := rfl
  unfold ready
  rw [message]
  cases asked : pending.message with
  | fail error => simp only [continueWith, map_pure]; rfl
  | div => simp only [continueWith, map_pure]; rfl
  | ok view =>
    simp only [continueWith, map_bind, map_pure]
    apply bind_congr
    intro encoded
    apply congrArg pure
    cases encoded with
    | fail error => rfl
    | div => rfl
    | ok value => exact publish kernel pending value

private theorem continue_map {Input : Type} (kernel : ConcreteRatchetKernel) (transform : Input → Input)
    (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → m (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (preserved : ∀ value, next (transform value) = result kernel <$> next value) :
    continueResult (mapOk transform <$> action) next = result kernel <$> continueResult action next := by
  cases action with
  | fail error => simp only [continueResult, map_pure]; rfl
  | div => simp only [continueResult, map_pure]; rfl
  | ok value => cases value with
    | Err previous => simp only [RawCtxMaterialInterpretation.rust_map_ok, mapOk, continueResult, map_pure]; rfl
    | Ok value =>
      simp only [RawCtxMaterialInterpretation.rust_map_ok, mapOk, continueResult]
      exact preserved value

/-- All raw optional ML replies and exact signature-width branches retain the same effectful writer and public response. -/
theorem signing_map (kernel : ConcreteRatchetKernel) (impl : QueryImpl RegistrationSigningShared.Spec m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    signing impl encode payload digest { pending with kernel } = result kernel <$> signing impl encode payload digest pending := by
  have request : ({ pending with kernel } : registration.ServerResponseSigning).request = pending.request := rfl
  unfold signing
  rw [request]
  cases asked : pending.request with
  | fail error => simp only [continueWith, map_pure]; rfl
  | div => simp only [continueWith, map_pure]; rfl
  | ok request =>
    simp only [continueWith, map_bind]
    apply bind_congr
    intro signature
    rw [RegistrationPublicationKernelErasure.signature_resume_map]
    exact continue_map kernel (fun value : registration.ServerResponseReady => { value with kernel })
      (pending.resume signature) (ready encode) (ready_map kernel encode)

/-- The complete actual hash/sign/stateful-encoder publication phase retains every public request and failure decision under private kernel replacement. -/
theorem program_map (kernel : ConcreteRatchetKernel) (impl : QueryImpl RegistrationSigningShared.Spec m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) :
    program impl encode { pending with kernel } = result kernel <$> program impl encode pending := by
  have request : ({ pending with kernel } : registration.ServerResponseHash).request = pending.request := rfl
  unfold program
  rw [request]
  cases asked : pending.request with
  | fail error => simp only [continueWith, map_pure]; rfl
  | div => simp only [continueWith, map_pure]; rfl
  | ok request =>
    simp only [continueWith, map_bind]
    apply bind_congr
    intro digest
    rw [RegistrationPublicationKernelErasure.hash_resume_map]
    exact continue_map kernel (fun value : registration.ServerResponseSigning => { value with kernel })
      (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)))
      (signing impl encode ⟨.server, BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request⟩ digest)
      (signing_map kernel impl encode _ digest)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationKernel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationKernel.ready_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationKernel.ready_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationKernel.signing_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationKernel.signing_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationKernel.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationKernel.program_map
