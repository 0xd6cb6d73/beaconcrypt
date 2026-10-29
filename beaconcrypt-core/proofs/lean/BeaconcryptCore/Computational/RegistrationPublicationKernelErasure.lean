-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationKernelErasure

/-! Actual response hashing, optional ML signing, width admission and dynamic encoding never inspect the private advanced kernel. The complete publication controller therefore commutes with replacing only that kernel, including every rejection path and actual signing attempt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationPublicationKernelErasure
open RegistrationWorldServerPublication
variable {Encoded : Type}

def mapOk {Input Output : Type} (f : Input → Output) :
    core.result.Result Input pqxdh.ServerState → core.result.Result Output pqxdh.ServerState
  | .Err previous => .Err previous
  | .Ok value => .Ok (f value)

def published (kernel : ConcreteRatchetKernel) (value : registration.PublishedServerResponse Encoded) :
    registration.PublishedServerResponse Encoded := { value with kernel }

def result (kernel : ConcreteRatchetKernel) (value : RustM (Result Encoded)) : RustM (Result Encoded) :=
  mapOk (published kernel) <$> value

private theorem continueResult_map {Input : Type} (kernel : ConcreteRatchetKernel) (f : Input → Input)
    (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp RegistrationSigningShared.Spec (RustM (Result Encoded)))
    (mapped : ∀ value, next (f value) = result kernel <$> next value) :
    continueResult (mapOk f <$> action) next = result kernel <$> continueResult action next := by
  cases action with
  | fail error => rfl
  | div => rfl
  | ok value => cases value <;> simp [RawCtxMaterialInterpretation.rust_map_ok, mapOk,
      continueResult, result, mapped]

/-- The source digest continuation retains a kernel without reading it. -/
theorem hash_resume_map (kernel : ConcreteRatchetKernel) (pending : registration.ServerResponseHash)
    (digest : core.option.Option (Array U8 64#usize)) :
    ({ pending with kernel } : registration.ServerResponseHash).resume digest =
      mapOk (fun value : registration.ServerResponseSigning => { value with kernel }) <$> pending.resume digest := by
  cases digest <;> simp only [registration.ServerResponseHash.resume, pqxdh.server_abort_candidate,
    bind_tc_ok, map_bind, RawCtxMaterialInterpretation.rust_map_ok, mapOk]

/-- The actual optional signature and exact-width gate do not inspect the retained kernel. -/
theorem signature_resume_map (kernel : ConcreteRatchetKernel) (pending : registration.ServerResponseSigning)
    (signature : core.option.Option (Slice U8)) :
    ({ pending with kernel } : registration.ServerResponseSigning).resume signature =
      mapOk (fun value : registration.ServerResponseReady => { value with kernel }) <$> pending.resume signature := by
  cases signature <;> simp only [registration.ServerResponseSigning.resume, pqxdh.server_abort_candidate,
    bind_tc_ok, map_bind, RawCtxMaterialInterpretation.rust_map_ok, mapOk]
  congr 1
  funext converted
  cases converted <;> rfl

/-- Dynamic encoding sees exactly the same signed native view under kernel replacement. -/
theorem ready_map (kernel : ConcreteRatchetKernel)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) :
    ready encode { pending with kernel } = result kernel <$> ready encode pending := by
  rw [ready_pure, ready_pure]
  simp only [map_pure]
  apply congrArg pure
  simp only [result, map_bind]
  congr 1
  funext view
  rw [BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines,
    BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines]
  cases encode view <;> rfl

/-- All real signing queries and later publication decisions are independent of the private retained kernel. -/
theorem signing_map (kernel : ConcreteRatchetKernel)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    signing encode payload digest { pending with kernel } =
      result kernel <$> signing encode payload digest pending := by
  simp only [signing, registration.ServerResponseSigning.request,
    session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.public_key,
    bind_tc_ok, continueWith, map_bind]
  apply bind_congr
  intro signature
  rw [signature_resume_map]
  exact continueResult_map kernel (fun value : registration.ServerResponseReady => { value with kernel })
    (pending.resume signature) (ready encode) (ready_map kernel encode)

/-- Complete native response publication commutes with hidden-kernel replacement while retaining every hash/sign effect. -/
theorem program_map (kernel : ConcreteRatchetKernel)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    program encode { pending with kernel } = result kernel <$> program encode pending := by
  have request : ({ pending with kernel } : registration.ServerResponseHash).request = pending.request := rfl
  simp only [program, request]
  cases requested : pending.request with
  | fail error => simp only [continueWith, map_pure]; rfl
  | div => simp only [continueWith, map_pure]; rfl
  | ok hash =>
    simp only [continueWith, map_bind]
    apply bind_congr
    intro digest
    rw [hash_resume_map]
    exact continueResult_map kernel (fun value : registration.ServerResponseSigning => { value with kernel })
      (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)))
      (signing encode ⟨.server, BeaconcryptCore.Refinement.RegistrationInputs.hashBytes hash⟩ digest)
      (signing_map kernel encode _ digest)

end BeaconcryptCore.Computational.RegistrationPublicationKernelErasure

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationKernelErasure.hash_resume_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationKernelErasure.hash_resume_map

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationKernelErasure.signature_resume_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationKernelErasure.signature_resume_map

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationKernelErasure.ready_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationKernelErasure.ready_map

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationKernelErasure.signing_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationKernelErasure.signing_map

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationKernelErasure.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationKernelErasure.program_map
