-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication
import BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter

/-! The actual schema packet fields and extracted registration writer request bodies are composed with the monadic Core publication controller. Crypto and writer primitives share one free request language, so every allocation and mutable serializer outcome is interpreted on the same current state. This module does not identify the deployed wrapper's remaining control/container operations with the older pure native SDK. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformWriter
open BeaconcryptCore.Refinement
abbrev Spec (E : Type) := RegistrationBeaconInitExecutor.Spec + AdapterRegistrationWriterRequestMonad.Spec E

def initPacket (view : registration.InitView) : beaconcrypt_parse.transport.initkex where
  identity_key := view.fields.identity_key.to_slice
  pre_key := view.fields.pre_key.to_slice
  one_time_key := view.fields.one_time_key.to_slice
  pq_key := view.fields.pq_key.to_slice

def responsePacket (view : registration.SignedResponseView) : beaconcrypt_parse.transport.kexresponse where
  identity_key := view.identity_key.to_slice
  ephemeral_key := view.ephemeral_key.to_slice
  kem_cipher_text := view.kem_cipher_text.to_slice
  app_cipher_text := view.application_ciphertext
  key_id := view.key_id
  signature := view.signature.to_slice

/-- This is the literal four-field conversion immediately preceding encode_init in the extracted public wrapper. -/
theorem init_conversion (view : registration.InitView) :
    (do
      let identity ← lift (Array.to_slice view.fields.identity_key)
      let prekey ← lift (Array.to_slice view.fields.pre_key)
      let one ← lift (Array.to_slice view.fields.one_time_key)
      let pq ← lift (Array.to_slice view.fields.pq_key)
      pure (⟨identity, prekey, one, pq⟩ : beaconcrypt_parse.transport.initkex)) =
      (RustM.ok (initPacket view)) := rfl

/-- The actual response conversion retains all public key fields, assigned id, application ciphertext and returned signature. -/
theorem response_conversion (view : registration.SignedResponseView) :
    (do
      let identity ← lift (Array.to_slice view.identity_key)
      let ephemeral ← lift (Array.to_slice view.ephemeral_key)
      let ciphertext ← lift (Array.to_slice view.kem_cipher_text)
      let signature ← lift (Array.to_slice view.signature)
      pure (⟨identity, ephemeral, ciphertext, view.application_ciphertext, view.key_id, signature⟩ :
        beaconcrypt_parse.transport.kexresponse)) = RustM.ok (responsePacket view) := rfl

def cryptoLift {E : Type} : QueryImpl RegistrationBeaconInitExecutor.Spec (OracleComp (Spec E)) :=
  fun request => (Spec E).query (.inl request)

def writerLift {E : Type} : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp (Spec E)) :=
  fun request => (Spec E).query (.inr request)

def signingLift {E : Type} : QueryImpl RegistrationSigningShared.Spec (OracleComp (Spec E)) :=
  fun request => (Spec E).query (.inl (.inl request))

def init (E : Type) (view : registration.InitView) :
    OracleComp (Spec E) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ writerLift (AdapterRegistrationWriterRequestExtraction.encodeInit
    (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) (initPacket view)).run

def response (E : Type) (view : registration.SignedResponseView) :
    OracleComp (Spec E) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ writerLift (AdapterRegistrationWriterRequestExtraction.encodeResponse
    (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) (responsePacket view)).run

def begin (E : Type)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :=
  RegistrationNativePlatformBeaconPublication.begin cryptoLift (init E) control inputs coins pin

def publication (E : Type) (pending : registration.ServerResponseHash) :=
  RegistrationNativePlatformServerPublication.program signingLift (response E) pending

variable {E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

theorem init_interpret
    (implementation : QueryImpl (Spec E) m) (view : registration.InitView) :
    simulateQ implementation (init E view) =
      simulateQ (fun request => implementation (.inr request))
        (AdapterRegistrationWriterRequestExtraction.encodeInit
          (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) (initPacket view)).run := by
  unfold init
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun impl => simulateQ impl
    (AdapterRegistrationWriterRequestExtraction.encodeInit
      (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) (initPacket view)).run)
  funext request
  exact simulateQ_spec_query implementation (.inr request)

theorem response_interpret
    (implementation : QueryImpl (Spec E) m) (view : registration.SignedResponseView) :
    simulateQ implementation (response E view) =
      simulateQ (fun request => implementation (.inr request))
        (AdapterRegistrationWriterRequestExtraction.encodeResponse
          (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) (responsePacket view)).run := by
  unfold response
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun impl => simulateQ impl
    (AdapterRegistrationWriterRequestExtraction.encodeResponse
      (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) (responsePacket view)).run)
  funext request
  exact simulateQ_spec_query implementation (.inr request)

theorem begin_interpret (implementation : QueryImpl (Spec E) m)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    simulateQ implementation (begin E control inputs coins pin) =
      RegistrationNativePlatformBeaconPublication.begin (fun request => implementation (.inl request))
        (fun view => simulateQ (fun request => implementation (.inr request))
          (AdapterRegistrationWriterRequestExtraction.encodeInit
            (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) (initPacket view)).run)
        control inputs coins pin := by
  unfold begin
  rw [RegistrationNativePlatformBeaconPublication.begin_interpret]
  have crypto : (fun request => simulateQ implementation (cryptoLift (E := E) request)) =
      (fun request => implementation (.inl request)) := by
    funext request
    exact simulateQ_spec_query implementation (.inl request)
  rw [crypto]
  simp_rw [init_interpret]

theorem publication_interpret (implementation : QueryImpl (Spec E) m)
    (pending : registration.ServerResponseHash) :
    simulateQ implementation (publication E pending) =
      RegistrationNativePlatformServerPublication.program (fun request => implementation (.inl (.inl request)))
        (fun view => simulateQ (fun request => implementation (.inr request))
          (AdapterRegistrationWriterRequestExtraction.encodeResponse
            (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) (responsePacket view)).run) pending := by
  unfold publication
  rw [RegistrationNativePlatformServerPublication.program_interpret]
  have signing : (fun request => simulateQ implementation (signingLift (E := E) request)) =
      (fun request => implementation (.inl (.inl request))) := by
    funext request
    exact simulateQ_spec_query implementation (.inl (.inl request))
  rw [signing]
  simp_rw [response_interpret]

omit [Monad m] [LawfulMonad m] in
theorem init_joint {σ ι : Type} {base : OracleSpec.{0, 0} ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (view : registration.InitView) (before : σ) :
    (simulateQ implementation (init E view)).run before =
      (AdapterRegistrationStatefulWriter.init (fun request => implementation (.inr request))
        (initPacket view)).run before := by
  exact congrArg (fun work : StateT σ (OracleComp base) _ => work.run before) (init_interpret implementation view)

omit [Monad m] [LawfulMonad m] in
theorem response_joint {σ ι : Type} {base : OracleSpec.{0, 0} ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (view : registration.SignedResponseView) (before : σ) :
    (simulateQ implementation (response E view)).run before =
      (AdapterRegistrationStatefulWriter.response (fun request => implementation (.inr request))
        (responsePacket view)).run before := by
  exact congrArg (fun work : StateT σ (OracleComp base) _ => work.run before) (response_interpret implementation view)

omit [Monad m] [LawfulMonad m] in
/-- Every crypto call, allocation, mutable writer reply and later Init publication sees its predecessor's exact shared state. -/
theorem begin_joint {σ ι : Type} {base : OracleSpec.{0, 0} ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (before : σ) :
    (simulateQ implementation (begin E control inputs coins pin)).run before =
      (RegistrationNativePlatformBeaconPublication.begin (fun request => implementation (.inl request))
        (fun view => AdapterRegistrationStatefulWriter.init (fun request => implementation (.inr request))
          (initPacket view)) control inputs coins pin).run before := by
  exact congrArg (fun work : StateT σ (OracleComp base) _ => work.run before) (begin_interpret implementation control inputs coins pin)

omit [Monad m] [LawfulMonad m] in
/-- The response hash and signing history lead into the literal extracted stateful writer without restarting platform state. -/
theorem publication_joint {σ ι : Type} {base : OracleSpec.{0, 0} ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (pending : registration.ServerResponseHash) (before : σ) :
    (simulateQ implementation (publication E pending)).run before =
      (RegistrationNativePlatformServerPublication.program (fun request => implementation (.inl (.inl request)))
        (fun view => AdapterRegistrationStatefulWriter.response (fun request => implementation (.inr request))
          (responsePacket view)) pending).run before := by
  exact congrArg (fun work : StateT σ (OracleComp base) _ => work.run before) (publication_interpret implementation pending)
end BeaconcryptCore.Computational.RegistrationNativePlatformWriter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriter.init_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriter.init_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriter.response_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriter.response_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriter.init_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriter.init_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriter.response_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriter.response_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriter.begin_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriter.begin_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriter.publication_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriter.publication_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriter.init_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriter.init_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriter.response_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriter.response_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriter.begin_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriter.begin_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriter.publication_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriter.publication_joint
