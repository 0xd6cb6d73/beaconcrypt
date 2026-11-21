-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
import BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop
import BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse
import BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter

/-! Actual child source request bodies interpret in the same parent native/platform monad. Init and response authentication share the same hash callback. Only response authentication uses the parent ML verification callback. Registration writers expand their checked source request programs. Rust failure/divergence and all shared poststates remain under RustT. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperChildren
open AdapterPublicWrapperRustT (RustT)
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] {E : Type}

/-- Parent capability dictionary: the ML verification leaf is used only by Server response authentication. The actual Init request specification contains only hash and Ed parse/open leaves. -/
inductive AuthenticationRequest where
  | hash (request : registration.HashRequest)
  | parseEd (input : Slice U8)
  | verifyEd (signed : Slice U8) (publicKey : primitive.PublicKey)
  | verifyResponseMldsa (request : registration.MldsaVerificationRequest)

abbrev AuthenticationResponse : AuthenticationRequest → Type
  | .hash _ => core.option.Option (Std.Array U8 64#usize)
  | .parseEd _ => core.result.Result primitive.PublicKey primitive.Error
  | .verifyEd _ _ => core.option.Option (alloc.vec.Vec U8)
  | .verifyResponseMldsa _ => Bool

abbrev AuthenticationSpec : OracleSpec AuthenticationRequest := fun request => RustM (AuthenticationResponse request)

def initQueries (authentication : QueryImpl AuthenticationSpec m) :
    QueryImpl AdapterInitAuthenticationRequestMonad.Spec m
  | .hash request => authentication (.hash request)
  | .parseEd input => authentication (.parseEd input)
  | .verifyEd signed publicKey => authentication (.verifyEd signed publicKey)

def response (authentication : QueryImpl AuthenticationSpec m) :
    QueryImpl AdapterAuthenticationRequestMonad.Spec m
  | .hash request => authentication (.hash request)
  | .verify request => authentication (.verifyResponseMldsa request)

@[instance_reducible] def children (authentication : QueryImpl AuthenticationSpec m)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) :
    AdapterPublicWrapperRequestMonad.ChildOperations (RustT m) where
  executeHash request := ⟨authentication (.hash request)⟩
  authenticateInit pin packet := ⟨simulateQ (initQueries authentication)
    (AdapterInitAuthenticationSourceLoop.authenticate (m := AdapterInitAuthenticationRequestMonad.Program) pin packet).run⟩
  authenticateResponse pending packet := ⟨simulateQ (response authentication)
    (AdapterAuthenticationRequestExtraction.authenticate (m := AdapterAuthenticationRequestMonad.Program) pending packet).run⟩
  commitmentHash transcript := ⟨recording (.hash transcript)⟩
  openRequest request := ⟨recording (.aead request)⟩
  ratchetHkdf request := ⟨recording (.kdf request)⟩
  compare left right := ⟨recording (.compare left right)⟩
  encodeInit packet := ⟨simulateQ writer
    (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) packet).run⟩
  encodeResponse packet := ⟨simulateQ writer
    (AdapterRegistrationWriterRequestExtraction.encodeResponse (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) packet).run⟩

attribute [local irreducible] AdapterInitAuthenticationSourceLoop.authenticate

theorem init_run (authentication : QueryImpl AuthenticationSpec m)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    ((children authentication recording writer).authenticateInit pin packet).run =
      simulateQ (initQueries authentication)
        (AdapterInitAuthenticationSourceLoop.authenticate (m := AdapterInitAuthenticationRequestMonad.Program) pin packet).run := rfl

theorem response_run (authentication : QueryImpl AuthenticationSpec m)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :
    ((children authentication recording writer).authenticateResponse pending packet).run =
      simulateQ (response authentication)
        (AdapterAuthenticationRequestExtraction.authenticate (m := AdapterAuthenticationRequestMonad.Program) pending packet).run := rfl

theorem init_writer_run (authentication : QueryImpl AuthenticationSpec m)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (packet : beaconcrypt_parse.transport.initkex) :
    ((children authentication recording writer).encodeInit packet).run =
      simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) packet).run := rfl

theorem response_writer_run (authentication : QueryImpl AuthenticationSpec m)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (packet : beaconcrypt_parse.transport.kexresponse) :
    ((children authentication recording writer).encodeResponse packet).run =
      simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeResponse
        (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) packet).run := rfl

theorem same_hash (authentication : QueryImpl AuthenticationSpec m)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) (request : registration.HashRequest) :
    response authentication (.hash request) = ((children authentication recording writer).executeHash request).run := rfl

omit [Monad m] in
theorem same_verification (authentication : QueryImpl AuthenticationSpec m)
    (request : registration.MldsaVerificationRequest) :
    response authentication (.verify request) = authentication (.verifyResponseMldsa request) := rfl

end BeaconcryptCore.Refinement.AdapterPublicWrapperChildren

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.init_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.init_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.response_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.response_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.init_writer_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.init_writer_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.response_writer_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.response_writer_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.same_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.same_hash

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.same_verification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperChildren.same_verification
