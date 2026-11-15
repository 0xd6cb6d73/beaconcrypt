-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperChildren
/-! The actual extracted Init and response authentication children compose with native primitive interpretation in the same shared monad. Init retains distinct Ed parse and attached-opening calls, including parse Err and absent opening. Response selects only hash and ML verification and ignores unrelated Ed operations. No codec, authentication-success or security conclusion is a premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
variable [ed : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m] {E : Type}

/-- The two Ed leaves retain their actual parse/open Rust replies; response authentication never selects them. -/
def authentication (native : QueryImpl RegistrationAuthenticationExecutor.Spec m)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8)))) :
    QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec m
  | .hash request => RustM.ok <$> native (.hash request)
  | .verifyResponseMldsa request => RustM.ok <$> native (.mldsa request)
  | .parseEd bytes => parseEd bytes
  | .verifyEd signed publicKey => verifyEd signed publicKey

theorem response_queries (native : QueryImpl RegistrationAuthenticationExecutor.Spec m)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8)))) :
    AdapterPublicWrapperChildren.response (authentication native parseEd verifyEd) =
      native ∘ₛ AdapterAuthenticationStatefulResponse.native := by
  funext query
  cases query <;> simp only [AdapterPublicWrapperChildren.response, authentication,
    QueryImpl.apply_compose, AdapterAuthenticationStatefulResponse.native, simulateQ_map, simulateQ_spec_query]

/-- Actual extracted response authentication and the selected native verifier/hash share the complete original monad. -/
theorem response (native : QueryImpl RegistrationAuthenticationExecutor.Spec m)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :
    ((AdapterPublicWrapperChildren.children (authentication native parseEd verifyEd) recording writer).authenticateResponse pending packet).run =
      simulateQ native (RegistrationResponseExecutor.begin pending packet) := by
  rw [AdapterPublicWrapperChildren.response_run, response_queries, QueryImpl.simulateQ_compose]
  exact congrArg (simulateQ native) (AdapterAuthenticationStatefulResponse.source pending packet)

/-- Each actual source authentication leaf is interpreted separately, including both Ed operations. -/
def normalAuthentication (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec m) :
    QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec m
  | .hash request => .ok <$> native (.inl (.hash request))
  | .verifyResponseMldsa request => .ok <$> native (.inl (.mldsa request))
  | .parseEd bytes => .ok <$> native (.inr (.parse bytes))
  | .verifyEd signed publicKey => .ok <$> native (.inr (.open signed publicKey))

theorem init_queries (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec m) :
    AdapterPublicWrapperChildren.initQueries (normalAuthentication native) =
      native ∘ₛ AdapterInitAuthenticationStateful.native := by
  funext request
  cases request <;> simp only [AdapterPublicWrapperChildren.initQueries, normalAuthentication,
    QueryImpl.apply_compose, AdapterInitAuthenticationStateful.native, simulateQ_map, simulateQ_spec_query]

/-- The full extracted Init authentication child compiles to the native authentication controller with the literal Ed parse/open sequence. -/
theorem init (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec m)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    ((AdapterPublicWrapperChildren.children (normalAuthentication native) recording writer).authenticateInit pin packet).run =
      AdapterInitAuthenticationDriver.observe <$>
        simulateQ (native ∘ₛ AdapterInitAuthenticationStateful.abstractNative)
          (RegistrationAuthenticationExecutor.begin pin packet) := by
  rw [AdapterPublicWrapperChildren.init_run, init_queries, QueryImpl.simulateQ_compose,
    AdapterInitAuthenticationSourceLoop.program_authenticate]
  change simulateQ native (AdapterInitAuthenticationStateful.interpret (AdapterInitAuthenticationDriver.authenticate pin packet)) = _
  rw [AdapterInitAuthenticationDriver.source, simulateQ_map, QueryImpl.simulateQ_compose]

end BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative.init_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative.init_queries
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative.response_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative.response_queries

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative.response

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative.init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative.init
