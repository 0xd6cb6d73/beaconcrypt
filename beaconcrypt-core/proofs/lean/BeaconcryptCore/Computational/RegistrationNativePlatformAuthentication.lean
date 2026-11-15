-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperChildren
import BeaconcryptCore.Computational.RegistrationWorldAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformInterpret

/-! Concrete shared-World interpretation of the actual two Ed leaves and the actual Init/response authentication programs. The Ed contracts concern only primitive parsing/public-byte views and attached opening; no native acceptance or protocol-security event appears in them. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m]

structure EdFunctional (crypto : Pqxdh.Crypto) where
  parse : Slice U8 → core.result.Result ed.PublicKey ed.Error
  publicKey : ed.PublicKey → Std.Array U8 32#usize
  parseRun : ∀ input, ed.parse input = .ok (parse input)
  parseKey : ∀ input key, parse input = .Ok key →
    TranscriptAuthParts.absSlice input = PqxdhRefinement.absBytes (publicKey key)
  parseError : ∀ input error, parse input = .Err error → ∀ signed,
    crypto.verify (TranscriptAuthParts.absSlice input) (TranscriptAuthParts.absSlice signed) = none
  verifyRun : ∀ signed key, ed.verify signed key = .ok
    (RegistrationAuthenticationShared.verifyEd25519 crypto ⟨publicKey key, signed⟩)

noncomputable def core (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (StateT (PqxdhRecordLiftWorld.State n) m) :=
  fun query before => simulateQ coins ((RegistrationWorldAuthentication.implementation setup codec route verify query).run before)

noncomputable def native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) (edLaws : EdFunctional setup.source.crypto) :
    QueryImpl AdapterInitAuthenticationStateful.NativeSpec (StateT (PqxdhRecordLiftWorld.State n) m)
  | .inl query => core coins setup codec route verify query
  | .inr (.parse input) => pure (edLaws.parse input)
  | .inr (.open signed key) => pure (RegistrationAuthenticationShared.verifyEd25519 setup.source.crypto ⟨edLaws.publicKey key, signed⟩)

noncomputable def source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec (StateT (PqxdhRecordLiftWorld.State n) m)
  | .hash request => .ok <$> core coins setup codec route verify (.hash request)
  | .verifyResponseMldsa request => .ok <$> core coins setup codec route verify (.mldsa request)
  | .parseEd input => pure (ed.parse input)
  | .verifyEd signed key => pure (ed.verify signed key)

variable [LawfulMonad m]
theorem opened (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) (edLaws : EdFunctional setup.source.crypto)
    (request : registration.Ed25519VerificationRequest) :
    simulateQ (native (n := n) coins setup codec route verify edLaws) (AdapterInitAuthenticationStateful.opened request) =
      pure (RegistrationAuthenticationShared.verifyEd25519 setup.source.crypto request) := by
  simp only [AdapterInitAuthenticationStateful.opened, simulateQ_bind, simulateQ_spec_query, native, pure_bind]
  cases parsed : edLaws.parse (Std.Array.to_slice request.public_key) with
  | Err error =>
      have rejected := edLaws.parseError (Std.Array.to_slice request.public_key) error parsed request.signed
      change setup.source.crypto.verify (PqxdhRefinement.absBytes request.public_key)
        (TranscriptAuthParts.absSlice request.signed) = none at rejected
      simp only [simulateQ_pure, RegistrationAuthenticationShared.verifyEd25519, rejected,
        RegistrationAuthenticationShared.openedBytes]
  | Ok key =>
      have bytes := edLaws.parseKey (Std.Array.to_slice request.public_key) key parsed
      simp only [simulateQ_spec_query, native]
      unfold RegistrationAuthenticationShared.verifyEd25519
      rw [← bytes]
      rfl

theorem source_query (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) (edLaws : EdFunctional setup.source.crypto)
    (query : AdapterInitAuthenticationRequestMonad.Spec.Domain) :
    AdapterPublicWrapperChildren.initQueries (source (n := n) coins setup codec route verify) query =
      (native coins setup codec route verify edLaws ∘ₛ AdapterInitAuthenticationStateful.native) query := by
  cases query <;> simp only [AdapterPublicWrapperChildren.initQueries, source, QueryImpl.apply_compose, AdapterInitAuthenticationStateful.native,
    simulateQ_map, simulateQ_spec_query, native, map_pure]
  · rw [edLaws.parseRun]
  · rw [edLaws.verifyRun]

omit ed [LawfulMonad m] in
private theorem core_ed (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (request : registration.Ed25519VerificationRequest) :
    core (n := n) coins setup codec route verify (.ed25519 request) =
      pure (RegistrationAuthenticationShared.verifyEd25519 setup.source.crypto request) := by
  funext before
  simp only [core, RegistrationWorldAuthentication.implementation, QueryImpl.apply_compose,
    RegistrationWorldAuthentication.callbacks, simulateQ_pure, StateT.run_pure]
  rfl

theorem abstract_query (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) (edLaws : EdFunctional setup.source.crypto)
    (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    (native (n := n) coins setup codec route verify edLaws ∘ₛ AdapterInitAuthenticationStateful.abstractNative) query =
      core coins setup codec route verify query := by
  cases query with
  | hash request | mldsa request =>
      simp only [QueryImpl.apply_compose, AdapterInitAuthenticationStateful.abstractNative, simulateQ_spec_query, native]
  | ed25519 request =>
      rw [QueryImpl.apply_compose, AdapterInitAuthenticationStateful.abstractNative,
        opened coins setup codec route verify edLaws request, core_ed]

attribute [local irreducible] AdapterInitAuthenticationSourceLoop.authenticate AdapterInitAuthenticationDriver.authenticate
  RegistrationAuthenticationExecutor.begin

theorem init_source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) (edLaws : EdFunctional setup.source.crypto)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    simulateQ (AdapterPublicWrapperChildren.initQueries (source (n := n) coins setup codec route verify))
      (AdapterInitAuthenticationSourceLoop.authenticate (m := AdapterInitAuthenticationRequestMonad.Program) pin packet).run =
      AdapterInitAuthenticationDriver.observe <$>
        simulateQ (core coins setup codec route verify) (RegistrationAuthenticationExecutor.begin pin packet) := by
  rw [AdapterInitAuthenticationSourceLoop.program_authenticate]
  have actual : AdapterPublicWrapperChildren.initQueries (source (n := n) coins setup codec route verify) =
      native coins setup codec route verify edLaws ∘ₛ AdapterInitAuthenticationStateful.native := by
    funext query
    exact source_query coins setup codec route verify edLaws query
  rw [actual, QueryImpl.simulateQ_compose]
  change simulateQ (native coins setup codec route verify edLaws)
    (AdapterInitAuthenticationStateful.interpret (AdapterInitAuthenticationDriver.authenticate pin packet)) = _
  rw [AdapterInitAuthenticationDriver.source, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have shared : native (n := n) coins setup codec route verify edLaws ∘ₛ AdapterInitAuthenticationStateful.abstractNative =
      core coins setup codec route verify := by
    funext query
    exact abstract_query coins setup codec route verify edLaws query
  rw [shared]

theorem response_source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :
    simulateQ (AdapterPublicWrapperChildren.response (source (n := n) coins setup codec route verify))
      (AdapterAuthenticationRequestExtraction.authenticate (m := AdapterAuthenticationRequestMonad.Program) pending packet).run =
      simulateQ (core coins setup codec route verify) (RegistrationResponseExecutor.begin pending packet) := by
  have actual : AdapterPublicWrapperChildren.response (source (n := n) coins setup codec route verify) =
      core coins setup codec route verify ∘ₛ AdapterAuthenticationStatefulResponse.native := by
    funext query
    cases query <;> simp only [AdapterPublicWrapperChildren.response, source, QueryImpl.apply_compose,
      AdapterAuthenticationStatefulResponse.native, simulateQ_map, simulateQ_spec_query]
  rw [actual, QueryImpl.simulateQ_compose]
  change simulateQ (core coins setup codec route verify)
    (AdapterAuthenticationStatefulResponse.authenticate pending packet) = _
  rw [AdapterAuthenticationStatefulResponse.source]

omit ed in
private theorem core_program {Value : Type} (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ (core coins setup codec route verify) work).run before =
      simulateQ coins ((simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify) work).run before) :=
  (congrFun (RegistrationNativePlatformInterpret.state_simulate coins
    (RegistrationWorldAuthentication.implementation setup codec route verify) work) before).symm

theorem init_world (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) (edLaws : EdFunctional setup.source.crypto)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ (AdapterPublicWrapperChildren.initQueries (source coins setup codec route verify))
      (AdapterInitAuthenticationSourceLoop.authenticate (m := AdapterInitAuthenticationRequestMonad.Program) pin packet).run).run before =
      (fun result => (AdapterInitAuthenticationDriver.observe result.1, result.2)) <$>
        simulateQ coins ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before) := by
  rw [init_source coins setup codec route verify edLaws pin packet, StateT.run_map,
    core_program coins setup codec route verify]
  have same : RegistrationWorldAuthentication.begin (n := n) setup codec route verify pin packet =
      simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify)
        (RegistrationAuthenticationExecutor.begin pin packet) := by
    unfold RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program RegistrationWorldAuthentication.implementation
    exact (QueryImpl.simulateQ_compose _ _ _).symm
  rw [same]

theorem response_world (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ (AdapterPublicWrapperChildren.response (source coins setup codec route verify))
      (AdapterAuthenticationRequestExtraction.authenticate (m := AdapterAuthenticationRequestMonad.Program) pending packet).run).run before =
      simulateQ coins ((simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify)
        (RegistrationResponseExecutor.begin pending packet)).run before) := by
  rw [response_source, core_program]

end BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.opened' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.opened

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.source_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.source_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.abstract_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.abstract_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.init_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.init_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.response_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.response_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.init_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.init_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.response_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication.response_world
