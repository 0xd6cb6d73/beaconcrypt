-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
/-! The actual corrected OPEN accept preserves the complete existing owner KEM pool on every outcome. The zero-other source syntax bill excludes private birth/service operations. Repeated pin/authentication hashes, real indexed encapsulation and the shared stateful reservation retain their literal effects, World counters and P poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceEffects (Extra Private)
open RegistrationNativePlatformServerOpenSyntax (Spec)
open RegistrationNativePlatformServerOpenSyntaxBounds (queryKind protocolKind)
open RegistrationNativePlatformPublicSourceAccept (actual syntaxActual)
variable {n : Nat} {ι KemSK Platform Value : Type} {base : OracleSpec ι}

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem interpreted_frame {A : Type} (work : StateT (Private n KemSK) ProbComp A)
    (before : Private n KemSK) (previous : Platform)
    (result : (A × Private n KemSK) × Platform)
    (frame : ∀ output ∈ support (work.run before), output.2.pool = before.pool)
    (supported : result ∈ support (((RegistrationNativePlatformInterpret.state RegistrationNativePlatformPublicSourceLocal.external work).run before).run previous)) :
    result.1.2.pool = before.pool := by
  change result ∈ support ((simulateQ RegistrationNativePlatformMldsaProgram.coins (work.run before)).run previous) at supported
  rw [RegistrationNativePlatformMldsaProgram.lift_coins, StateT.run_lift, bind_pure_comp, support_map] at supported
  obtain ⟨output, reached, rfl⟩ := supported
  exact frame output reached

private theorem effect_frame (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (before : Private n KemSK) (previous : Platform)
    (result : ((PqxdhRecordLiftInterface.EnvEffects n).Range query × Private n KemSK) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformInterpret.state RegistrationNativePlatformPublicSourceLocal.external
      (RegistrationNativeKemReferenceWorld.effect query)).run before).run previous)) : result.1.2.pool = before.pool := by
  apply interpreted_frame _ before previous result ?_ supported
  intro output reached
  change output ∈ support ((fun value => (value.1, { before with world := value.2 })) <$>
    (PqxdhRecordLiftWorld.effects query).run before.world) at reached
  rw [support_map] at reached
  obtain ⟨value, _, rfl⟩ := reached
  rfl

private theorem encapsulation_frame (setup : Setup base KemSK)
    (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp) (key : PqxdhKemIndCca.MlKem768PublicKey)
    (before : Private n KemSK) (previous : Platform)
    (result : ((RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Range (.inr (.inr key)) × Private n KemSK) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformInterpret.state RegistrationNativePlatformPublicSourceLocal.external
      (RegistrationNativeKemReferenceWorld.kem setup other (.inr (.inr key)))).run before).run previous)) : result.1.2.pool = before.pool := by
  apply interpreted_frame _ before previous result ?_ supported
  intro output reached
  rw [RegistrationNativeKemReferenceWorld.kem_encapsulation, support_map] at reached
  obtain ⟨value, _, rfl⟩ := reached
  rfl

/-- Every source-permitted actual leaf preserves the whole private owner pool, including the original reservation's arbitrary reached P. -/
theorem query_frame (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (reserve : StateT Platform ProbComp Bool)
    (query : (Spec n KemSK).Domain) (allowed : queryKind (n := n) (KemSK := KemSK) query ≠ .other)
    (before : Private n KemSK) (previous : Platform) (result : ((Spec n KemSK).Range query × Private n KemSK) × Platform)
    (supported : result ∈ support (((syntaxActual setup wire route sign seed scalar reserve query).run before).run previous)) :
    result.1.2.pool = before.pool := by
  cases query with
  | inr token =>
    cases token
    simp only [syntaxActual, StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
    obtain ⟨output, _, rfl⟩ := supported
    rfl
  | inl query =>
    cases query with
    | inl message =>
      simp only [syntaxActual, actual, RegistrationNativePlatformServerOpenKernel.handler,
        RegistrationNativePlatformPublicSourceAccept.actualCallbacks, RegistrationNativePlatformServerOpenSource.callbacks,
        RegistrationNativePlatformServerOpenSource.prepare, StateT.run, pure_apply, mem_support_pure_iff] at supported
      cases supported
      rfl
    | inr query =>
      cases query with
      | inl query =>
        cases query with
        | inl message => exact False.elim (allowed rfl)
        | inr query =>
          cases query with
          | inl publication => exact False.elim (allowed rfl)
          | inr effect => exact effect_frame effect before previous result supported
      | inr query =>
        cases query with
        | inl other => exact False.elim (allowed rfl)
        | inr query =>
          cases query with
          | inl pool => exact False.elim (allowed rfl)
          | inr key => exact encapsulation_frame setup _ key before previous result supported

/-- Every adaptive permitted actual source request tree preserves the same pool through its complete private/platform execution. -/
theorem program_frame (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (reserve : StateT Platform ProbComp Bool)
    (work : OracleComp (Spec n KemSK) Value)
    (allowed : work.AllQueriesSatisfy (fun query => queryKind (n := n) (KemSK := KemSK) query ≠ .other))
    (before : Private n KemSK) (previous : Platform) (result : (Value × Private n KemSK) × Platform)
    (supported : result ∈ support (((simulateQ (syntaxActual setup wire route sign seed scalar reserve) work).run before).run previous)) :
    result.1.2.pool = before.pool := by
  induction work using OracleComp.inductionOn generalizing before previous result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    rfl
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, first, last⟩ := supported
    exact (ih middle.1.1 (allowed.2 middle.1.1) middle.1.2 middle.2 result last).trans
      (query_frame setup wire route sign seed scalar reserve query allowed.1 before previous middle first)

/-- The zero-other bill of the literal corrected accept syntax discharges the permitted-request condition without a caller frame premise. -/
theorem syntax_pool (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment)
    (before : Private n KemSK) (previous : Platform)
    (result : ((((RustM (Option Nat) × RegistrationServerMaterialFrontend.State) × RegistrationServerReferenceCompiler.Environment) × Private n KemSK) × Platform))
    (supported : result ∈ support (((simulateQ (syntaxActual setup wire route sign seed scalar reserve)
      (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run front).run env)).run before).run previous)) :
    result.1.2.pool = before.pool := by
  apply program_frame setup wire route sign seed scalar reserve _ ?_ before previous result supported
  classical
  apply (isQueryBoundP_zero_iff _ (fun query => queryKind (n := n) (KemSK := KemSK) query ≠ .other)).mp
  simpa only [not_not, RegistrationNativePlatformServerOpenSyntaxBounds.cap] using RegistrationNativePlatformServerOpenSyntaxBounds.accept_bound (n := n) setup checks verify .other packet front env

/-- The actual corrected OpenControl accept, including all failed prefixes and shared reservation effects, retains the entire owner private pool. -/
theorem accept_pool (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment)
    (before : Private n KemSK) (previous : Platform)
    (result : ((((RustM (Option Nat) × RegistrationServerMaterialFrontend.State) × RegistrationServerReferenceCompiler.Environment) × Private n KemSK) × Platform))
    (supported : result ∈ support (((((RegistrationNativePlatformServerOpenControl.accept
      (actual (n := n) setup wire route sign seed scalar) (StateT.lift reserve) setup checks verify packet).run front).run env).run before).run previous)) :
    result.1.2.pool = before.pool := by
  have equation := congrArg (fun work => ((work.run front).run env))
    (RegistrationNativePlatformServerOpenSyntax.accept_source (syntaxActual (n := n) setup wire route sign seed scalar reserve) setup checks verify packet)
  change simulateQ (syntaxActual setup wire route sign seed scalar reserve)
    (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run front).run env) =
    (((RegistrationNativePlatformServerOpenControl.accept (actual setup wire route sign seed scalar)
      (StateT.lift reserve) setup checks verify packet).run front).run env) at equation
  rw [← equation] at supported
  exact syntax_pool setup wire checks route sign seed scalar reserve verify packet front env before previous result supported
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- Closing the actual source accept into the existing public/environment/private layout retains the same full private pool on every result. -/
theorem close_pool (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : RegistrationNativePlatformServerOpenControl.State n KemSK Extra) (previous : Platform)
    (result : (RustM (Option Nat) × RegistrationNativePlatformServerOpenControl.State n KemSK Extra) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformServerOpenControl.close
      (RegistrationNativePlatformServerOpenControl.accept (actual setup wire route sign seed scalar) (StateT.lift reserve)
        setup checks verify packet)).run before).run previous)) :
    result.1.2.2.2.pool = before.2.2.pool := by
  simp only [RegistrationNativePlatformServerOpenControl.close,
    RegistrationNativePlatformServerOpenKernel.closeEnvironment, StateT.run, map_apply,
    Functor.map_map] at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact accept_pool setup wire checks route sign seed scalar reserve verify packet before.1 before.2.1 before.2.2 previous inner reached

end BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool.query_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool.query_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool.program_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool.program_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool.syntax_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool.syntax_pool

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool.accept_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool.accept_pool

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool.close_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool.close_pool
