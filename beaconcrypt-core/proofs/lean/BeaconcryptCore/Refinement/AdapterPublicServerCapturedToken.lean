-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementCapturedBinding
import BeaconcryptCore.Refinement.AdapterPublicServerAgreementReceipt
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! A returned actual source token contains the same completed agreement that emerged from its same captured source request tree. Binding preservation follows from the original Core invariant, independently of source primitive normality or a second global primitive model. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerCapturedToken
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementInterpreter (Capture)
open AdapterPublicServerAgreementReceipt (Receipt)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK PlatformState : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "NativeM" => StateT Native (StateT PlatformState ProbComp)

theorem record {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (rng nextRng : R)
    (effect : agreement.AgreementEffect) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (before after : Native) (previous next : PlatformState)
    (supported : ((.ok (.Some token, current, nextRng), after), next) ∈ support
      ((((AdapterPublicServerAcceptBody.record (m := NativeM) self rng effect).run).run before).run previous)) :
    ∃ completed, effect = .ServerComplete completed ∧ token.registration.agreement = completed ∧
      token.registration_id = completed.pending.registration_id.bytes := by
  cases effect <;> try { simp only [AdapterPublicServerAcceptBody.record, RustT.run_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq,
    reduceCtorEq, false_and] at supported }
  case ServerComplete completed =>
    rw [AdapterPublicServerToken.record] at supported
    simp only [RustT.run_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨⟨reply, middle⟩, between⟩, _called, continued⟩ := supported
    cases reply with
    | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, reduceCtorEq, false_and] at continued
    | ok pair =>
      rcases pair with ⟨inserted, history⟩
      simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
      have same := RustM.ok.inj (congrArg (fun value => value.1.1) continued)
      have tokenFields := AdapterPublicServerToken.result_token self rng completed inserted history token (congrArg Prod.fst same).symm
      exact ⟨completed, rfl, tokenFields⟩

theorem replay {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (receipt : Receipt R)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (current : beaconcrypt_public_wrapper.server.Server)
    (nextRng : R) (before after : Native) (previous next : PlatformState)
    (supported : ((.ok (.Some token, current, nextRng), after), next) ∈ support
      (((AdapterPublicServerAgreementReceipt.replay (n := n) (KemSK := KemSK) (source := mlSource)
        (m := StateT PlatformState ProbComp) self receipt).run before).run previous)) :
    ∃ completed journal capture, receipt = .ok ((.ok (.ServerComplete completed), journal), capture) ∧
      token.registration.agreement = completed ∧ token.registration_id = completed.pending.registration_id.bytes := by
  cases receipt with
  | fail error | div => simp only [AdapterPublicServerAgreementReceipt.replay, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | ok pair =>
    rcases pair with ⟨⟨effect, journal⟩, capture⟩
    simp only [AdapterPublicServerAgreementReceipt.replay, RustT.run_bind, RustT.run_liftRust,
      pure_bind] at supported
    cases effect with
    | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, reduceCtorEq, false_and] at supported
    | ok effect =>
      obtain ⟨completed, same, agreement, identifier⟩ := record self capture.rng nextRng effect token current before after previous next supported
      cases same
      exact ⟨completed, journal, capture, rfl, agreement, identifier⟩

variable [original : CryptoOperations (RustT ProbComp)]

theorem program {R E : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E) (keys : AdapterPublicAgreementFields.Keys)
    (self : beaconcrypt_public_wrapper.server.Server) (control : pqxdh.ServerState)
    (authenticated : registration.AuthenticatedInit) (rng nextRng : R)
    (receipt : Receipt R) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (before after : Native) (previous next : PlatformState)
    (supported : (((receipt, .ok (.Some token, current, nextRng)), after), next) ∈ support
      (((AdapterPublicServerAgreementReceipt.program coins generator keys self
        (RegistrationAgreementExecutor.server control .Fresh authenticated) rng).run before).run previous)) :
    token.registration.agreement.binding = authenticated.binding := by
  simp only [AdapterPublicServerAgreementReceipt.program, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨captured, middle⟩, between⟩, called, continued⟩ := supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
  obtain ⟨⟨⟨result, finalNative⟩, finalExternal⟩, replayed, returned⟩ := continued
  have wordEq := congrArg (fun value => value.1.1.2) returned
  have nativeEq := congrArg (fun value => value.1.2) returned
  have externalEq := congrArg Prod.snd returned
  change .ok (.Some token, current, nextRng) = result at wordEq
  change after = finalNative at nativeEq
  subst result
  subst finalNative
  cases externalEq
  obtain ⟨completed, journal, capture, same, agreement, _identifier⟩ := replay self captured token current nextRng middle after between next replayed
  rw [same] at called
  rw [agreement]
  exact AdapterPublicAgreementCapturedBinding.server coins generator keys rng control .Fresh authenticated completed journal capture before middle previous between called

end BeaconcryptCore.Refinement.AdapterPublicServerCapturedToken

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCapturedToken.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCapturedToken.record

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCapturedToken.replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCapturedToken.replay

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCapturedToken.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCapturedToken.program
