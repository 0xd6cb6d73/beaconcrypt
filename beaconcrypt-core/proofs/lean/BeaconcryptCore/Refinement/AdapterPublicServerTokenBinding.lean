-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCapturedToken
import BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The complete actual source reservation/lookup suffix retains the original authenticated binding in every returned token. No allocation-success, primitive-normality or whole source-controller premise is needed: each conclusion is drawn from its actual supported returned capability and the same captured request tree. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerTokenBinding
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerReservationReceipt (Receipt)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK PlatformState : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "NativeM" => StateT Native (StateT PlatformState ProbComp)

theorem reserved {R E : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E) (self : beaconcrypt_public_wrapper.server.Server)
    (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit) (rng nextRng : R)
    (receipt : Receipt R) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (before after : Native) (previous next : PlatformState)
    (supported : (((receipt, .ok (.Some token, current, nextRng)), after), next) ∈ support
      (((AdapterPublicServerReservationReceipt.program coins generator self control authenticated rng).run before).run previous)) :
    token.registration.agreement.binding = authenticated.binding := by
  simp only [AdapterPublicServerReservationReceipt.program, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨allocated, middle⟩, between⟩, _called, continued⟩ := supported
  cases allocated with
  | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, and_false, false_and] at continued
  | ok pair =>
    rcases pair with ⟨allocation, history⟩
    cases allocation with
    | Err error => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        RustM.ok.injEq, reduceCtorEq, and_false, false_and] at continued
    | Ok allocatedUnit =>
      simp only [StateT.run_map, support_map] at continued
      obtain ⟨⟨⟨⟨captured, result⟩, currentNative⟩, currentExternal⟩, called, returned⟩ := continued
      have wordEq := congrArg (fun value => value.1.1.2) returned
      have nativeEq := congrArg (fun value => value.1.2) returned
      have externalEq := congrArg Prod.snd returned
      change result = .ok (.Some token, current, nextRng) at wordEq
      change currentNative = after at nativeEq
      subst result
      subst currentNative
      cases externalEq
      exact AdapterPublicServerCapturedToken.program coins generator
        (AdapterPublicAgreementServerNative.keys (platform.arcView self.identity).identity_key.secret_key)
        {self with consumed_registrations := history} control authenticated rng nextRng captured token current middle after between next called

theorem lookup {R E : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E) (self : beaconcrypt_public_wrapper.server.Server)
    (pending : peer.RegistrationLookup) (rng nextRng : R)
    (receipt : Receipt R) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (before after : Native) (previous next : PlatformState)
    (supported : (((receipt, .ok (.Some token, current, nextRng)), after), next) ∈ support
      (((AdapterPublicServerLookupReceipt.program coins generator self pending rng).run before).run previous)) :
    token.registration.agreement.binding = pending.authenticated.binding := by
  simp only [AdapterPublicServerLookupReceipt.program, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨observed, middle⟩, between⟩, _called, continued⟩ := supported
  cases observed with
  | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, and_false, false_and] at continued
  | ok present => cases present with
    | true => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        RustM.ok.injEq, reduceCtorEq, and_false, false_and] at continued
    | false => exact reserved coins generator self pending.control pending.authenticated rng nextRng receipt token current middle after between next continued

end BeaconcryptCore.Refinement.AdapterPublicServerTokenBinding

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerTokenBinding.reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerTokenBinding.reserved

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerTokenBinding.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerTokenBinding.lookup
