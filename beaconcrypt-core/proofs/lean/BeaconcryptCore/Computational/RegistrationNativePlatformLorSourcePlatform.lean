-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
/-! The actual common-platform envelope preserves the granular source KEM contract query by query. Its public reservation uses only the literal coin embedding, so the private KEM state is retained on every failed or successful allocator outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform
open RegistrationNativeSecretWordInterface (Spec LocalSpec liftLocal)
open RegistrationNativePlatformLorIdealStateLift (interpret)
open RegistrationNativePlatformLorSourceKem (Contract)
variable {n : Nat} {KemSK Platform Private A : Type}
variable (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
noncomputable def extend : QueryImpl (Spec n KemSK) (StateT (Platform × Private) ProbComp) :=
  fun query before => (fun result => (result.1,(before.1,result.2))) <$> (implementation query).run before.2

private theorem extend_run (query : (Spec n KemSK).Domain) (before : Platform × Private) :
    (extend implementation query).run before =
      (fun result => (result.1,(before.1,result.2))) <$> (implementation query).run before.2 := rfl

private theorem program (work : OracleComp (Spec n KemSK) A) (previous : Platform) (before : Private) :
    (simulateQ (extend implementation) work).run (previous,before) =
      (fun result => (result.1,(previous,result.2))) <$> (simulateQ implementation work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,extend_run,map_bind,bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1 result.2

/-- Literal local source requests retain the actual public platform coordinate in the same persistent interpretation. -/
theorem local_source (routed : Bool) :
    (fun query => interpret implementation (RegistrationNativePlatformSecretWordFrontendView.wordLocal (Platform := Platform) routed query)) =
      extend implementation ∘ₛ liftLocal routed := by
  funext query
  apply StateT.ext
  rintro ⟨previous,before⟩
  rw [QueryImpl.apply_compose,program]
  exact RegistrationNativePlatformLorIdealStateLift.lifted implementation (liftLocal routed query) previous before

variable (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (provider : QueryImpl (RegistrationNativeSecretWordKemInterface.Routed KemSK)
      (StateT (RegistrationNativeSecretWordKemProvider.State KemSK) ProbComp))
    (contract : Contract implementation kem input provider)
include contract

/-- Extending only the public platform coordinate derives the same individual preparation, routed and quiet KEM receipts. -/
theorem lifted_contract : Contract (extend (Platform := Platform) implementation) (fun current => kem current.2) input provider := by
  constructor
  · intro message before result supported
    simp only [extend_run,support_map] at supported
    obtain ⟨reached,called,rfl⟩ := supported
    exact contract.prepare message before.2 reached called
  · intro query before result supported
    simp only [extend_run,support_map] at supported
    obtain ⟨reached,called,rfl⟩ := supported
    exact contract.routed query before.2 reached called
  · intro query quiet before result supported
    simp only [extend_run,support_map] at supported
    obtain ⟨reached,called,rfl⟩ := supported
    exact contract.quiet query quiet before.2 reached called

private theorem coins_kem (work : ProbComp A) (before : Private) (result : A × Private)
    (supported : result ∈ support ((simulateQ implementation
      (simulateQ (fun coin => RegistrationNativeSecretWordFrontend.effect (.inl coin)) work)).run before)) :
    kem result.2=kem before := by
  rw [←QueryImpl.simulateQ_compose] at supported
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    rfl
  | query_bind query next ih =>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    have unchanged := contract.quiet (.inl (.inr (.inl (.inr (.inr (.inl query)))))) trivial before middle
      (by simpa only [QueryImpl.apply_compose,RegistrationNativeSecretWordFrontend.effect,simulateQ_spec_query] using called)
    exact (ih middle.1 middle.2 result continued).trans unchanged

/-- Every actual reservation outcome preserves the full private KEM row/marker while keeping its reached platform state. -/
theorem reservation_kem (reserve : StateT Platform ProbComp A) (before : Platform × Private)
    (result : A × (Platform × Private))
    (supported : result ∈ support ((interpret implementation (RegistrationNativePlatformSecretWordOrdinary.platform reserve)).run before)) :
    kem result.2.2=kem before.2 := by
  rw [RegistrationNativePlatformLorIdealStateLift.run,support_map] at supported
  obtain ⟨reached,called,rfl⟩ := supported
  exact coins_kem implementation kem input provider contract (reserve.run before.1) before.2 reached called

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform.local_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform.local_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform.lifted_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform.lifted_contract

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform.reservation_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform.reservation_kem
