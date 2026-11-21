-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationShared

/-! The current Init's first callback hashes its exact request. It makes no Beacon ML verification or fingerprint query. The historical credential-gate and forgery statements are retired. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationInitGateExecutor
open CtxRomAuth RegistrationAuthenticationExecutor
open BeaconcryptCore.Refinement.RegistrationAuthentication
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow (Event)

/-- The actual first step uses the shared cache and the request's complete preimage. -/
theorem hash_step {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (before : registration.InitHash) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
      (step (.HashRequested before))).run state =
      (fun hashed =>
        (edge (.hash (.Some (RegistrationAuthenticationShared.digestArray hashed.1)))
          (before.resume (.Some (RegistrationAuthenticationShared.digestArray hashed.1))),
          (state.1, hashed.2))) <$>
        (ctxRandomOracle ((), absBytes before.input)).run state.2 := by
  obtain ⟨request, requested, bytes⟩ := init_hash_request before
  simp only [step, requested, continueWith, simulateQ_spec_query, bind_pure_comp,
    simulateQ_map, StateT.run_map]
  rw [RegistrationAuthenticationShared.hash_exact, bytes]
  simp only [Functor.map_map]

/-- Every reached first callback supplies its actual hash reply and a cache receipt, including rejection. -/
theorem hash_edge_receipt {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (before : registration.InitHash) (state after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (event : Event) (next : registration.InitAuthentication)
    (supported : (.ok (some (event, next)), after) ∈ support
      ((simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
        (step (.HashRequested before))).run state)) :
    ∃ digest, event = .hash (.Some (RegistrationAuthenticationShared.digestArray digest)) ∧
      state.2 ≤ after.2 ∧ after.2 ((), absBytes before.input) = some digest := by
  rw [hash_step, support_map] at supported
  obtain ⟨⟨digest, cache⟩, queried, same⟩ := supported
  have afterSame : (state.1, cache) = after := congrArg Prod.snd same
  have eventSame := (edge_success _ _ event next (congrArg Prod.fst same)).1.symm
  have cached := MldsaSharedAuthentication.query_cached (absBytes before.input) state.2 (digest, cache) queried
  exact ⟨digest, eventSame, by simpa only [← afterSame] using cached.1,
    by simpa only [← afterSame] using cached.2⟩

end BeaconcryptCore.Computational.RegistrationInitGateExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationInitGateExecutor.hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitGateExecutor.hash_step

/-- info: 'BeaconcryptCore.Computational.RegistrationInitGateExecutor.hash_edge_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitGateExecutor.hash_edge_receipt
