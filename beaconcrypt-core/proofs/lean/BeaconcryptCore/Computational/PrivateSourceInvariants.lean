import BeaconcryptCore.Computational.PqxdhPrivateSourceCoins

/-!
These invariants concern supported complete executions of the distinct protocol-private/public source interface from arbitrary prior state. The compiler's full public-log restoration is retained; only already-proved signing-message and existing seed-index facts are extracted. Other requests, callback effects, later creations and actual reveals still execute. There is no whole-state invariance, source coin disclosure, key injectivity, secrecy, native ownership or cryptographic security claim.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PrivateSourceInvariants
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting PqxdhDynamicIdentityReports
open PqxdhJointPhase1Reports PqxdhPhase1AcceptanceOracle PqxdhJointPhase1AcceptanceComposition
open PqxdhPrivateSourceCoins

/-- A zero-signing private/public source schedule preserves every actual prior signing message while all other effects and public logging still execute. -/
theorem private_run_noSign (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (index : Fin count) {Result : Type}
    (client : OracleComp PrivateSourceSpec Result)
    (noSign : client.IsQueryBoundP (fun query => IsSigning (translated query)) 0)
    (state : BareState count) (result : Result × BareState count)
    (supported : result ∈ support ((simulateQ (privateImpl attachedVerify primitives count) client).run state)) :
    signedMessages (result.2.1.histories index) = signedMessages (state.1.histories index) := by
  change result ∈ support ((simulateQ (privateImpl attachedVerify primitives count) client).run
    (restoreState state state.2.transcript)) at supported
  rw [← compile_complete attachedVerify primitives count client state state.2.transcript] at supported
  obtain ⟨compiled, hcompiled, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  exact bare_run_noSign attachedVerify primitives count index
    ((simulateQ compile client).run state.2.transcript)
    (compile_bound client IsSigning 0 noSign state.2.transcript) state compiled hcompiled

/-- Every already-created seed remains at its original index through arbitrary private coins, public services, later creation, acceptance and reveals. -/
theorem private_run_created (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count index : Nat) (seed : IdentitySeed) {Result : Type}
    (client : OracleComp PrivateSourceSpec Result) (state : BareState count)
    (created : state.2.seeds[index]? = some seed) (result : Result × BareState count)
    (supported : result ∈ support ((simulateQ (privateImpl attachedVerify primitives count) client).run state)) :
    result.2.2.seeds[index]? = some seed := by
  change result ∈ support ((simulateQ (privateImpl attachedVerify primitives count) client).run
    (restoreState state state.2.transcript)) at supported
  rw [← compile_complete attachedVerify primitives count client state state.2.transcript] at supported
  obtain ⟨compiled, hcompiled, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  exact bare_run_created attachedVerify primitives count index seed
    ((simulateQ compile client).run state.2.transcript) state created compiled hcompiled

end BeaconcryptCore.Computational.PrivateSourceInvariants

/--
info: 'BeaconcryptCore.Computational.PrivateSourceInvariants.private_run_noSign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PrivateSourceInvariants.private_run_noSign

/--
info: 'BeaconcryptCore.Computational.PrivateSourceInvariants.private_run_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PrivateSourceInvariants.private_run_created
