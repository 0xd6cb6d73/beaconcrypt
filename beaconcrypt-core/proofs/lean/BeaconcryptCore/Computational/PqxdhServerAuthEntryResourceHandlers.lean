import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceServices
import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourcePotential

open OracleComp OracleSpec
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhJointGapDh
open PqxdhServerAuthSourceCosts PqxdhServerAuthTailCosts PqxdhServerAuthPendingBudget
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response τ : Type}

/-- Every accept attempt pays the real scalar/KEM prefix and at most one table read, without requiring successful admission. -/
theorem accept_step_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (services : Services Response τ) (serviceBound : ServiceUniform services)
    (caps : KemCaps) (bounded : KemBound setup caps) (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) :
    ((acceptStep setup codec checks publicValue services raw).run state).IsTotalQueryBound (32 + caps.encapsCost + 64) := by
  unfold acceptStep
  simp only [StateT.run]
  apply isTotalQueryBound_bind (n₂ := 64) (server_prefix_uniform setup codec checks caps bounded raw state.1.server.consumed)
  rintro ⟨(_ | input), consumed⟩
  · trivial
  · dsimp only
    split_ifs
    · rw [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      exact serviceBound.derive _ state.2.2
    · trivial

/-- A pending token pays the full real or selected build; consumed and absent tokens invoke no callback. -/
theorem build_step_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (services : Services Response τ) (serviceBound : ServiceUniform services)
    (index : Nat) (payload : Option Pqxdh.Bytes) (state : FlatState KemSK τ) :
    ((buildStep setup codec checks services index payload).run state).IsTotalQueryBound
      (64 * slotWeight (state.1.pending index)) := by
  unfold buildStep
  simp only [StateT.run]
  cases token : state.1.pending index with
  | none => trivial
  | some pending =>
      simp only [slotWeight, Nat.mul_one, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      split_ifs
      · exact serviceBound.build pending payload state.1.server ([], state.1.ctx)
      · exact build_uniform setup codec checks pending.pending pending.root payload state.1.server ([], state.1.ctx)

/-- Only the active original finish phase pays decapsulation, one root-table lookup and one complete raw opening. Every refusal and failed final check remains counted. -/
theorem finish_step_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (services : Services Response τ) (serviceBound : ServiceUniform services)
    (caps : KemCaps) (bounded : KemBound setup caps) (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) :
    ((finishStep setup codec publicValue beaconSeed services raw).run state).IsTotalQueryBound
      ((caps.decapsCost + 128) * PqxdhServerAuthGapDh.initSentFlag state.1) := by
  simp only [finishStep, StateT.run]
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [PqxdhServerAuthGapDh.initSentFlag, phase, Nat.mul_one]
      apply isTotalQueryBound_bind (n₁ := caps.decapsCost) (n₂ := 128)
      · rw [StateT.run', IsTotalQueryBound, isQueryBound_map_iff]
        exact beacon_prefix_uniform setup codec beaconSeed caps bounded control _ oneTime kem raw ()
      · intro prepared
        cases prepared with
        | none => trivial
        | some pending =>
            apply isTotalQueryBound_bind (n₁ := 64) (n₂ := 64) (serviceBound.derive _ state.2.2)
            rintro ⟨reply, table⟩
            cases reply with
            | rejected => trivial
            | root root =>
                simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
                exact beacon_after_uniform setup codec pending _ ((), state.1.ctx)
            | hidden =>
                simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
                exact serviceBound.after pending ((), state.1.ctx)
  | _ => trivial

/-- Public HMAC evaluations remain real outside the approved Extract-domain interface; inside it, the complete service pays its table cap. -/
theorem hmac_step_uniform (setup : Setup baseSpec KemSK)
    (services : Services Response τ) (serviceBound : ServiceUniform services)
    (key : PqxdhSecretInputKdf.HmacBlock) (bytes : Pqxdh.Bytes) (state : FlatState KemSK τ) :
    ((hmacStep setup services key bytes).run state).IsTotalQueryBound
      (if key = PqxdhSecretInputKdf.zeroSalt ∧ bytes.length = 192 then 64 else 0) := by
  simp only [hmacStep, StateT.run]
  split_ifs
  · rw [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    exact serviceBound.table bytes state.2.2
  · trivial

/-- The unchanged public commitment oracle retains its shared-cache 64-byte miss allowance. -/
theorem hash_step_uniform (bytes : Pqxdh.Bytes) (state : FlatState KemSK τ) :
    ((hashStep bytes).run state).IsTotalQueryBound 64 := by
  simp only [hashStep, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
  exact CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) state.1.ctx

/-- Every original API capability pays its explicit immediate bill, including arbitrary replies and bad-state continuations. -/
theorem skeleton_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (services : Services Response τ) (serviceBound : ServiceUniform services)
    (caps : KemCaps) (bounded : KemBound setup caps) (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ) :
    ((skeleton setup codec checks publicValue beaconSeed services query).run state).IsTotalQueryBound
      (entryBill caps query state.1) := by
  rcases query with coin | query
  · simp only [skeleton, StateT.run, entryBill, IsTotalQueryBound, isQueryBound_map_iff]
    rw [isQueryBound_query_iff]
    omega
  cases query with
  | accept raw => exact accept_step_uniform setup codec checks publicValue services serviceBound caps bounded raw state
  | build index payload => exact build_step_uniform setup codec checks services serviceBound index payload state
  | finish raw => exact finish_step_uniform setup codec publicValue beaconSeed services serviceBound caps bounded raw state
  | hmac key bytes => exact hmac_step_uniform setup services serviceBound key bytes state
  | hash bytes => exact hash_step_uniform bytes state
  | reveal key => trivial

/-- Designation, sticky refusal and complete private instrumentation add no random draw; both actual handlers pay the same proved bill on every state. -/
theorem hidden_handler_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (services : Services Response HiddenTable) (serviceBound : ServiceUniform services)
    (caps : KemCaps) (bounded : KemBound setup caps) (query : ServerAuthSpec.Domain) (state : HiddenState KemSK) :
    ((hiddenHandler setup codec checks context Q j services query).run state).IsTotalQueryBound
      (entryBill caps query state.1.1) := by
  simp only [hiddenHandler, StateT.run, IsTotalQueryBound, isQueryBound_map_iff, once]
  split_ifs
  all_goals simp only [latch, StateT.run, isQueryBound_map_iff]
  · exact skeleton_uniform setup codec checks _ context.beaconSeed services serviceBound caps bounded query state.1
  · exact skeleton_uniform setup codec checks _ context.beaconSeed _
      (selecting_services_uniform setup context services serviceBound) caps bounded query state.1
  · exact skeleton_uniform setup codec checks _ context.beaconSeed services serviceBound caps bounded query state.1

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.accept_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.accept_step_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.build_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.build_step_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finish_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finish_step_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmac_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmac_step_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hash_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hash_step_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.skeleton_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.skeleton_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_handler_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_handler_uniform
