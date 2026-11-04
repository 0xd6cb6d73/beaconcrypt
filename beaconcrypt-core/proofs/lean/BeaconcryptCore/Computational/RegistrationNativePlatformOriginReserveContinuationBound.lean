-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess
/-! Stopping after a successful public send prunes only an original continuation. The actual charged reserve syntax supplies the stopped-tail caps without any claim about hypothetical platform states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveContinuationBound
open PqxdhRecordLiftProtocol (ServiceSpec)
open RegistrationNativePlatformOriginReserveSourceGuess (fixed)
variable {n : Nat} {Platform Failure X : Type}

private theorem bind_prune {I A B C : Type} {spec : OracleSpec I}
    (frontWork : OracleComp spec A) (full : A → OracleComp spec B) (pruned : A → OracleComp spec C)
    (counted : spec.Domain → Prop) [DecidablePred counted] (cap : Nat)
    (bounded : (frontWork >>= full).IsQueryBoundP counted cap)
    (cuts : ∀reply limit,(full reply).IsQueryBoundP counted limit → (pruned reply).IsQueryBoundP counted limit) :
    (frontWork >>= pruned).IsQueryBoundP counted cap := by
  induction frontWork using OracleComp.inductionOn generalizing cap with
  | pure value =>
      simpa only [pure_bind] using cuts value cap (by simpa only [pure_bind] using bounded)
  | query_bind query next ih =>
      simp only [bind_assoc,isQueryBoundP_query_bind_iff] at bounded ⊢
      exact ⟨bounded.1,fun reply => ih reply _ (bounded.2 reply)⟩

def continued (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) X)
    (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (reply : Option RawCtxSourceSend.Encrypted) :
    OracleComp (ServiceSpec n) X := do
  let _ ← ((ServiceSpec n).query (.publish tag) : OracleComp (ServiceSpec n) _)
  let gated ← simulateQ RegistrationNativePlatformOriginGateSource.coins
    ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) reply).run before)
  after gated.1 gated.2

/-- Every actual optional-reply source cap supplies both stopped reserve-tail caps. Only branches after public publication are discarded; all real reserve and failure-state effects are retained. -/
theorem fixed_bound (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) X)
    (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag)
    (counted : (ServiceSpec n).Domain → Prop) [DecidablePred counted] (cap : Nat)
    (bounded : ∀reply,(continued reserve after before tag reply).IsQueryBoundP counted cap)
    (amount : Nat) (absent : Bool) :
    (fixed reserve (after none) before tag amount absent).IsQueryBoundP counted cap := by
  cases absent with
  | true =>
      have full := bounded none
      simp only [continued,RegistrationNativePlatformOrdinaryGate.gate,StateT.run_pure,
        simulateQ_pure,pure_bind] at full
      simpa only [fixed,ite_true,isQueryBoundP_query_bind_iff,isQueryBoundP_map_iff] using full
  | false =>
      let dummy : RawCtxSourceSend.Encrypted := ⟨List.replicate amount default,0#u64,0#u64⟩
      let frontWork : OracleComp (ServiceSpec n) (core.result.Result Unit Failure × Platform) := do
        let _ ← ((ServiceSpec n).query (.publish tag) : OracleComp (ServiceSpec n) _)
        simulateQ RegistrationNativePlatformOriginGateSource.coins ((reserve amount).run before)
      let full : core.result.Result Unit Failure × Platform → OracleComp (ServiceSpec n) X := fun allocated =>
        match allocated.1 with
        | .Ok _ => after (some dummy) allocated.2
        | .Err _ => after none allocated.2
      let pruned : core.result.Result Unit Failure × Platform → OracleComp (ServiceSpec n) (Option (X × Platform)) := fun allocated =>
        match allocated.1 with
        | .Ok _ => pure none
        | .Err _ => (fun value => some (value,allocated.2)) <$> after none allocated.2
      have expanded : continued reserve after before tag (some dummy)=(frontWork >>= full) := by
        simp only [continued,RegistrationNativePlatformOrdinaryGate.gate,StateT.run_bind,
          simulateQ_bind,bind_assoc,dummy,List.length_replicate,frontWork]
        apply bind_congr
        intro _
        apply bind_congr
        rintro ⟨result,platform⟩
        cases result <;> simp only [full,StateT.run_pure,simulateQ_pure,pure_bind]
        rfl
      have original : (frontWork >>= full).IsQueryBoundP counted cap := expanded ▸ bounded (some dummy)
      have stopped := bind_prune frontWork full pruned counted cap original (by
        rintro ⟨result,platform⟩ limit bound
        cases result with
        | Ok returned => exact isQueryBoundP_pure _ _ _
        | Err error => simpa only [pruned,full,isQueryBoundP_map_iff] using bound)
      have same : fixed reserve (after none) before tag amount false=(frontWork >>= pruned) := by
        simp only [fixed,Bool.false_eq_true,ite_false,frontWork,pruned,bind_assoc]
        rfl
      rw [same]
      exact stopped
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveContinuationBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveContinuationBound.fixed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveContinuationBound.fixed_bound
