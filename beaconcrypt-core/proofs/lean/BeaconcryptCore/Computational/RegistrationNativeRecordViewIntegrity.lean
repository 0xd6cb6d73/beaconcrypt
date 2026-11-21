-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto

/-! Integrity-only record comparison for the actual arbitrary native World program, including its effectful initialization and shared cache. Ordinary-origin and cross-handle observers need only the ordered chain and CTX integrity reductions. Every observer-specific reduction and source category bill remains explicit. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordViewIntegrity
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftIdeal (hops chainView ctxView)
open PqxdhRecordLiftLaterWorlds (chainsOf ctxRunOf RecordBounded)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open RegistrationNativeRecordPackage (client actual ctx View)
open RegistrationNativeRecordViewCrypto (real decision chainLoss authLoss decision_coins)
variable {n : Nat} {ι KemSK Reader Response E Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
  (budget : PqxdhDeploymentInterface.Budget) (observe : View n E Value → Bool)

/-- The complete actual native program reaches replay-dictionary integrity with only the explicit chain and CTX authentication losses. -/
theorem replay_bound (records : RecordBounded budget (client work))
    (bill : BudgetKind → Nat)
    (billed : ∀ kind, Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route (client work) PqxdhRecordLiftProtocol.initialControl) (bill kind))
    (hmac : PqxdhSecretInputKdf.HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal ((observe <$> real setup codec route work).boolDistance
      (observe <$> ctx (fun _ => .replay) setup codec route work)) ≤
      chainLoss setup codec route work budget observe hmac +
        authLoss setup codec route work budget observe fallback (bill .hash) (bill .raw) := by
  have chain := PqxdhRecordLiftLaterChain.chain_loss_of setup codec route budget (client work) records hmac correct
    (fun old _ => decision observe old)
  have stepBills := fun step : Fin (hops n budget) => PqxdhRecordLiftLaterCtx.step_bills_of setup codec route
    (client work) bill billed (decision observe) 0 (decision_coins observe) budget step
  have auth := PqxdhRecordLiftLaterCtx.ctx_auth_loss_of setup codec route fallback budget (client work) records
    (decision observe) (bill .hash) (bill .raw)
    (fun step => ⟨1, (stepBills step).2.1, (stepBills step).2.2.1, by norm_num, (stepBills step).2.2.2⟩)
  have triangle := ProbComp.boolDistance_triangle
    (chainsOf (fun _ => false) setup codec route (client work) >>= fun result => decision observe (chainView result))
    (chainsOf (fun _ => true) setup codec route (client work) >>= fun result => decision observe (chainView result))
    (ctxRunOf (fun _ => .replay) id setup codec route (client work) >>= fun result => decision observe (ctxView result))
  have compared : ENNReal.ofReal
      ((chainsOf (fun _ => false) setup codec route (client work) >>= fun result => decision observe (chainView result)).boolDistance
        (ctxRunOf (fun _ => .replay) id setup codec route (client work) >>= fun result => decision observe (ctxView result))) ≤
      chainLoss setup codec route work budget observe hmac +
        authLoss setup codec route work budget observe fallback (bill .hash) (bill .raw) := by
    calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal triangle
      _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add chain auth
  have first :
      (chainsOf (fun _ => false) setup codec route (client work) >>= fun result => decision observe (chainView result)) =
        observe <$> real setup codec route work := by
    simp only [real, Functor.map_map, decision, bind_pure_comp]
    rfl
  have last :
      (ctxRunOf (fun _ => .replay) id setup codec route (client work) >>= fun result => decision observe (ctxView result)) =
        observe <$> ctx (fun _ => .replay) setup codec route work := by
    simp only [ctx, Functor.map_map, decision, bind_pure_comp]
    rfl
  simpa only [first, last] using compared

/-- The same named actual native event pays the two reductions once, without conditioning on an ideal good state. -/
theorem replay_probability (records : RecordBounded budget (client work))
    (bill : BudgetKind → Nat)
    (billed : ∀ kind, Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route (client work) PqxdhRecordLiftProtocol.initialControl) (bill kind))
    (hmac : PqxdhSecretInputKdf.HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[observe <$> real setup codec route work] {true} ≤
      𝒟[observe <$> ctx (fun _ => .replay) setup codec route work] {true} +
        chainLoss setup codec route work budget observe hmac +
          authLoss setup codec route work budget observe fallback (bill .hash) (bill .raw) := by
  exact (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (observe <$> real setup codec route work) (observe <$> ctx (fun _ => .replay) setup codec route work)).trans
    ((add_le_add le_rfl (replay_bound setup codec route work budget observe records bill billed hmac correct fallback)).trans_eq
      (add_assoc _ _ _).symm)

/-- Erasing only origin observations retains the exact same source program event and failed-operation effects. -/
theorem source_probability
    (event : RegistrationNativeEntropyRun.Outcome E Value → Bool)
    (records : RecordBounded budget (client work)) (bill : BudgetKind → Nat)
    (billed : ∀ kind, Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route (client work) PqxdhRecordLiftProtocol.initialControl) (bill kind))
    (hmac : PqxdhSecretInputKdf.HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[event <$> actual setup codec route work] {true} ≤
      𝒟[(event ∘ View.result) <$> ctx (fun _ => .replay) setup codec route work] {true} +
        chainLoss setup codec route work budget (event ∘ View.result) hmac +
          authLoss setup codec route work budget (event ∘ View.result) fallback (bill .hash) (bill .raw) := by
  have same := congrArg (fun distribution => event <$> distribution)
    (RegistrationNativeRecordViewCrypto.real_result_source setup codec route work)
  simp only [Functor.map_map] at same
  rw [← same]
  exact replay_probability setup codec route work budget (event ∘ View.result) records bill billed hmac correct fallback

end BeaconcryptCore.Computational.RegistrationNativeRecordViewIntegrity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordViewIntegrity.replay_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordViewIntegrity.replay_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordViewIntegrity.replay_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordViewIntegrity.replay_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordViewIntegrity.source_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordViewIntegrity.source_probability
