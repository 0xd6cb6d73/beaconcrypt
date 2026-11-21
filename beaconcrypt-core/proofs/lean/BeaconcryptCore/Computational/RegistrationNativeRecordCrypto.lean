-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordPackage

/-! Arbitrary actual effectful native World clients consume the existing ordered chain, CTX integrity and CTX privacy reductions. Every loss is an explicit reduction advantage. Resource hypotheses concern actual query counts only; source and ideal endpoint equalities are derived by the exact native packaging layer. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordCrypto
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftIdeal (hops chainView ctxView)
open PqxdhRecordLiftLaterWorlds (chainsOf ctxRunOf RecordBounded)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open RegistrationNativeRecordPackage (Extra client actual ctx View)
variable {n : Nat} {ι KemSK Reader Response E Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
  (budget : PqxdhDeploymentInterface.Budget) (observe : RegistrationNativeEntropyRun.Outcome E Value → Bool)

noncomputable def decision (old : PqxdhRecordLiftIdeal.View n (Extra E) Value) : ProbComp Bool :=
  pure (observe (RegistrationNativeRecordPackage.view old).result)

noncomputable def chainLoss (hmac : PqxdhSecretInputKdf.HmacSha512) :=
  CborRawRecordLiftCrypto.chainLoss setup codec route (client work) budget (decision observe) hmac

noncomputable def authLoss (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (qHash qRaw : Nat) :=
  CborRawRecordLiftCrypto.authLoss setup codec route (client work) budget (decision observe) fallback qHash qRaw

noncomputable def privacyLoss :=
  CborRawRecordLiftCrypto.privacyLoss setup codec route (client work) budget (decision observe)

/-- Deterministic complete-native-result observations have zero decision-coin cost. -/
theorem decision_coins (old : PqxdhRecordLiftIdeal.View n (Extra E) Value) :
    (decision observe old).IsTotalQueryBound 0 := by
  trivial

/-- Actual startup and the original native program reach the all-random endpoint through the three explicit record losses at coefficient one. -/
theorem random_bound (records : RecordBounded budget (client work))
    (bill : BudgetKind → Nat)
    (billed : ∀ kind, Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route (client work) PqxdhRecordLiftProtocol.initialControl) (bill kind))
    (hmac : PqxdhSecretInputKdf.HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal ((observe <$> actual setup codec route work).boolDistance
      ((observe ∘ View.result) <$> ctx (fun _ => .random) setup codec route work)) ≤
      chainLoss setup codec route work budget observe hmac +
        authLoss setup codec route work budget observe fallback (bill .hash) (bill .raw) +
          privacyLoss setup codec route work budget observe := by
  have chain := PqxdhRecordLiftLaterChain.chain_loss_of setup codec route budget (client work) records hmac correct
    (fun old _ => decision observe old)
  have stepBills := fun step : Fin (hops n budget) => PqxdhRecordLiftLaterCtx.step_bills_of setup codec route
    (client work) bill billed (decision observe) 0 (decision_coins observe) budget step
  have auth := PqxdhRecordLiftLaterCtx.ctx_auth_loss_of setup codec route fallback budget (client work) records
    (decision observe) (bill .hash) (bill .raw)
    (fun step => ⟨1, (stepBills step).2.1, (stepBills step).2.2.1, by norm_num, (stepBills step).2.2.2⟩)
  have privacy := PqxdhRecordLiftLaterPriv.ctx_priv_loss_of setup codec route budget (client work) records (decision observe)
  have first := ProbComp.boolDistance_triangle
    (chainsOf (fun _ => false) setup codec route (client work) >>= fun result => decision observe (chainView result))
    (chainsOf (fun _ => true) setup codec route (client work) >>= fun result => decision observe (chainView result))
    (ctxRunOf (fun _ => .replay) id setup codec route (client work) >>= fun result => decision observe (ctxView result))
  have last := ProbComp.boolDistance_triangle
    (chainsOf (fun _ => false) setup codec route (client work) >>= fun result => decision observe (chainView result))
    (ctxRunOf (fun _ => .replay) id setup codec route (client work) >>= fun result => decision observe (ctxView result))
    (ctxRunOf (fun _ => .random) id setup codec route (client work) >>= fun result => decision observe (ctxView result))
  have compared : ENNReal.ofReal
      ((chainsOf (fun _ => false) setup codec route (client work) >>= fun result => decision observe (chainView result)).boolDistance
        (ctxRunOf (fun _ => .random) id setup codec route (client work) >>= fun result => decision observe (ctxView result))) ≤
      chainLoss setup codec route work budget observe hmac +
        authLoss setup codec route work budget observe fallback (bill .hash) (bill .raw) +
          privacyLoss setup codec route work budget observe := by
    calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal last
      _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ (ENNReal.ofReal (_ + _)) + _ := add_le_add (ENNReal.ofReal_le_ofReal first) le_rfl
      _ = _ + _ + _ := congrArg (fun value => value + _) (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _))
      _ ≤ _ := add_le_add (add_le_add chain auth) privacy
  have real := RegistrationNativeRecordPackage.real_result_source setup codec route work
  have firstEq :
      (chainsOf (fun _ => false) setup codec route (client work) >>= fun result => decision observe (chainView result)) =
        observe <$> actual setup codec route work := by
    rw [← real, Functor.map_map]
    simp only [decision, bind_pure_comp, chainView, PqxdhRecordLiftIdeal.viewOf,
      RegistrationNativeRecordPackage.view, RegistrationNativeRecordPackage.decode, Option.map_map]
    rfl
  have lastEq :
      (ctxRunOf (fun _ => .random) id setup codec route (client work) >>= fun result => decision observe (ctxView result)) =
        (observe ∘ View.result) <$> ctx (fun _ => .random) setup codec route work := by
    simp only [ctx, Functor.map_map, decision, bind_pure_comp]
    rfl
  simpa only [firstEq, lastEq] using compared

end BeaconcryptCore.Computational.RegistrationNativeRecordCrypto

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordCrypto.decision_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordCrypto.decision_coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordCrypto.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordCrypto.random_bound
