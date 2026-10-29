-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordPackage

/-! Arbitrary actual effectful native World clients consume the ordered chain, CTX integrity and privacy reductions while retaining the permitted actual hidden-origin map in their decision. The real annotated source forgets only that observation to recover the exact guarded native result; no private seed or primitive state is supplied to an observer. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto
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
  (budget : PqxdhDeploymentInterface.Budget) (observe : View n E Value → Bool)

noncomputable def real : ProbComp (View n E Value) :=
  (RegistrationNativeRecordPackage.view ∘ chainView) <$>
    chainsOf (fun _ => false) setup codec route (client work)

noncomputable def decision (old : PqxdhRecordLiftIdeal.View n (Extra E) Value) : ProbComp Bool :=
  pure (observe (RegistrationNativeRecordPackage.view old))

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

/-- The complete real annotated source reaches all-random records while retaining the same permitted origin-aware observer through the three explicit record losses. -/
theorem random_bound (records : RecordBounded budget (client work))
    (bill : BudgetKind → Nat)
    (billed : ∀ kind, Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route (client work) PqxdhRecordLiftProtocol.initialControl) (bill kind))
    (hmac : PqxdhSecretInputKdf.HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal ((observe <$> real setup codec route work).boolDistance
      (observe <$> ctx (fun _ => .random) setup codec route work)) ≤
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
  have firstEq :
      (chainsOf (fun _ => false) setup codec route (client work) >>= fun result => decision observe (chainView result)) =
        observe <$> real setup codec route work := by
    simp only [real, Functor.map_map, decision, bind_pure_comp]
    rfl
  have lastEq :
      (ctxRunOf (fun _ => .random) id setup codec route (client work) >>= fun result => decision observe (ctxView result)) =
        observe <$> ctx (fun _ => .random) setup codec route work := by
    simp only [ctx, Functor.map_map, decision, bind_pure_comp]
    rfl
  simpa only [firstEq, lastEq] using compared

/-- Forgetting only the origin observation recovers the exact complete actual guarded source, including effectful startup. -/
theorem real_result_source :
    View.result <$> real setup codec route work = actual setup codec route work := by
  simpa only [real, Functor.map_map, Function.comp_def, chainView, PqxdhRecordLiftIdeal.viewOf,
    RegistrationNativeRecordPackage.view, RegistrationNativeRecordPackage.decode, Option.map_map] using
    RegistrationNativeRecordPackage.real_result_source setup codec route work

/-- The real annotated view is the literal same cursor-aware World AST under the all-real private service, with the actual control origin map retained. -/
theorem real_source :
    real setup codec route work =
      (fun result => RegistrationNativeRecordPackage.nativeView (result.1.1.1, result.1.2) result.2.produced) <$>
        CborRawRecordOriginFlatten.interpret
          (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source (fun _ => false)) setup codec)
          codec route work CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl PqxdhRecordLiftProtocol.initialPrivate := by
  simp only [real, PqxdhRecordLiftLaterWorlds.chainsOf, client, CborRecordWorldClient.client,
    PqxdhRecordLiftProtocol.schedule, CborRawRecordOriginFlatten.interpret,
    simulateQ_map, StateT.run_map, Functor.map_map]
  congr 1
  funext result
  exact RegistrationNativeRecordPackage.encoded_view (result.1.1.1, result.1.2) result.2.produced

end BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto.decision_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto.decision_coins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto.random_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto.real_result_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto.real_result_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto.real_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto.real_source
