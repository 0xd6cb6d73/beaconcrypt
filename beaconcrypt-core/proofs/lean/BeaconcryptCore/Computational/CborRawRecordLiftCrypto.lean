-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordLiftReductions

/-! Concrete record cryptographic bounds for the actual CBOR cursor client. The existing arbitrary-client chain, CTX-integrity and CTX-privacy reductions are instantiated with the original full World program below which the cursor runs. Every loss is the advantage of an explicit reduction, with the actual proved service bills; no whole record-lift premise is supplied. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordLiftCrypto
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment WorldSpec EffectKind Frame)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftIdeal (View chainView ctxView hops)
open PqxdhRecordLiftLaterWorlds (Outcome chainsOf ctxRunOf)
open CborRawRecordLiftBounds (client)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
section Losses
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (Outcome E X)) (budget : Budget) (decision : View n E X → ProbComp Bool)

noncomputable def chainLoss (hmac : PqxdhSecretInputKdf.HmacSha512) : ℝ≥0∞ :=
  ∑ step : Fin (hops n budget), PqxdhRecordLiftIdeal.hopLoss hmac
    (PqxdhRecordLiftLaterChain.observerOf setup codec route work (fun view _ => decision view) budget step)

noncomputable def authLoss (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (qHash qRaw : Nat) : ℝ≥0∞ :=
  ∑ step : Fin (hops n budget), PqxdhRecordLiftIdeal.integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead)
    setup.source.crypto fallback (PqxdhRecordLiftCtxModes.decisionClient setup.source.crypto
      (PqxdhRecordLiftLaterCtx.stepClientOf setup codec route work decision budget step)) qHash qRaw

noncomputable def privacyLoss : ℝ≥0∞ :=
  ∑ step : Fin (hops n budget), PqxdhRecordLiftIdeal.privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead)
    setup.source.crypto (PqxdhRecordLiftCtxPrivModes.decisionClient PqxdhRecordLiftCtxPrivModes.bytesSample
      setup.source.crypto (PqxdhRecordLiftLaterPriv.stepClientOf setup codec route work decision budget step))

/-- The all-real compiled cursor client is the actual complete World execution, including its original ledger. -/
theorem real_source :
    (Prod.map id PqxdhRecordLiftWorldCompiler.world ∘ PqxdhRecordLiftProtocol.rejoin) <$>
      chainsOf (fun _ => false) setup codec route work =
        (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run PqxdhRecordLiftWorld.initial := by
  rw [chainsOf, PqxdhRecordLiftMixedWorld.policy_real]
  exact PqxdhRecordLiftProtocol.initial_schedule_source setup codec route work

end Losses
section Bounds
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decision : View n E X → ProbComp Bool) (cost : Nat)
    (coins : ∀ view, (decision view).IsTotalQueryBound cost)

include respects in
/-- The concrete raw chain loss is the exact Extract/HMAC observer sum at coefficient one. -/
theorem chain_bound (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac) :
    ENNReal.ofReal
      ((chainsOf (fun _ => false) setup codec route
          (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (chainView value)).boolDistance
        (chainsOf (fun _ => true) setup codec route
          (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (chainView value))) ≤
      chainLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget decision
        hmac :=
  PqxdhRecordLiftLaterChain.chain_loss_of setup codec route budget _
    (CborRawRecordLiftBounds.record_bounded env setup.source.crypto codec serverKid bounds mode budget adversary respects)
    hmac correct (fun view _ => decision view)

include framed respects coins in
/-- Native CBOR admission retains the genuine shared-cache and raw-attempt caps of every CTX integrity reduction. -/
theorem auth_bound (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal
      ((chainsOf (fun _ => true) setup codec route
          (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (chainView value)).boolDistance
        (ctxRunOf (fun _ => .replay) id setup codec route
          (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (ctxView value))) ≤
      authLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget decision
        fallback (PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, cost⟩)
          (PqxdhRecordLiftCtxBills.programBill .raw ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have program := fun kind => CborRawRecordLiftBounds.ctx_categories env startup allowance framed setup.source.crypto
    codec route serverKid bounds mode budget adversary respects cost kind
  have stepBills := fun step : Fin (hops n budget) => PqxdhRecordLiftLaterCtx.step_bills_of setup codec route _ _ program
    decision cost coins budget step
  exact PqxdhRecordLiftLaterCtx.ctx_auth_loss_of setup codec route fallback budget _
    (CborRawRecordLiftBounds.record_bounded env setup.source.crypto codec serverKid bounds mode budget adversary respects)
    decision _ _ (fun step => ⟨1, (stepBills step).2.1, (stepBills step).2.2.1, by norm_num, (stepBills step).2.2.2⟩)

include respects in
/-- The concrete raw replay-to-random loss is the exact IND-dollar reduction sum at coefficient one. -/
theorem privacy_bound :
    ENNReal.ofReal
      ((ctxRunOf (fun _ => .replay) id setup codec route
          (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (ctxView value)).boolDistance
        (ctxRunOf (fun _ => .random) id setup codec route
          (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (ctxView value))) ≤
      privacyLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget decision :=
  PqxdhRecordLiftLaterPriv.ctx_priv_loss_of setup codec route budget _
    (CborRawRecordLiftBounds.record_bounded env setup.source.crypto codec serverKid bounds mode budget adversary respects)
    decision

include framed respects coins in
/-- The actual raw real and integrity-ideal record worlds differ by the explicit chain and CTX integrity losses. -/
theorem record_auth_bound (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal
      ((chainsOf (fun _ => false) setup codec route
          (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (chainView value)).boolDistance
        (ctxRunOf (fun _ => .replay) id setup codec route
          (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (ctxView value))) ≤
      chainLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget decision hmac +
        authLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget decision
          fallback (PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, cost⟩)
            (PqxdhRecordLiftCtxBills.programBill .raw ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have triangle := ProbComp.boolDistance_triangle
    (chainsOf (fun _ => false) setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (chainView value))
    (chainsOf (fun _ => true) setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (chainView value))
    (ctxRunOf (fun _ => .replay) id setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (ctxView value))
  calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal triangle
    _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add
      (chain_bound setup codec route env serverKid bounds mode budget adversary respects decision hmac correct)
      (auth_bound setup codec route env startup allowance framed serverKid bounds mode budget adversary respects decision
        cost coins fallback)

include framed respects coins in
/-- The actual raw real and random-ciphertext worlds differ by the three explicit losses, each at coefficient one. -/
theorem record_random_bound (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal
      ((chainsOf (fun _ => false) setup codec route
          (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (chainView value)).boolDistance
        (ctxRunOf (fun _ => .random) id setup codec route
          (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (ctxView value))) ≤
      chainLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget decision hmac +
        authLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget decision
          fallback (PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, cost⟩)
            (PqxdhRecordLiftCtxBills.programBill .raw ⟨budget, startup, allowance, bounds, n, cost⟩) +
        privacyLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget decision := by
  have triangle := ProbComp.boolDistance_triangle
    (chainsOf (fun _ => false) setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (chainView value))
    (ctxRunOf (fun _ => .replay) id setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (ctxView value))
    (ctxRunOf (fun _ => .random) id setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (ctxView value))
  calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal triangle
    _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add
      (record_auth_bound setup codec route env startup allowance framed serverKid bounds mode budget adversary respects
        decision cost coins hmac correct fallback)
      (privacy_bound setup codec route env serverKid bounds mode budget adversary respects decision)

end Bounds
end BeaconcryptCore.Computational.CborRawRecordLiftCrypto

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftCrypto.real_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftCrypto.real_source
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftCrypto.chain_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftCrypto.chain_bound
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftCrypto.auth_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftCrypto.auth_bound
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftCrypto.privacy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftCrypto.privacy_bound
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftCrypto.record_auth_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftCrypto.record_auth_bound
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftCrypto.record_random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftCrypto.record_random_bound
