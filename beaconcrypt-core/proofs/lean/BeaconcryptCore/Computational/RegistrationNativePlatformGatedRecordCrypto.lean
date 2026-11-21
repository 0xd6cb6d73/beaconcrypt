-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills
import BeaconcryptCore.Computational.CborRawRecordLiftCrypto
/-! Chain, CTX integrity and privacy reductions for the actual gated open client. The identical capacity service and persistent public retry state run through every hybrid; every loss names the concrete reduction. The source frame and narrow public service cost receipt give resource bounds, rather than a whole security or client-equivalence premise. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment WorldSpec EffectKind Frame)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftIdeal (View chainView ctxView hops)
open PqxdhRecordLiftLaterWorlds (Outcome chainsOf ctxRunOf)
open RegistrationNativePlatformGatedRecordInterface (client)
open CborRawRecordLiftCrypto (chainLoss authLoss privacyLoss)
variable {n : Nat} {ι KemSK Reader Response E X Failure : Type} {baseSpec : OracleSpec ι}
section Bounds
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (reserveCoins : Nat)
    (reserveBounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound reserveCoins)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
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
          (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (chainView value)).boolDistance
        (chainsOf (fun _ => true) setup codec route
          (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (chainView value))) ≤
      chainLoss setup codec route (client env reserve setup.source.crypto codec serverKid bounds mode adversary) budget decision
        hmac :=
  PqxdhRecordLiftLaterChain.chain_loss_of setup codec route budget _
    (RegistrationNativePlatformGatedRecordBounds.client_bound env reserve setup.source.crypto codec serverKid bounds mode budget adversary respects)
    hmac correct (fun view _ => decision view)

include framed respects coins reserveBounded in
/-- Native CBOR admission retains the genuine shared-cache and raw-attempt caps of every CTX integrity reduction. -/
theorem auth_bound (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal
      ((chainsOf (fun _ => true) setup codec route
          (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (chainView value)).boolDistance
        (ctxRunOf (fun _ => .replay) id setup codec route
          (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (ctxView value))) ≤
      authLoss setup codec route (client env reserve setup.source.crypto codec serverKid bounds mode adversary) budget decision
        fallback (PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, cost⟩)
          (PqxdhRecordLiftCtxBills.programBill .raw ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have program := fun kind => RegistrationNativePlatformGatedRecordBills.ctx env startup allowance framed reserve reserveCoins reserveBounded setup.source.crypto
    codec route serverKid bounds mode budget adversary respects cost kind
  have stepBills := fun step : Fin (hops n budget) => PqxdhRecordLiftLaterCtx.step_bills_of setup codec route _ _ program
    decision cost coins budget step
  exact PqxdhRecordLiftLaterCtx.ctx_auth_loss_of setup codec route fallback budget _
    (RegistrationNativePlatformGatedRecordBounds.client_bound env reserve setup.source.crypto codec serverKid bounds mode budget adversary respects)
    decision _ _ (fun step => ⟨1, by
      simpa only [RegistrationNativePlatformGatedRecordBills.ctxBill, PqxdhRecordLiftCtxBills.effectBill,
        Nat.zero_mul, Nat.add_zero] using (stepBills step).2.1,
      (stepBills step).2.2.1, by norm_num, by
      simpa only [RegistrationNativePlatformGatedRecordBills.ctxBill, PqxdhRecordLiftCtxBills.effectBill,
        Nat.zero_mul, Nat.add_zero] using (stepBills step).2.2.2⟩)

include respects in
/-- The concrete raw replay-to-random loss is the exact IND-dollar reduction sum at coefficient one. -/
theorem privacy_bound :
    ENNReal.ofReal
      ((ctxRunOf (fun _ => .replay) id setup codec route
          (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (ctxView value)).boolDistance
        (ctxRunOf (fun _ => .random) id setup codec route
          (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (ctxView value))) ≤
      privacyLoss setup codec route (client env reserve setup.source.crypto codec serverKid bounds mode adversary) budget decision :=
  PqxdhRecordLiftLaterPriv.ctx_priv_loss_of setup codec route budget _
    (RegistrationNativePlatformGatedRecordBounds.client_bound env reserve setup.source.crypto codec serverKid bounds mode budget adversary respects)
    decision

include framed respects coins reserveBounded in
/-- The actual raw real and integrity-ideal record worlds differ by the explicit chain and CTX integrity losses. -/
theorem record_auth_bound (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal
      ((chainsOf (fun _ => false) setup codec route
          (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (chainView value)).boolDistance
        (ctxRunOf (fun _ => .replay) id setup codec route
          (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (ctxView value))) ≤
      chainLoss setup codec route (client env reserve setup.source.crypto codec serverKid bounds mode adversary) budget decision hmac +
        authLoss setup codec route (client env reserve setup.source.crypto codec serverKid bounds mode adversary) budget decision
          fallback (PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, cost⟩)
            (PqxdhRecordLiftCtxBills.programBill .raw ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have triangle := ProbComp.boolDistance_triangle
    (chainsOf (fun _ => false) setup codec route
      (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (chainView value))
    (chainsOf (fun _ => true) setup codec route
      (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (chainView value))
    (ctxRunOf (fun _ => .replay) id setup codec route
      (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (ctxView value))
  calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal triangle
    _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add
      (chain_bound setup codec route env reserve serverKid bounds mode budget adversary respects decision hmac correct)
      (auth_bound setup codec route env reserve reserveCoins reserveBounded startup allowance framed serverKid bounds mode budget adversary respects decision
        cost coins fallback)

include framed respects coins reserveBounded in
/-- The actual raw real and random-ciphertext worlds differ by the three explicit losses, each at coefficient one. -/
theorem record_random_bound (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal
      ((chainsOf (fun _ => false) setup codec route
          (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (chainView value)).boolDistance
        (ctxRunOf (fun _ => .random) id setup codec route
          (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value =>
            decision (ctxView value))) ≤
      chainLoss setup codec route (client env reserve setup.source.crypto codec serverKid bounds mode adversary) budget decision hmac +
        authLoss setup codec route (client env reserve setup.source.crypto codec serverKid bounds mode adversary) budget decision
          fallback (PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, cost⟩)
            (PqxdhRecordLiftCtxBills.programBill .raw ⟨budget, startup, allowance, bounds, n, cost⟩) +
        privacyLoss setup codec route (client env reserve setup.source.crypto codec serverKid bounds mode adversary) budget decision := by
  have triangle := ProbComp.boolDistance_triangle
    (chainsOf (fun _ => false) setup codec route
      (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (chainView value))
    (ctxRunOf (fun _ => .replay) id setup codec route
      (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (ctxView value))
    (ctxRunOf (fun _ => .random) id setup codec route
      (client env reserve setup.source.crypto codec serverKid bounds mode adversary) >>= fun value => decision (ctxView value))
  calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal triangle
    _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add
      (record_auth_bound setup codec route env reserve reserveCoins reserveBounded startup allowance framed serverKid bounds mode budget adversary respects
        decision cost coins hmac correct fallback)
      (privacy_bound setup codec route env reserve serverKid bounds mode budget adversary respects decision)

end Bounds
end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto.chain_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto.chain_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto.auth_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto.auth_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto.privacy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto.privacy_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto.record_auth_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto.record_auth_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto.record_random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordCrypto.record_random_bound
