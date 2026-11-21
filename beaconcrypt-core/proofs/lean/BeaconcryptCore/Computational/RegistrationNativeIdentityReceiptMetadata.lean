-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView

/-! The actual source signer consumes only its complete ML request. Different private raw transcript payloads or cached digest annotations change only the appended receipt coordinate, which the explicit analysis view erases. The actual signer draw, optional reply, native counters and all other reached state are identical. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReceiptMetadata
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (change : S → S) (before : S) :
    (modify change : StateT S m Unit) before = pure ((), change before) := rfl

/-- The actual compact Beacon source callback cannot leak a censored preimage through current private ML receipt metadata. -/
theorem compact (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat)
    (owner : RegistrationNativeIdentityFrontend.Owner source) (request : registration.MldsaSigningRequest)
    (left right : MldsaTranscriptAuth.Payload) (digestLeft digestRight : CtxRomAuth.CtxDigest)
    (before : RegistrationNativeIdentityHistoryView.Packed (source := source) (Auxiliary := Auxiliary)) :
    Prod.map id RegistrationNativeIdentityEnvReceiptView.view <$>
      (RegistrationNativeIdentityHistoryView.pack (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary)
        setup source index owner (.inl (.sign request left digestLeft)))).run before =
    Prod.map id RegistrationNativeIdentityEnvReceiptView.view <$>
      (RegistrationNativeIdentityHistoryView.pack (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary)
        setup source index owner (.inl (.sign request right digestRight)))).run before := by
  rfl

/-- The literal CTX/native Local source dictionary has the same metadata independence with all sampled draw counters retained. -/
theorem local_sign (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (request : registration.MldsaSigningRequest) (left right : MldsaTranscriptAuth.Payload)
    (digestLeft digestRight : CtxRomAuth.CtxDigest) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id RegistrationNativePlatformIdentityReceiptView.view <$>
      (RegistrationNativePlatformCtxSigning.outgoing sign (.sign request left digestLeft)).run before =
    Prod.map id RegistrationNativePlatformIdentityReceiptView.view <$>
      (RegistrationNativePlatformCtxSigning.outgoing sign (.sign request right digestRight)).run before := by
  simp only [RegistrationNativePlatformCtxSigning.outgoing, StateT.run, Functor.map_map,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]

end BeaconcryptCore.Computational.RegistrationNativeIdentityReceiptMetadata
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReceiptMetadata.compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReceiptMetadata.compact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReceiptMetadata.local_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReceiptMetadata.local_sign
