-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter
import BeaconcryptCore.Computational.RegistrationAgreementSourceEntries
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! Source Core entry bodies derive the finite bound used by the literal public SDK executor. Both roles and actual replay lookups use the same native nine-step request program with the proved source-field interpreter. The remaining material interpretation is per primitive. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementInterpreter (handler)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]

noncomputable def run {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (work : OracleComp Spec (RustM agreement.AgreementEffect)) (rng : R) : RustT m (agreement.AgreementEffect × R) := do
  let (result, after) ← (simulateQ (handler generator keys) work).run ⟨rng, .None, .None⟩
  let completed ← liftRust result
  pure (completed, after.rng)

omit material primitive crypto [LawfulMonad m] in
private theorem lift_ok {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl

noncomputable section

theorem entry {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (start : RustM agreement.AgreementEffect)
    (normal : ∃ phase, start = .ok phase)
    (bounded : ∀ phase, start = .ok phase → rank phase ≤ 9) (rng : R) :
    (do let phase ← liftRust start
        beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT m) generator phase keys rng) =
      run generator keys (continueWith start (drive 9)) rng := by
  obtain ⟨phase, started⟩ := normal
  rw [started, lift_ok, pure_bind,
    AdapterPublicAgreementInterpreter.execute_nine generator keys phase rng (bounded phase started)]
  rfl

theorem server {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (rng : R) :
    (do let phase ← liftRust (agreement.begin_server_agreement control status authenticated)
        beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT m) generator phase keys rng) =
      run generator keys (RegistrationAgreementExecutor.server control status authenticated) rng := by
  apply entry generator keys _ (BeaconcryptCore.PanicFreedom.KeyAgreement.begin_server_agreement_total control status authenticated)
  exact RegistrationAgreementSourceEntries.server_rank control status authenticated

theorem beacon {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (authenticated : registration.AuthenticatedResponse) (rng : R) :
    (do let phase ← liftRust (agreement.begin_beacon_agreement authenticated)
        beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT m) generator phase keys rng) =
      run generator keys (RegistrationAgreementExecutor.beacon authenticated) rng := by
  apply entry generator keys _ (BeaconcryptCore.PanicFreedom.KeyAgreement.begin_beacon_agreement_total authenticated)
  exact RegistrationAgreementSourceEntries.beacon_rank authenticated

theorem lookup {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (pending : peer.RegistrationLookup) (consumed : Bool) (rng : R) :
    (do let phase ← liftRust (pending.resume consumed)
        beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT m) generator phase keys rng) =
      run generator keys (continueWith (pending.resume consumed) (drive 9)) rng := by
  apply entry generator keys _ ?_ (RegistrationAgreementSourceEntries.lookup_rank pending consumed)
  cases consumed with
  | false => exact BeaconcryptCore.PanicFreedom.KeyAgreement.begin_server_agreement_total pending.control .Fresh pending.authenticated
  | true => exact ⟨.Rejected .None, rfl⟩
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries.entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries.entry

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries.server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries.beacon

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries.lookup
