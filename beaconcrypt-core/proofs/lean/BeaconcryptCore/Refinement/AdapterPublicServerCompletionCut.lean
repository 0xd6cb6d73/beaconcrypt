-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionSource
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! First-record execution preserves the private response-signing cut, and the actual response hash supplies its replacement before signing. Erasing this cut through the complete first-record/publication sequence preserves the identical full state and every base-monad failure poststate. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerCompletionCut
open BeaconcryptCore.Computational
open RegistrationNativePlatformCutJournal (State)
open RegistrationNativePlatformCutErasure (liftWorld)
variable {S Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def stage
    (first : StateT S m (RustM RegistrationServerRecordExecutor.Result))
    (impl : QueryImpl RegistrationSigningShared.Spec (StateT S m))
    (fallback : registration.MldsaSigningRequest → StateT S m RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT S m (RustM (core.option.Option Encoded))) :
    StateT (State S) m (RustM (RegistrationWorldServerPublication.Result Encoded)) := do
  let recorded ← liftWorld first
  RegistrationNativePlatformServerPublication.continueResult recorded
    (RegistrationNativePlatformServerPublication.program
      (RegistrationNativePlatformCutJournal.source impl fallback) (fun view => liftWorld (encode view)))

noncomputable def native
    (first : StateT S m (RustM RegistrationServerRecordExecutor.Result))
    (impl : QueryImpl RegistrationSigningShared.Spec (StateT S m))
    (encode : registration.SignedResponseView → StateT S m (RustM (core.option.Option Encoded))) :
    StateT S m (RustM (RegistrationWorldServerPublication.Result Encoded)) := do
  let recorded ← first
  RegistrationNativePlatformServerPublication.continueResult recorded
    (RegistrationNativePlatformServerPublication.program impl encode)

theorem erasure
    (first : StateT S m (RustM RegistrationServerRecordExecutor.Result))
    (impl : QueryImpl RegistrationSigningShared.Spec (StateT S m))
    (fallback : registration.MldsaSigningRequest → StateT S m RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT S m (RustM (core.option.Option Encoded))) (before : State S) :
    Prod.map id Prod.fst <$> (stage first impl fallback encode).run before =
      (native first impl encode).run before.1 := by
  unfold stage native
  rw [StateT.run_bind, StateT.run_bind, map_bind]
  change ((fun result => (result.1, (result.2, before.2))) <$> first.run before.1 >>= fun result =>
      Prod.map id Prod.fst <$>
        ((RegistrationNativePlatformServerPublication.continueResult result.1
          (RegistrationNativePlatformServerPublication.program
            (RegistrationNativePlatformCutJournal.source impl fallback) (fun view => liftWorld (encode view)))).run result.2)) = _
  rw [bind_map_left]
  apply bind_congr
  rintro ⟨recorded, current⟩
  cases recorded with
  | fail error | div => simp only [RegistrationNativePlatformServerPublication.continueResult, StateT.run_pure, map_pure, Prod.map, id_eq]
  | ok result => cases result with
    | Err rejected => simp only [RegistrationNativePlatformServerPublication.continueResult, StateT.run_pure, map_pure, Prod.map, id_eq]
    | Ok pending => exact RegistrationNativePlatformCutWorld.server impl fallback encode pending (current, before.2)
end BeaconcryptCore.Refinement.AdapterPublicServerCompletionCut
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionCut.erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionCut.erasure
