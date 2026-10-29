-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationNativeKeyPhases

/-! The prepare callback returns the actual root Expand of the protected PRK, before any admitted material demand. Only its private root result is erased by the public message-reference interface. The exact source key schedule then consumes that same dependent root; the primitive trial never treats it as independently sampled context. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKeyPreparation
open RegistrationNativeKeyPhases
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (HmacSha512 HmacOracle RootOutput HmacBlock expandRoot)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open LazyOracleDiscard (StateLens)

/-- This is the root-phase value consumed by the actual private agreement continuation: protected Extract has supplied its cached PRK, and the actual fixed root Expand runs here. Initial64/ongoing76 remain absent until material demand. -/
noncomputable def prepare (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) :
    StateT State ProbComp (Option (Message × RootOutput)) := do
  let accepted ← onMeta (prepareMeta input message)
  match accepted with
  | none => pure none
  | some reference => match input message with
    | none => pure none
    | some bytes =>
      if inside bytes then
        (fun prk => some (reference, expandRoot hmac prk)) <$> cacheLens.query bytes
      else pure (some (reference, RegistrationNativeRelatedRoot.nativeRoot source bytes))

private theorem dropped_query (bytes : Pqxdh.Bytes) (before : State) :
    Prod.snd <$> (cacheLens.query bytes).run before = cacheLens.complete bytes before := by
  simp only [StateLens.query, StateLens.complete, cacheLens, StateLens.snd,
    StateT.run, LazyOracleDiscard.complete, Functor.map_map]

private theorem prepareMeta_run (input : Message → Option Pqxdh.Bytes) (message : Message) (before : Meta) :
    (prepareMeta input message).run before = match input message with
    | none => pure (none, { before with prepares := before.prepares + 1 })
    | some bytes => pure (some message, { before with
        prepared := Function.update before.prepared bytes true
        prepares := before.prepares + 1
        roots := before.roots + 1 }) := rfl

/-- Keeping only the prepared message erases precisely the private root reply, after executing its real dependent root Expand phase. The complete preparation metadata and private PRK cache agree. -/
theorem prepare_public (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) (before : State) :
    Prod.map (Option.map Prod.fst) id <$> (prepare source hmac input inside message).run before =
      (eager source hmac input inside (.inr (.prepare message))).run before := by
  rw [eager_prepare_run]
  simp only [prepare, StateT.run_bind, onMeta_run, prepareMeta_run]
  cases realized : input message with
  | none =>
    simp [realized, point, StateLens.completeOpt, StateT.run_pure]
  | some bytes =>
    cases protectedInput : inside bytes
    · simp [realized, point, Option.filter, protectedInput, StateLens.completeOpt, StateT.run_pure]
    · simp only [realized, point, protectedInput, map_pure, pure_bind, ite_true,
        Option.filter_some, StateLens.completeOpt, StateT.run_map, Functor.map_map]
      rw [← dropped_query]
      simp only [bind_pure_comp, Functor.map_map, Prod.map, id_eq, Option.map_some]

/-- The root handed privately to the native continuation and its complete108 material are one dependent function of the same PRK. -/
theorem material_from_prepared (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (prk : HmacBlock) :
    PqxdhServerAuthKeySchedule.fromRoot source (expandRoot hmac prk) =
      PqxdhServerAuthKeySchedule.keySchedule source hmac prk := rfl

end BeaconcryptCore.Computational.RegistrationNativeKeyPreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyPreparation.prepare_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyPreparation.prepare_public
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyPreparation.material_from_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyPreparation.material_from_prepared
