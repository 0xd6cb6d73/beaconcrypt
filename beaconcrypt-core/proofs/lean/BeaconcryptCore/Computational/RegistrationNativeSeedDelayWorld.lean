-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall

/-! Every actual World query commutes with an unobserved completion of the canonical hidden-seed cache under the explicitly named accounting projection. Records retain their installed concrete kernels and the current shared CTX cache; administration retains every used-role guard and marker. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (EnvEffects WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeSeedDelayCore (lens mask)
open LazyOracleDiscard (Commutes)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

def charge (query : (EnvEffects n).Domain) : StateT (State n) ProbComp Unit := fun before =>
  pure ((), PqxdhRecordLiftWorld.chargeEffect query before)

theorem charge_commutes (query : (EnvEffects n).Domain) : Commutes lens (charge query) := by
  apply LazyOracleDiscard.commutes_frame
  intro before cache
  simp only [charge, StateT.run, PqxdhRecordLiftWorld.chargeEffect, lens, map_pure]

/-- All actual capability branches commute; hidden installation uses its exact cached-query construction and every other branch is a concrete cache frame. -/
theorem capability_commutes (query : (PqxdhRecordLiftInterface.CapabilitySpec n).Domain) :
    Commutes lens (RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.capability query)) := by
  by_cases quiet : ¬RegistrationNativeSeedDelayFrames.ReadsSeed query
  · exact RegistrationNativeSeedDelayCore.normalize_commutes _
      (RegistrationNativeSeedDelayFrames.capability_frame query quiet)
  · cases query with
    | installServer keyId binding ref =>
        cases ref with
        | hidden slot => exact RegistrationNativeSeedDelayInstall.server_commutes keyId binding slot
        | known kernel => exact False.elim (quiet (by change ¬False; exact not_false))
    | installBeacon owner shell ref =>
        cases ref with
        | hidden slot => exact RegistrationNativeSeedDelayInstall.beacon_commutes owner shell slot
        | known kernel => exact False.elim (quiet (by change ¬False; exact not_false))
    | peerPresent keyId => exact False.elim (quiet (by change ¬False; exact not_false))
    | ownerPresent owner => exact False.elim (quiet (by change ¬False; exact not_false))
    | appendOwner identity keyId phase => exact False.elim (quiet (by change ¬False; exact not_false))
    | advanceOwner owner phase => exact False.elim (quiet (by change ¬False; exact not_false))
    | hash bytes => exact False.elim (quiet (by change ¬False; exact not_false))

noncomputable def delegated : QueryImpl (EnvEffects n) (StateT (State n) ProbComp)
  | .inl coin => RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.sampled (unifSpec.query coin : ProbComp _))
  | .inr request => RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.capability request)

/-- The literal effect charge stays before its actual callback under normalization. -/
theorem effect_shape (query : (EnvEffects n).Domain) :
    RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.effects query) = (do
      let _ ← RegistrationNativeSeedDelayCore.normalize (charge query)
      delegated query) := by
  funext before
  cases query <;> rfl

/-- Public coins and actual counted administration preserve commutation without erasing their effect/native receipts. -/
theorem effects_commutes (query : (EnvEffects n).Domain) :
    Commutes lens (RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.effects query)) := by
  rw [effect_shape]
  apply LazyOracleDiscard.commutes_bind lens
    (RegistrationNativeSeedDelayNormalize.normalize_commutes _ (charge_commutes query))
  intro _
  cases query with
  | inl coin =>
      exact RegistrationNativeSeedDelayCore.normalize_commutes _
        (RegistrationNativeSeedDelayCore.sampled_frame (unifSpec.query coin : ProbComp _))
  | inr request => exact capability_commutes request

noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (WorldSpec n) (StateT (State n) ProbComp) :=
  fun query => RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.handler setup codec route query)

/-- Every concrete normalized World query satisfies seed completion commutation; no client noninterference premise is required. -/
theorem handler_commutes (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) :
    Commutes lens (handler setup codec route query) := by
  cases query with
  | inl created =>
      exact RegistrationNativeSeedDelayCore.normalize_commutes _
        (RegistrationNativeSeedDelayFrames.initialize_frame created)
  | inr query => cases query with
    | inl effect => exact effects_commutes effect
    | inr query => cases query with
      | inl query => cases query with
        | inl send =>
            exact RegistrationNativeSeedDelayCore.normalize_commutes _
              (RegistrationNativeSeedDelayFrames.server_frame setup codec route (.inl send))
        | inr raw =>
            exact RegistrationNativeSeedDelayCore.normalize_commutes _
              (RegistrationNativeSeedDelayFrames.server_frame setup codec route (.inr raw))
      | inr query => rcases query with ⟨owner, query⟩; cases query with
        | inl plaintext =>
            exact RegistrationNativeSeedDelayCore.normalize_commutes _
              (RegistrationNativeSeedDelayFrames.beacon_frame setup codec owner (.inl plaintext))
        | inr raw =>
            exact RegistrationNativeSeedDelayCore.normalize_commutes _
              (RegistrationNativeSeedDelayFrames.beacon_frame setup codec owner (.inr raw))

/-- Entire adaptive World programs commute with completing any canonical seed, including later hidden installations and all records. -/
theorem program_commutes {Value : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) :
    Commutes lens (simulateQ (handler setup codec route) work) :=
  LazyOracleDiscard.commutes_simulateQ lens _ (handler_commutes setup codec route) work

end BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.charge_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.charge_commutes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.capability_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.capability_commutes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.effect_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.effect_shape
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.effects_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.effects_commutes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.handler_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.handler_commutes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.program_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld.program_commutes
