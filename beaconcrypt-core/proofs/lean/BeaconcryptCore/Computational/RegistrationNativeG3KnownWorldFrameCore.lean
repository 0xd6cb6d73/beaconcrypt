-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall
import BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames

/-! Actual World operations outside hidden-reference installation ignore private seed and role-use bookkeeping. This equation retains all concrete records, populated associated data, raw counters, CTX state and produced frames. Known installations keep their actual lifecycle tests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects CapabilitySpec)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeHiddenWorldInstall (view)
open RegistrationNativeSeedDelayFrames (ReadsSeed)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

def Allowed : (WorldSpec n).Domain → Prop
  | .inr (.inl (.inr query)) => ¬ReadsSeed query
  | _ => True

theorem view_idempotent (before : State n) : view (view before) = view before := rfl

theorem capability_input (query : (CapabilitySpec n).Domain) (quiet : ¬ReadsSeed query) (before : State n) :
    Prod.map id view <$> (PqxdhRecordLiftWorld.capability query).run before =
      Prod.map id view <$> (PqxdhRecordLiftWorld.capability query).run (view before) := by
  cases query with
  | peerPresent keyId | ownerPresent owner | appendOwner identity keyId phase =>
      simp only [PqxdhRecordLiftWorld.capability, StateT.run, view, map_pure, Prod.map_def, id_eq]
  | advanceOwner owner phase =>
      cases found : before.owners[owner]? with
      | none => simp only [PqxdhRecordLiftWorld.capability, StateT.run, view, found, map_pure, Prod.map_def, id_eq]
      | some current =>
          cases current <;>
            simp only [PqxdhRecordLiftWorld.capability, StateT.run, view, found, map_pure, Prod.map_def, id_eq]
          all_goals split <;> simp only [map_pure]
  | installServer keyId binding ref =>
      cases ref with
      | hidden slot => exact False.elim (quiet trivial)
      | known kernel =>
          cases found : before.server with
          | none => simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installServer, StateT.run,
              view, found, map_pure, Prod.map_def, id_eq]
          | some server =>
              simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installServer, StateT.run, view, found,
                PqxdhRecordLiftWorld.Unused, and_true]
              split <;> simp only [PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.markUsed,
                state_pure_apply, pure_bind, map_pure, Prod.map_def, id_eq, view, found]
  | installBeacon owner shell ref =>
      cases ref with
      | hidden slot => exact False.elim (quiet trivial)
      | known kernel =>
          simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installBeacon, StateT.run, view,
            PqxdhRecordLiftWorld.Unused, and_true, PqxdhRecordLiftWorld.BeaconReady]
          split <;> simp only [PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.markUsed,
            state_pure_apply, pure_bind, map_pure, Prod.map_def, id_eq, view]
  | hash bytes =>
      simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.sampled, StateT.run, view,
        bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]

theorem effects_input (query : (EnvEffects n).Domain)
    (quiet : match query with | .inr request => ¬ReadsSeed request | _ => True) (before : State n) :
    Prod.map id view <$> (PqxdhRecordLiftWorld.effects query).run before =
      Prod.map id view <$> (PqxdhRecordLiftWorld.effects query).run (view before) := by
  cases query with
  | inl coin =>
      simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.sampled, StateT.run, view,
        bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, PqxdhRecordLiftWorld.chargeEffect]
  | inr request => exact capability_input request quiet (PqxdhRecordLiftWorld.chargeEffect (.inr request) before)

theorem handler_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (quiet : Allowed query) (before : State n) :
    Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run before =
      Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run (view before) := by
  cases query with
  | inl created =>
      cases found : before.server <;> simp only [PqxdhRecordLiftWorld.handler,
        PqxdhRecordLiftWorld.initializeServer, StateT.run, view, found, map_pure, Prod.map_def, id_eq]
  | inr query => cases query with
    | inl effect => cases effect with
      | inl coin => exact effects_input (.inl coin) trivial before
      | inr request => exact effects_input (.inr request) quiet before
    | inr record => cases record with
      | inl server =>
          cases server <;> cases found : before.server <;> simp only [PqxdhRecordLiftWorld.handler,
            PqxdhRecordLiftWorld.serverStep, StateT.run, view, found, map_pure, bind_pure_comp,
            Functor.map_map, Prod.map_def, id_eq, PqxdhRecordLiftWorld.produce]
      | inr beacon =>
          rcases beacon with ⟨owner, query⟩
          cases query <;> cases found : before.owners[owner]? <;>
            simp only [PqxdhRecordLiftWorld.handler, PqxdhRecordLiftWorld.beaconStep, StateT.run,
              view, found, map_pure, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq,
              PqxdhRecordLiftWorld.produce]

end BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore.view_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore.capability_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore.capability_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore.effects_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore.effects_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore.handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore.handler_input
