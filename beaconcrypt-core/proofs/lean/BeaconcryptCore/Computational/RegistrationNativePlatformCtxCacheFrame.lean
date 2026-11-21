-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorld
/-! Native non-hash World work cannot inspect or change CTX cache addresses. The equations retain every primitive draw and the complete reached World, including refusal paths and sampled seed installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame
open PqxdhRecordLiftWorld
open PqxdhRecordLiftInterface
variable {n : Nat} {A : Type}
abbrev Cache := CtxRomAuth.CtxRO.QueryCache

def replace (cache : Cache) (before : State n) : State n :=
  {before with primitive := (before.primitive.1, cache)}

theorem sampled (cache : Cache) (work : ProbComp A) (before : State n) :
    Prod.map id (replace cache) <$> (PqxdhRecordLiftWorld.sampled work).run before =
      (PqxdhRecordLiftWorld.sampled work).run (replace cache before) := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map, replace]
  rfl

theorem resolve (cache : Cache) (role : Role) (ref : KernelRef n) (before : State n) :
    Prod.map id (replace cache) <$> (PqxdhRecordLiftWorld.resolve role ref).run before =
      (PqxdhRecordLiftWorld.resolve role ref).run (replace cache before) := by
  cases ref with
  | known kernel => simp only [PqxdhRecordLiftWorld.resolve, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | hidden slot =>
    simp only [PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.sampled, StateT.run,
      bind_pure_comp, Functor.map_map, replace]
    rfl

theorem installServer (cache : Cache) (keyId : Std.U64) (identity : PeerBinding)
    (ref : KernelRef n) (before : State n) :
    Prod.map id (replace cache) <$> (PqxdhRecordLiftWorld.installServer keyId identity ref).run before =
      (PqxdhRecordLiftWorld.installServer keyId identity ref).run (replace cache before) := by
  unfold PqxdhRecordLiftWorld.installServer
  simp only [StateT.run, replace]
  cases reached : before.server with
  | none => simp only [map_pure, Prod.map_def, id_eq, replace, reached]
  | some server =>
    simp only [← reached, Unused]
    split_ifs with permitted
    · simp only [map_bind]
      have restored := resolve cache .server ref before
      simp only [StateT.run, replace] at restored
      rw [← restored, bind_map_left]
      apply bind_congr
      intro resolved
      simp only [map_pure, Prod.map_def, id_eq, replace, markUsed]
      cases ref <;> rfl
    · simp only [map_pure, Prod.map_def, id_eq, replace]

theorem installBeacon (cache : Cache) (owner : Nat) (shell : BeaconShell)
    (ref : KernelRef n) (before : State n) :
    Prod.map id (replace cache) <$> (PqxdhRecordLiftWorld.installBeacon owner shell ref).run before =
      (PqxdhRecordLiftWorld.installBeacon owner shell ref).run (replace cache before) := by
  unfold PqxdhRecordLiftWorld.installBeacon
  simp only [StateT.run, replace, BeaconReady, Unused]
  split_ifs with permitted
  · simp only [map_bind]
    have restored := resolve cache .beacon ref before
    simp only [StateT.run, replace] at restored
    rw [← restored, bind_map_left]
    apply bind_congr
    intro resolved
    simp only [map_pure, Prod.map_def, id_eq, replace, markUsed]
    cases ref <;> rfl
  · simp only [map_pure, Prod.map_def, id_eq, replace]

def NonHash : (CapabilitySpec n).Domain → Prop
  | .hash _ => False
  | _ => True

theorem capability (cache : Cache) (query : (CapabilitySpec n).Domain) (allowed : NonHash query)
    (before : State n) :
    Prod.map id (replace cache) <$> (PqxdhRecordLiftWorld.capability query).run before =
      (PqxdhRecordLiftWorld.capability query).run (replace cache before) := by
  cases query with
  | peerPresent keyId | ownerPresent owner | appendOwner publicKey identity phase =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run, map_pure, Prod.map_def, id_eq, replace]
  | advanceOwner owner phase =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run, replace]
    cases found : before.owners[owner]? with
    | none => simp only [map_pure, Prod.map_def, id_eq, replace]
    | some prior =>
      cases prior with
      | inactive previous =>
        dsimp only
        split_ifs <;> simp only [map_pure, Prod.map_def, id_eq, replace]
      | established shell kernel => simp only [map_pure, Prod.map_def, id_eq, replace]
  | installServer keyId identity ref => exact installServer cache keyId identity ref before
  | installBeacon owner shell ref => exact installBeacon cache owner shell ref before
  | hash bytes => exact False.elim allowed

def NonHashEffect : (EnvEffects n).Domain → Prop
  | .inl _ => True
  | .inr query => NonHash query

theorem effects (cache : Cache) (query : (EnvEffects n).Domain) (allowed : NonHashEffect query)
    (before : State n) :
    Prod.map id (replace cache) <$> (PqxdhRecordLiftWorld.effects query).run before =
      (PqxdhRecordLiftWorld.effects query).run (replace cache before) := by
  cases query with
  | inl coin =>
    simpa only [PqxdhRecordLiftWorld.effects, StateT.run, chargeEffect, replace] using
      sampled cache (unifSpec.query coin : ProbComp _) (chargeEffect (.inl coin) before)
  | inr request =>
    simpa only [PqxdhRecordLiftWorld.effects, StateT.run, chargeEffect, replace] using
      capability cache request allowed (chargeEffect (.inr request) before)
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.sampled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.sampled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.resolve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.resolve

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.installServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.installServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.installBeacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.installBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.capability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame.effects
