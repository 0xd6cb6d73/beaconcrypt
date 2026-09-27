import BeaconcryptCore.Computational.PqxdhInitialGenericRecords
import BeaconcryptCore.Computational.PqxdhInitialGenericBeacon

/-!
The original post-registration schedule retains the complete role family, registration fields, shared primitive state and private identity interpreter. Record, selector and attempted Beacon finish requests preserve their original order and optional replies. Only the installed kernel representation changes; the native source and concrete private interpreters discharge the displayed operational equations.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialGenericPost
open PqxdhInitialGenericProtocol
variable {ι Kernel M P I D K A N Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

abbrev Spec (extra : OracleSpec ι) (S B : Nat) :=
  (RawCtxProtocolReveals.SourceSpec S B + extra) + PqxdhPhase2LiveFinish.FinishSpec B
abbrev State (Kernel M P I D K A N : Type) (S B : Nat) :=
  PqxdhInitialGenericProtocol.State Kernel M P I D K A S B × N
abbrev NativeState (M P I D K A N : Type) (S B : Nat) :=
  PqxdhRegistrationProtocolState.State M P I D K A S B × N

def native (interpret : Kernel → ConcreteRatchetKernel) (state : State Kernel M P I D K A N S B) : NativeState M P I D K A N S B :=
  (PqxdhInitialGenericProtocol.native interpret state.1, state.2)

def installed (index : Fin B) (before : State Kernel M P I D K A N S B)
    (result : (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState Kernel I D K) ×
      (RawCtxSharedPrimitive.SharedState A × N)) :
    Option Pqxdh.Bytes × State Kernel M P I D K A N S B :=
  (result.1.1, (finishInstall index before.1 result.1.2 result.2.1, result.2.2))

def nativeInstalled (index : Fin B) (before : NativeState M P I D K A N S B)
    (result : (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D K) ×
      (RawCtxSharedPrimitive.SharedState A × N)) :
    Option Pqxdh.Bytes × NativeState M P I D K A N S B :=
  (result.1.1, (PqxdhPhase2LiveFinish.install index before.1 result.1.2 result.2.1, result.2.2))

/-- The whole private identity interpreter and shared primitive poststate accompany the exact original installed Beacon. -/
theorem installed_native (interpret : Kernel → ConcreteRatchetKernel) (index : Fin B)
    (before : State Kernel M P I D K A N S B)
    (result : (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState Kernel I D K) ×
      (RawCtxSharedPrimitive.SharedState A × N)) :
    Prod.map id (native interpret) (installed index before result) =
      nativeInstalled index (native interpret before)
        (Prod.map (Prod.map id (RawCtxGenericRoleStorage.nativeBeacon interpret)) id result) := by
  simp only [installed, nativeInstalled, native, Prod.map_apply, id_eq, finish_native]
  rfl

noncomputable def post
    (records : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhInitialGenericProtocol.State Kernel M P I D K A S B) m))
    (selector : QueryImpl extra (StateT N m))
    (owner : Pqxdh.Bytes → RawCtxGenericRoleStorage.BeaconState Kernel I D K →
      StateT (RawCtxSharedPrimitive.SharedState A × N) m
        (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState Kernel I D K)) :
    QueryImpl (Spec extra S B) (StateT (State Kernel M P I D K A N S B) m)
  | .inl (.inl query) => fun before =>
      (fun result => (result.1, (result.2, before.2))) <$> (records query).run before.1
  | .inl (.inr query) => fun before =>
      (fun result => (result.1, (before.1, result.2))) <$> (selector query).run before.2
  | .inr (.finish index raw) => fun before =>
      installed index before <$> (owner raw (before.1.roles.1.2 index)).run (before.1.primitive, before.2)

noncomputable def nativePost
    (records : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) m))
    (selector : QueryImpl extra (StateT N m))
    (owner : Pqxdh.Bytes → RawCtxBeaconLifecycle.State I D K →
      StateT (RawCtxSharedPrimitive.SharedState A × N) m
        (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D K)) :
    QueryImpl (Spec extra S B) (StateT (NativeState M P I D K A N S B) m)
  | .inl (.inl query) => fun before =>
      (fun result => (result.1, (result.2, before.2))) <$> (records query).run before.1
  | .inl (.inr query) => fun before =>
      (fun result => (result.1, (before.1, result.2))) <$> (selector query).run before.2
  | .inr (.finish index raw) => fun before =>
      nativeInstalled index before <$> (owner raw (before.1.roles.1.2 index)).run (before.1.primitive, before.2)

set_option backward.isDefEq.respectTransparency false in
/-- Each original record, selector and finish request retains its whole public reply and all private poststate under the displayed operational maps. -/
theorem step_native (interpret : Kernel → ConcreteRatchetKernel)
    (records : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhInitialGenericProtocol.State Kernel M P I D K A S B) m))
    (nativeRecords : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) m))
    (recordMap : ∀ query before, (nativeRecords query).run (PqxdhInitialGenericProtocol.native interpret before) =
      Prod.map id (PqxdhInitialGenericProtocol.native interpret) <$> (records query).run before)
    (selector : QueryImpl extra (StateT N m))
    (owner : Pqxdh.Bytes → RawCtxGenericRoleStorage.BeaconState Kernel I D K →
      StateT (RawCtxSharedPrimitive.SharedState A × N) m
        (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState Kernel I D K))
    (nativeOwner : Pqxdh.Bytes → RawCtxBeaconLifecycle.State I D K →
      StateT (RawCtxSharedPrimitive.SharedState A × N) m
        (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D K))
    (ownerMap : ∀ raw before, nativeOwner raw (RawCtxGenericRoleStorage.nativeBeacon interpret before) =
      Prod.map id (RawCtxGenericRoleStorage.nativeBeacon interpret) <$> owner raw before)
    (query : (Spec extra S B).Domain) (before : State Kernel M P I D K A N S B) :
    (nativePost nativeRecords selector nativeOwner query).run (native interpret before) =
      Prod.map id (native interpret) <$> (post records selector owner query).run before := by
  simp only [StateT.run] at recordMap
  rcases query with (query | query) | query
  case inl.inl =>
    simp only [nativePost, post, native, StateT.run, recordMap, Functor.map_map]
    rfl
  case inl.inr =>
    simp only [nativePost, post, native, StateT.run, Functor.map_map]
    rfl
  case inr =>
    cases query with
    | finish index raw =>
      simp only [nativePost, post, native, PqxdhInitialGenericProtocol.native,
        RawCtxGenericFamilyLive.nativeState, RawCtxGenericRoleFamily.nativeRoles, StateT.run]
      rw [ownerMap]
      simp only [Functor.map, StateT.map, bind_pure_comp, Functor.map_map]
      apply congrArg (fun f => f <$> _)
      funext result
      exact (installed_native interpret index before result).symm

/-- The same original adaptive scheduler sees identical replies in source order while every private state component is retained. -/
theorem schedule_native (interpret : Kernel → ConcreteRatchetKernel)
    (records : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhInitialGenericProtocol.State Kernel M P I D K A S B) m))
    (nativeRecords : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) m))
    (recordMap : ∀ query before, (nativeRecords query).run (PqxdhInitialGenericProtocol.native interpret before) =
      Prod.map id (PqxdhInitialGenericProtocol.native interpret) <$> (records query).run before)
    (selector : QueryImpl extra (StateT N m))
    (owner : Pqxdh.Bytes → RawCtxGenericRoleStorage.BeaconState Kernel I D K →
      StateT (RawCtxSharedPrimitive.SharedState A × N) m
        (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState Kernel I D K))
    (nativeOwner : Pqxdh.Bytes → RawCtxBeaconLifecycle.State I D K →
      StateT (RawCtxSharedPrimitive.SharedState A × N) m
        (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D K))
    (ownerMap : ∀ raw before, nativeOwner raw (RawCtxGenericRoleStorage.nativeBeacon interpret before) =
      Prod.map id (RawCtxGenericRoleStorage.nativeBeacon interpret) <$> owner raw before)
    (client : OracleComp (Spec extra S B) Result) (before : State Kernel M P I D K A N S B) :
    (simulateQ (nativePost nativeRecords selector nativeOwner) client).run (native interpret before) =
      Prod.map id (native interpret) <$> (simulateQ (post records selector owner) client).run before := by
  exact (map_run_simulateQ_eq_of_query_map_eq (post records selector owner)
    (nativePost nativeRecords selector nativeOwner) (native interpret)
    (fun query state => (step_native interpret records nativeRecords recordMap selector owner nativeOwner ownerMap query state).symm)
    client before).symm

end BeaconcryptCore.Computational.PqxdhInitialGenericPost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericPost.installed_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericPost.installed_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericPost.step_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericPost.step_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericPost.schedule_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericPost.schedule_native
