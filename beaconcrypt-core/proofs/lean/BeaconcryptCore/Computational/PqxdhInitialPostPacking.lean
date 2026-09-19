import BeaconcryptCore.Computational.PqxdhInitialPendingPost

/-!
The complete post state is split into source frontend fields and the single shared/private ambient state. Packing is a reversible field rearrangement: it retains every role, control, consumed binding, shared primitive and private identity field. Each original record, selector and finish operation has the same full distribution after this rearrangement, including the unchanged source installation tick.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPostPacking
open PqxdhInitialPendingPost
variable {ι Chain M P I D K A N Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

abbrev Ambient (A N : Type) := RawCtxSharedPrimitive.SharedState A × N
abbrev Full (Chain M P I D K A N : Type) (S B : Nat) := Front Chain M P I D K S B × Ambient A N

def pack (state : Full Chain M P I D K A N S B) :
    PqxdhInitialGenericPost.State (KernelOf Chain) M P I D K A N S B :=
  (⟨state.1.roles, state.1.controls, state.1.consumed, state.2.1⟩, state.2.2)

def unpack (state : PqxdhInitialGenericPost.State (KernelOf Chain) M P I D K A N S B) :
    Full Chain M P I D K A N S B :=
  (⟨state.1.roles, state.1.controls, state.1.consumed⟩, (state.1.primitive, state.2))

/-- Every complete original field survives splitting and repacking. -/
theorem pack_unpack (state : PqxdhInitialGenericPost.State (KernelOf Chain) M P I D K A N S B) :
    pack (unpack state) = state := by cases state; rfl

/-- Every frontend and ambient field survives packing and splitting. -/
theorem unpack_pack (state : Full Chain M P I D K A N S B) : unpack (pack state) = state := by cases state; rfl

noncomputable def record
    (live : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (RawCtxGenericFamilyLive.State (KernelOf Chain) M P I D K S B)
        (StateT (RawCtxSharedPrimitive.SharedState A) m))) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhInitialGenericProtocol.State (KernelOf Chain) M P I D K A S B) m) :=
  fun query before => do
    let result ← ((live query).run before.roles).run before.primitive
    pure (result.1.1, {before with roles := result.1.2, primitive := result.2})

noncomputable def separated
    (live : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (RawCtxGenericFamilyLive.State (KernelOf Chain) M P I D K S B)
        (StateT (RawCtxSharedPrimitive.SharedState A) m)))
    (selector : QueryImpl extra (StateT N m))
    (owner : Pqxdh.Bytes → RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K →
      StateT (Ambient A N) m (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K)) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B) (StateT (Full Chain M P I D K A N S B) m)
  | .inl (.inl query) => fun before => do
      let result ← ((live query).run before.1.roles).run before.2.1
      pure (result.1.1, ({before.1 with roles := result.1.2}, (result.2, before.2.2)))
  | .inl (.inr query) => fun before => do
      let result ← (selector query).run before.2.2
      pure (result.1, (before.1, (before.2.1, result.2)))
  | .inr (.finish index raw) => fun before => do
      let result ← (owner raw (before.1.roles.1.2 index)).run before.2
      pure (result.1.1, (install index before.1 result.1.2, result.2))

/-- The actual original per-query state assembly agrees exactly with the single ambient interpreter, including finish installation and history tick. -/
theorem step
    (live : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (RawCtxGenericFamilyLive.State (KernelOf Chain) M P I D K S B)
        (StateT (RawCtxSharedPrimitive.SharedState A) m)))
    (selector : QueryImpl extra (StateT N m))
    (owner : Pqxdh.Bytes → RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K →
      StateT (Ambient A N) m (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K))
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain) (before : Full Chain M P I D K A N S B) :
    (PqxdhInitialGenericPost.post (record live) selector owner query).run (pack before) =
      Prod.map id pack <$> (separated live selector owner query).run before := by
  rcases query with (query | query) | query
  all_goals simp only [PqxdhInitialGenericPost.post, record, separated, pack, StateT.run, bind_pure_comp, Functor.map_map]
  all_goals rfl

/-- The full original adaptive post continuation preserves its complete final state after packing, with no callback or marginal-distribution premise. -/
theorem schedule
    (live : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (RawCtxGenericFamilyLive.State (KernelOf Chain) M P I D K S B)
        (StateT (RawCtxSharedPrimitive.SharedState A) m)))
    (selector : QueryImpl extra (StateT N m))
    (owner : Pqxdh.Bytes → RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K →
      StateT (Ambient A N) m (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K))
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Full Chain M P I D K A N S B) :
    (simulateQ (PqxdhInitialGenericPost.post (record live) selector owner) client).run (pack before) =
      Prod.map id pack <$> (simulateQ (separated live selector owner) client).run before := by
  exact (map_run_simulateQ_eq_of_query_map_eq (separated live selector owner)
    (PqxdhInitialGenericPost.post (record live) selector owner) pack
    (fun query state => (step live selector owner query state).symm) client before).symm

end BeaconcryptCore.Computational.PqxdhInitialPostPacking

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostPacking.pack_unpack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostPacking.pack_unpack

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostPacking.unpack_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostPacking.unpack_pack

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostPacking.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostPacking.step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostPacking.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostPacking.schedule
