import BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity
import BeaconcryptCore.Computational.PqxdhPhase2OldSource
import BeaconcryptCore.Computational.PqxdhPhase2LiveFinish

/-!
The actual selected Beacon finish commutes with reassociation of the complete shared primitive state and an additional private state. The same native owner program, optional API reply, installation and single live-history tick are retained, together with all other owners, controls and consumed registration records.

This is an arbitrary-lawful-monad operational equation. It assumes no successful finish, state validity, primitive correctness or state-preservation law; it proves no cryptographic hop or symbolic observation equivalence. Storage, snapshots, persistence and restoration are excluded.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2FinishIdentity
open PqxdhPhase2SharedIdentity PqxdhPhase2OldSource PqxdhPhase2LiveFinish
variable {M P I D K X Response A J : Type} {S B : Nat}

/-- The actual selected native finish and installation preserve all fields and the same complete private state under reassociation. -/
theorem finish_reassociate {m : Type → Type} [Monad m] [LawfulMonad m]
    (native : QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response))
      (StateT (Shared (A := A)) (StateT J m)))
    (decode : RawCtxReceive.FrameDecoder) (query : (FinishSpec B).Domain)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) (identities : J) :
    (fun result => (result.1, packState result.2.1 result.2.2)) <$>
      (((finishImpl native decode).flattenStateT query).run (state, identities)) =
      ((finishImpl (packed native.flattenStateT) decode query).run (packState state identities)) := by
  cases query with
  | finish index raw =>
      change @Eq (m (Option PqxdhBeaconPhase2Preparation.Bytes ×
        PqxdhRegistrationProtocolState.State M P I D K (A × J) S B)) _ _
      have complete := packed_run native.flattenStateT
        (PqxdhBeaconPhase2Publication.nativeOwner decode raw (state.roles.1.2 index))
        (state.primitive, identities)
      rw [simulateQ_flattenStateT_run] at complete
      have projected := congrArg (fun work =>
        (fun result : (Option PqxdhBeaconPhase2Preparation.Bytes × RawCtxBeaconLifecycle.State I D K) ×
          Shared (A := A × J) =>
          (result.1.1, install index (packState state identities) result.1.2 result.2)) <$> work) complete
      convert projected using 1
      · simp only [QueryImpl.flattenStateT, finishImpl, StateT.run_mk,
          bind_pure_comp, StateT.run_map, Functor.map_map, packState, install, pack]
        rfl
      · simp only [finishImpl, StateT.run_mk, bind_pure_comp, packState]
        rfl

end BeaconcryptCore.Computational.PqxdhPhase2FinishIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2FinishIdentity.finish_reassociate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2FinishIdentity.finish_reassociate
