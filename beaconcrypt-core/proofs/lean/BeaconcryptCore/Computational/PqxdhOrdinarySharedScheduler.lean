import BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom
import BeaconcryptCore.Computational.RawCtxSourceSharedRom

/-!
The complete ordinary prechallenge scheduler executes native record, public, reveal, identity and Phase2-finish requests through one ROM. Its local state contains the actual role/control/history and joint identity state but no independently writable CTX cache. The interpreter alone has the selected KEM secret; no eventual selected message key is an argument.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler
open PqxdhPhase2SourceAux PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhKemIndCca PqxdhJointKdfGame PqxdhPrivateKemSource PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhGeneratedBeaconState
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

structure Local (M P I D K A : Type) (S B count : Nat) where
  roles : PqxdhRegistrationProtocolState.Roles M P (IdentityHandle I) D (KemHandle K) S B
  controls : Fin S → pqxdh.ServerState
  consumed : Fin S → List Pqxdh.Bytes
  auxiliary : A × BareState count

def attach {count : Nat} (state : Local M P I D K A S B count) (cache : CtxRO.QueryCache) :
    PqxdhPhase2SourceScheduler.State M P I D K (A × BareState count) S B :=
  ⟨state.roles, state.controls, state.consumed, (state.auxiliary, cache)⟩

def separate {count : Nat} (state : PqxdhPhase2SourceScheduler.State M P I D K (A × BareState count) S B) :
    Local M P I D K A S B count :=
  ⟨state.roles, state.controls, state.consumed, state.primitive.1⟩

variable (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)

noncomputable def record (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) :
    StateT (Local M P I D K A S B count) (OracleComp HashSpec) ((RawCtxProtocolReveals.SourceSpec S B).Range query) := StateT.mk fun state =>
  (fun result => (result.1, {state with roles := result.2})) <$>
    simulateQ (RawCtxSourceSharedRom.backend source writer)
      ((RawCtxProtocolReveals.protocolImpl S B sender route decode query).run state.roles)

noncomputable def selector (query : (SelectorSpec baseSpec).Domain) :
    StateT (Local M P I D K A S B count) (OracleComp HashSpec) ((SelectorSpec baseSpec).Range query) := StateT.mk fun state =>
  (fun result => (result.1, {state with auxiliary := (state.auxiliary.1, result.2)})) <$>
    simulateQ RawCtxSelectiveSharedRom.coins
      (evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives count query).run state.auxiliary.2))

noncomputable def finish (query : (PqxdhPhase2LiveFinish.FinishSpec B).Domain) :
    StateT (Local M P I D K A S B count) (OracleComp HashSpec) (Option Pqxdh.Bytes) := StateT.mk fun state =>
  match query with
  | .finish index raw => do
    let result ← (simulateQ (PqxdhOrdinaryNativeSharedRom.compiler attachedVerify primitives count source localImpl baseImpl kem secret)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw (state.roles.1.2 index))).run state.auxiliary
    pure (result.1.1, {state with
      roles := ((state.roles.1.1, Function.update state.roles.1.2 index result.1.2), RawCtxProtocolReveals.tick state.roles.2)
      auxiliary := result.2})

noncomputable def compiler : QueryImpl (PqxdhPhase2SourceScheduler.Spec baseSpec S B)
    (StateT (Local M P I D K A S B count) (OracleComp HashSpec))
  | .inl (.inl query) => record count source writer sender route decode query
  | .inl (.inr query) => selector attachedVerify primitives count baseImpl kem secret query
  | .inr query => finish attachedVerify primitives count source decode localImpl baseImpl kem secret query

/-- The local representation retains every original source field, with only the common cache threaded externally. -/
theorem attach_separate (state : PqxdhPhase2SourceScheduler.State M P I D K (A × BareState count) S B) :
    attach (separate state) state.primitive.2 = state := by
  cases state
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original reached Beacon finish executes its entire native callback program and installs the same optional result, role and common cache. -/
theorem finish_source (query : (PqxdhPhase2LiveFinish.FinishSpec B).Domain)
    (state : Local M P I D K A S B count) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((finish attachedVerify primitives count source decode localImpl baseImpl kem secret query).run state)).run cache =
      simulateQ (PqxdhPhase2NativeSource.interpretation baseImpl kem secret)
        ((PqxdhPhase2LiveFinish.finishImpl
          (PqxdhPhase2SourceScheduler.ordinaryNative attachedVerify primitives count source localImpl) decode query).run
            (attach state cache)) := by
  cases query with
  | finish index raw =>
    simp only [PqxdhOrdinarySharedScheduler.finish, PqxdhPhase2LiveFinish.finishImpl, StateT.run_mk, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
    rw [← PqxdhOrdinaryNativeSharedRom.original]
    simp only [Functor.map_map, attach, PqxdhPhase2LiveFinish.install]

set_option backward.isDefEq.respectTransparency false in
/-- Original record/public/reveal callbacks execute through the same ROM while retaining the complete role history, registration controls and identity state. -/
theorem record_source (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (state : Local M P I D K A S B count) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((record count source writer sender route decode query).run state)).run cache =
      (PqxdhRegistrationProtocolState.sourceImpl source writer sender route decode query).run (attach state cache) := by
  have forwarded := RawCtxSourceSharedRom.backend_program source writer
    ((RawCtxProtocolReveals.protocolImpl S B sender route decode query).run state.roles) state.auxiliary cache
  have native := RawCtxProtocolReveals.schedule_interpretation source writer S B sender route decode
    ((RawCtxProtocolReveals.SourceSpec S B).query query : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _)
    state.roles (state.auxiliary, cache)
  simp only [simulateQ_spec_query] at native
  have linked := congrArg (fun work => (fun result => (result.1.1,
    PqxdhRegistrationProtocolState.restore (attach state cache) (result.1.2, result.2))) <$> work) (forwarded.symm.trans native)
  simp only [record, StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map,
    PqxdhRegistrationProtocolState.restore, attach] at linked ⊢
  exact linked

set_option backward.isDefEq.respectTransparency false in
/-- The original identity, base and prechallenge decapsulation service preserves the reached ROM cache and all fields outside its actual identity state. -/
theorem selector_source (query : (SelectorSpec baseSpec).Domain)
    (state : Local M P I D K A S B count) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((selector attachedVerify primitives count baseImpl kem secret query).run state)).run cache =
      simulateQ (PqxdhPhase2NativeSource.interpretation baseImpl kem secret)
        ((PqxdhPhase2SourceScheduler.ordinary attachedVerify primitives count source writer sender route decode localImpl
          (.inl (.inr query))).run (attach state cache)) := by
  simp only [selector, StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [RawCtxSelectiveSharedRom.coins_complete]
  simp only [Functor.map_map, PqxdhPhase2SourceScheduler.ordinary, StateT.run_mk, bind_pure_comp, simulateQ_map,
    PqxdhPhase2SourceScheduler.identityState, attach]
  simp only [PqxdhPhase2NativeSource.interpretation, QueryImpl.simulateQ_compose, evalKem]

set_option backward.isDefEq.respectTransparency false in
/-- All source request classes preserve their original optional reply and full state under the same prechallenge interpretation. -/
theorem step (query : (PqxdhPhase2SourceScheduler.Spec baseSpec S B).Domain)
    (state : Local M P I D K A S B count) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((compiler attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret query).run state)).run cache =
      simulateQ (PqxdhPhase2NativeSource.interpretation baseImpl kem secret)
        ((PqxdhPhase2SourceScheduler.ordinary attachedVerify primitives count source writer sender route decode localImpl query).run
          (attach state cache)) := by
  rcases query with ((query | query) | query)
  · simp only [compiler, PqxdhPhase2SourceScheduler.ordinary, StateT.run_mk]
    rw [PqxdhPhase2NativeSource.interpretation, QueryImpl.simulateQ_compose]
    exact (record_source count source writer sender route decode query state cache).trans
      (evalKem_coins baseImpl kem secret _).symm
  · exact selector_source attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret query state cache
  · exact finish_source attachedVerify primitives count source decode localImpl baseImpl kem secret query state cache

/-- The common-ROM compiler executes the complete adaptive scheduler, retaining all source fields and all replies in their original order. -/
theorem program (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (state : Local M P I D K A S B count) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((simulateQ (compiler attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret) client).run state)).run cache =
      simulateQ (PqxdhPhase2NativeSource.interpretation baseImpl kem secret)
        ((simulateQ (PqxdhPhase2SourceScheduler.ordinary attachedVerify primitives count source writer sender route decode localImpl) client).run
          (attach state cache)) := by
  let compiled := compiler (P := P) (S := S) (B := B) attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret
  let original := PqxdhPhase2SourceScheduler.ordinary (baseSpec := baseSpec) (P := P) (S := S) (B := B) attachedVerify primitives count source writer sender route decode localImpl
  let interpreted := PqxdhPhase2NativeSource.interpretation baseImpl kem secret
  have perQuery : ∀ query before,
      Prod.map id (fun (pair : Local M P I D K A S B count × CtxRO.QueryCache) => attach pair.1 pair.2) <$>
        (((hashImpl.mapStateTBase compiled).flattenStateT query).run before) =
        ((interpreted.mapStateTBase original) query).run (attach before.1 before.2) := by
    intro query before
    simpa only [compiled, original, interpreted, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
      StateT.run, StateT.mk, Functor.map_map, Prod.map_def, id_eq] using
      step attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret query before.1 before.2
  have whole := map_run_simulateQ_eq_of_query_map_eq
    ((hashImpl.mapStateTBase compiled).flattenStateT) (interpreted.mapStateTBase original)
    (fun pair => attach pair.1 pair.2) perQuery client (state, cache)
  have unpacked := congrArg (fun work => (fun result => (result.1.1, attach result.1.2 result.2)) <$> work)
    (simulateQ_mapStateTBase_run_eq_map_flattenStateT hashImpl compiled client state cache)
  simp only [Functor.map_map, Prod.map_def, id_eq] at unpacked whole
  rw [← QueryImpl.simulateQ_mapStateTBase_run] at whole
  exact unpacked.trans whole

end BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler


/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.attach_separate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.attach_separate

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.record_source

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.selector_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.selector_source

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.step

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler.program
